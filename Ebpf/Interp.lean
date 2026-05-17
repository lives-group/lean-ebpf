import Ebpf.Semantics
import Ebpf.EbpfVerifier

namespace Ebpf

/- Fuel-based interpreter -/

abbrev CallOracle := BitVec 32 → RegFile → Memory → RegFile × Memory

def interp (prog : Program) (oracle : CallOracle) : State → ℕ → Option State
  | _s, 0 => none
  | s, fuel + 1 =>
    match prog[s.pc]? with
    | none               => none
    | some Instr.exit    => some s
    | some (Instr.alu64 op dst src) =>
        let v := evalAlu64 op (s.regs dst) (evalSrc s.regs src)
        interp prog oracle { s with regs := s.regs.set dst v, pc := s.pc + 1 } fuel
    | some (Instr.alu32 op dst src) =>
        let v := evalAlu32 op (s.regs dst) (evalSrc s.regs src)
        interp prog oracle { s with regs := s.regs.set dst v, pc := s.pc + 1 } fuel
    | some (Instr.neg64 dst) =>
        interp prog oracle
          { s with regs := s.regs.set dst (- s.regs dst), pc := s.pc + 1 } fuel
    | some (Instr.neg32 dst) =>
        interp prog oracle
          { s with regs := s.regs.set dst (zext32 (- s.regs dst)), pc := s.pc + 1 } fuel
    | some (Instr.endian e sz dst) =>
        let v := evalEndian e sz (s.regs dst)
        interp prog oracle { s with regs := s.regs.set dst v, pc := s.pc + 1 } fuel
    | some (Instr.ja off) =>
        let pc' : Int := (s.pc : Int) + 1 + offset16ToInt off
        if _ : 0 ≤ pc' then
          interp prog oracle { s with pc := pc'.toNat } fuel
        else none
    | some (Instr.jmp64 op dst src off) =>
        if evalJmp64 op (s.regs dst) (evalSrc s.regs src) then
          let pc' : Int := (s.pc : Int) + 1 + offset16ToInt off
          if _ : 0 ≤ pc' then
            interp prog oracle { s with pc := pc'.toNat } fuel
          else none
        else
          interp prog oracle { s with pc := s.pc + 1 } fuel
    | some (Instr.jmp32 op dst src off) =>
        if evalJmp32 op (s.regs dst) (evalSrc s.regs src) then
          let pc' : Int := (s.pc : Int) + 1 + offset16ToInt off
          if _ : 0 ≤ pc' then
            interp prog oracle { s with pc := pc'.toNat } fuel
          else none
        else
          interp prog oracle { s with pc := s.pc + 1 } fuel
    | some (Instr.store sz dst off src) =>
        let addr := s.regs dst + BitVec.signExtend 64 off
        let mem' := writeMem s.mem addr (evalSrc s.regs src) sz
        interp prog oracle { s with mem := mem', pc := s.pc + 1 } fuel
    | some (Instr.load sz dst src off) =>
        let addr := s.regs src + BitVec.signExtend 64 off
        let v    := readMem s.mem addr sz
        interp prog oracle { s with regs := s.regs.set dst v, pc := s.pc + 1 } fuel
    | some (Instr.lddw dst imm) =>
        interp prog oracle { s with regs := s.regs.set dst imm, pc := s.pc + 2 } fuel
    | some (Instr.atomic sz op fetch dst src off) =>
        let addr   := s.regs dst + BitVec.signExtend 64 off
        let oldVal := readMem s.mem addr sz
        let newVal := match op with
          | AtomicOp.add     => oldVal + s.regs src
          | AtomicOp.or      => oldVal ||| s.regs src
          | AtomicOp.and     => oldVal &&& s.regs src
          | AtomicOp.xor     => oldVal ^^^ s.regs src
          | AtomicOp.xchg    => s.regs src
          | AtomicOp.cmpxchg =>
              if s.regs Reg.r0 = oldVal then s.regs src else oldVal
        let mem'  := writeMem s.mem addr newVal sz
        let regs' := match op with
          | AtomicOp.cmpxchg => s.regs.set Reg.r0 oldVal
          | _                => if fetch then s.regs.set src oldVal else s.regs
        interp prog oracle { regs := regs', mem := mem', pc := s.pc + 1 } fuel
    | some (Instr.call fid) =>
        let (regs', mem') := oracle fid s.regs s.mem
        interp prog oracle { regs := regs', mem := mem', pc := s.pc + 1 } fuel

/- Coherence theorem -/

def OracleOk (oracle : CallOracle) : Prop :=
  ∀ (fid : BitVec 32) (regs : RegFile) (mem : Memory)
    (r : Reg), r ∈ ([Reg.r6, Reg.r7, Reg.r8, Reg.r9, Reg.r10] : List Reg) →
    (oracle fid regs mem).1 r = regs r

theorem interp_coherent
    (prog : Program)
    (oracle : CallOracle)
    (hok : OracleOk oracle)
    (fuel : ℕ)
    (s₀ sf : State)
    (h : interp prog oracle s₀ fuel = some sf) :
    (∃ _ : Steps prog s₀ sf, prog[sf.pc]? = some Instr.exit) := by
  induction fuel generalizing s₀ with
  | zero =>
    simp [interp] at h
  | succ n ih =>
    simp only [interp] at h
    match hpc : prog[s₀.pc]? with
    | none => simp [hpc] at h
    | some Instr.exit =>
        simp only [hpc] at h
        rw [show sf = s₀ from (Option.some.inj h).symm]
        exists Steps.refl s₀
    | some (Instr.alu64 op dst src) =>
        simp only [hpc] at h
        let s₁ := { s₀ with
                     regs := s₀.regs.set dst (evalAlu64 op (s₀.regs dst) (evalSrc s₀.regs src)),
                     pc := s₀.pc + 1 }
        have hstep : Step prog s₀ s₁ :=
          Step.alu64 s₀.regs s₀.mem s₀.pc op dst src _ hpc rfl
        cases ih s₁ h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ hstep hsteps
    | some (Instr.alu32 op dst src) =>
        simp only [hpc] at h
        let s₁ := { s₀ with
                     regs := s₀.regs.set dst (evalAlu32 op (s₀.regs dst) (evalSrc s₀.regs src)),
                     pc := s₀.pc + 1 }
        have hstep : Step prog s₀ s₁ :=
          Step.alu32 s₀.regs s₀.mem s₀.pc op dst src _ hpc rfl
        cases ih s₁ h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ hstep hsteps
    | some (Instr.neg64 dst) =>
        simp only [hpc] at h
        let s₁ := { s₀ with regs := s₀.regs.set dst (- s₀.regs dst), pc := s₀.pc + 1 }
        cases ih s₁ h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ (Step.neg64 s₀.regs s₀.mem s₀.pc dst hpc) hsteps
    | some (Instr.neg32 dst) =>
        simp only [hpc] at h
        let s₁ := { s₀ with regs := s₀.regs.set dst (zext32 (- s₀.regs dst)), pc := s₀.pc + 1 }
        cases ih s₁ h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ (Step.neg32 s₀.regs s₀.mem s₀.pc dst hpc) hsteps
    | some (Instr.endian e sz dst) =>
        simp only [hpc] at h
        let s₁ := { s₀ with regs := s₀.regs.set dst (evalEndian e sz (s₀.regs dst)),
                             pc := s₀.pc + 1 }
        have hstep : Step prog s₀ s₁ :=
          Step.endian s₀.regs s₀.mem s₀.pc e sz dst _ hpc rfl
        cases ih s₁ h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ hstep hsteps
    | some (Instr.ja off) =>
        simp only [hpc] at h
        split_ifs at h with hnn
        · let s₁ := { s₀ with pc := ((s₀.pc : Int) + 1 + offset16ToInt off).toNat }
          have hstep : Step prog s₀ s₁ :=
            Step.ja s₀.regs s₀.mem s₀.pc off _ hpc rfl hnn
          cases ih s₁ h with
          | intro hsteps hexit =>
            exists Steps.step _ _ _ hstep hsteps
    | some (Instr.jmp64 op dst src off) =>
        simp only [hpc] at h
        by_cases hcond : evalJmp64 op (s₀.regs dst) (evalSrc s₀.regs src) = true
        · simp only [hcond, ite_true] at h
          split_ifs at h with hnn
          · let s₁ := { s₀ with pc := ((s₀.pc : Int) + 1 + offset16ToInt off).toNat }
            have hstep : Step prog s₀ s₁ :=
              Step.jmp64_taken s₀.regs s₀.mem s₀.pc op dst src off _ hpc hcond rfl hnn
            cases ih s₁ h with
            | intro hsteps hexit =>
              exists Steps.step _ _ _ hstep hsteps
        · simp only [Bool.not_eq_true] at hcond
          simp only [hcond] at h
          let s₁ := { s₀ with pc := s₀.pc + 1 }
          have hstep : Step prog s₀ s₁ :=
            Step.jmp64_fallthrough s₀.regs s₀.mem s₀.pc op dst src off hpc hcond
          cases ih s₁ h with
          | intro hsteps hexit =>
            exists Steps.step _ _ _ hstep hsteps
    | some (Instr.jmp32 op dst src off) =>
        simp only [hpc] at h
        by_cases hcond : evalJmp32 op (s₀.regs dst) (evalSrc s₀.regs src) = true
        · simp only [hcond, ite_true] at h
          split_ifs at h with hnn
          · let s₁ := { s₀ with pc := ((s₀.pc : Int) + 1 + offset16ToInt off).toNat }
            have hstep : Step prog s₀ s₁ :=
              Step.jmp32_taken s₀.regs s₀.mem s₀.pc op dst src off _ hpc hcond rfl hnn
            cases ih s₁ h with
            | intro hsteps hexit =>
              exists Steps.step _ _ _ hstep hsteps
        · simp only [Bool.not_eq_true] at hcond
          simp only [hcond] at h
          let s₁ := { s₀ with pc := s₀.pc + 1 }
          have hstep : Step prog s₀ s₁ :=
            Step.jmp32_fallthrough s₀.regs s₀.mem s₀.pc op dst src off hpc hcond
          cases ih s₁ h with
          | intro hsteps hexit =>
            exists Steps.step _ _ _ hstep hsteps
    | some (Instr.store sz dst off src) =>
        simp only [hpc] at h
        let addr := s₀.regs dst + BitVec.signExtend 64 off
        let mem' := writeMem s₀.mem addr (evalSrc s₀.regs src) sz
        let s₁ := { s₀ with mem := mem', pc := s₀.pc + 1 }
        have hstep : Step prog s₀ s₁ :=
          Step.store s₀.regs s₀.mem s₀.pc sz dst off src addr mem' hpc rfl rfl
        cases ih s₁ h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ hstep hsteps
    | some (Instr.load sz dst src off) =>
        simp only [hpc] at h
        let addr := s₀.regs src + BitVec.signExtend 64 off
        let v    := readMem s₀.mem addr sz
        let s₁ := { s₀ with regs := s₀.regs.set dst v, pc := s₀.pc + 1 }
        have hstep : Step prog s₀ s₁ :=
          Step.load s₀.regs s₀.mem s₀.pc sz dst src off addr v hpc rfl rfl
        cases ih s₁ h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ hstep hsteps
    | some (Instr.lddw dst imm) =>
        simp only [hpc] at h
        let s₁ := { s₀ with regs := s₀.regs.set dst imm, pc := s₀.pc + 2 }
        have hstep : Step prog s₀ s₁ :=
          Step.lddw s₀.regs s₀.mem s₀.pc dst imm hpc
        cases ih s₁ h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ hstep hsteps
    | some (Instr.atomic sz op fetch dst src off) =>
        simp only [hpc] at h
        let addr   := s₀.regs dst + BitVec.signExtend 64 off
        let oldVal := readMem s₀.mem addr sz
        let newVal := match op with
          | AtomicOp.add     => oldVal + s₀.regs src
          | AtomicOp.or      => oldVal ||| s₀.regs src
          | AtomicOp.and     => oldVal &&& s₀.regs src
          | AtomicOp.xor     => oldVal ^^^ s₀.regs src
          | AtomicOp.xchg    => s₀.regs src
          | AtomicOp.cmpxchg =>
              if s₀.regs Reg.r0 = oldVal then s₀.regs src else oldVal
        let mem'  := writeMem s₀.mem addr newVal sz
        let regs' := match op with
          | AtomicOp.cmpxchg => s₀.regs.set Reg.r0 oldVal
          | _                => if fetch then s₀.regs.set src oldVal else s₀.regs
        let s₁ := ({ regs := regs', mem := mem', pc := s₀.pc + 1 } : State)
        have hstep : Step prog s₀ s₁ :=
          Step.atomic_op s₀.regs s₀.mem s₀.pc sz op fetch dst src off
            addr oldVal newVal mem' regs' hpc rfl rfl rfl rfl rfl
        cases ih s₁ h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ hstep hsteps
    | some (Instr.call fid) =>
        simp only [hpc] at h
        set regs' := (oracle fid s₀.regs s₀.mem).1 with hregs'_def
        set mem'  := (oracle fid s₀.regs s₀.mem).2 with hmem'_def
        let s₁ := ({ regs := regs', mem := mem', pc := s₀.pc + 1 } : State)
        have hcallee : ∀ r, r ∈ ([Reg.r6, Reg.r7, Reg.r8, Reg.r9, Reg.r10] : List Reg) →
            regs' r = s₀.regs r :=
          fun r hr => hok fid s₀.regs s₀.mem r hr
        let fp : BitVec 64 → Option (BitVec 8) :=
          fun a => if mem' a = s₀.mem a then none else some (mem' a)
        have hfp : ∀ a, fp a = none → mem' a = s₀.mem a := by
          intro a ha
          simp only [fp] at ha
          by_cases heq : mem' a = s₀.mem a
          · exact heq
          · simp only [if_neg heq] at ha
            exact absurd ha (by simp)
        have hstep : Step prog s₀ s₁ :=
          Step.call s₀.regs regs' s₀.mem mem' s₀.pc fid fp hpc hcallee hfp
        cases ih s₁ h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ hstep hsteps

/- Monotonicity -/

lemma interp_mono (prog : Program) (oracle : CallOracle) :
    ∀ fuel fuel' s sf,
    fuel ≤ fuel' →
    interp prog oracle s fuel = some sf →
    interp prog oracle s fuel' = some sf := by
  intro fuel
  induction fuel with
  | zero => intros; simp [interp] at *
  | succ n ih =>
    intro fuel' s sf hle h
    match fuel' with
    | 0 => omega
    | m + 1 =>
      have hn : n ≤ m := Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hle)
      simp only [interp] at h ⊢
      match hpc : prog[s.pc]? with
      | none => simp [hpc] at h
      | some Instr.exit => simp only [hpc] at h ⊢; exact h
      | some (Instr.alu64 op dst src) =>
          simp only [hpc] at h ⊢; exact ih m _ _ hn h
      | some (Instr.alu32 op dst src) =>
          simp only [hpc] at h ⊢; exact ih m _ _ hn h
      | some (Instr.neg64 dst) =>
          simp only [hpc] at h ⊢; exact ih m _ _ hn h
      | some (Instr.neg32 dst) =>
          simp only [hpc] at h ⊢; exact ih m _ _ hn h
      | some (Instr.endian e sz dst) =>
          simp only [hpc] at h ⊢; exact ih m _ _ hn h
      | some (Instr.ja off) =>
          simp only [hpc] at h ⊢
          split_ifs at h ⊢ with hnn
          · exact ih m _ _ hn h
      | some (Instr.jmp64 op dst src off) =>
          simp only [hpc] at h ⊢
          by_cases hcond : evalJmp64 op (s.regs dst) (evalSrc s.regs src) = true
          · simp only [hcond, ite_true] at h ⊢
            split_ifs at h ⊢ with hnn
            · exact ih m _ _ hn h
          · simp only [Bool.not_eq_true] at hcond
            simp only [hcond] at h ⊢
            exact ih m _ _ hn h
      | some (Instr.jmp32 op dst src off) =>
          simp only [hpc] at h ⊢
          by_cases hcond : evalJmp32 op (s.regs dst) (evalSrc s.regs src) = true
          · simp only [hcond, ite_true] at h ⊢
            split_ifs at h ⊢ with hnn
            · exact ih m _ _ hn h
          · simp only [Bool.not_eq_true] at hcond
            simp only [hcond] at h ⊢
            exact ih m _ _ hn h
      | some (Instr.store sz dst off src) =>
          simp only [hpc] at h ⊢; exact ih m _ _ hn h
      | some (Instr.load sz dst src off) =>
          simp only [hpc] at h ⊢; exact ih m _ _ hn h
      | some (Instr.lddw dst imm) =>
          simp only [hpc] at h ⊢; exact ih m _ _ hn h
      | some (Instr.atomic sz op fetch dst src off) =>
          simp only [hpc] at h ⊢; exact ih m _ _ hn h
      | some (Instr.call fid) =>
          simp only [hpc] at h ⊢; exact ih m _ _ hn h

/- Termination for well-formed programs -/

private lemma verifies_pc_lt {prog : Program} {mapSize : ℕ}
    {callTypes : BitVec 32 → RegType} {pc : ℕ} {s : AState}
    (h : Verifies prog mapSize callTypes pc s) : pc < prog.size := by
  cases h with
  | exit pc s hp _ _ => exact (Array.getElem?_eq_some_iff.mp hp).choose
  | alu64 pc s op dst src t hp _ _ _ _ => exact (Array.getElem?_eq_some_iff.mp hp).choose
  | alu32 pc s op dst src t hp _ _ _ _ => exact (Array.getElem?_eq_some_iff.mp hp).choose
  | neg64 pc s dst hp _ _ => exact (Array.getElem?_eq_some_iff.mp hp).choose
  | neg32 pc s dst hp _ _ => exact (Array.getElem?_eq_some_iff.mp hp).choose
  | endian pc s e sz dst hp _ _ => exact (Array.getElem?_eq_some_iff.mp hp).choose
  | ja pc s off pc' hp _ _ _ => exact (Array.getElem?_eq_some_iff.mp hp).choose
  | jmp64 pc s op dst src off pc' hp _ _ _ _ _ _ => exact (Array.getElem?_eq_some_iff.mp hp).choose
  | jmp32 pc s op dst src off pc' hp _ _ _ _ _ _ => exact (Array.getElem?_eq_some_iff.mp hp).choose
  | load pc s sz dst src off hp _ _ => exact (Array.getElem?_eq_some_iff.mp hp).choose
  | store pc s sz dst off src hp _ _ _ => exact (Array.getElem?_eq_some_iff.mp hp).choose
  | lddw pc s dst imm hp _ => exact (Array.getElem?_eq_some_iff.mp hp).choose
  | atomic pc s sz op fetch dst src off hp _ _ _ _ =>
      exact (Array.getElem?_eq_some_iff.mp hp).choose
  | call pc s fid hp _ _ _ _ _ _ hrec => exact (Array.getElem?_eq_some_iff.mp hp).choose

private lemma interp_terminates_of_verifies
    (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
    (oracle : CallOracle)
    (hnb : NoBackEdges prog) :
    ∀ pc (abs_s : AState),
    Verifies prog mapSize callTypes pc abs_s →
    ∀ c_s : State, c_s.pc = pc →
    ∃ sf, interp prog oracle c_s (prog.size + 1 - pc) = some sf := by
  intro pc abs_s hv
  induction hv with
  | exit pc abs_s hprog _ _ =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := by
        exact (Array.getElem?_eq_some_iff.mp hprog).choose
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some Instr.exit from hpc_eq ▸ hprog]
      exists c_s
  | alu64 pc abs_s op dst src t hprog _ _ _ hrec ih =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt1 : pc + 1 < prog.size := by have := verifies_pc_lt hrec; omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel1 : prog.size + 1 - (pc + 1) = prog.size - pc := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some (Instr.alu64 op dst src) from hpc_eq ▸ hprog]
      let c_s' : State := { c_s with
        regs := c_s.regs.set dst (evalAlu64 op (c_s.regs dst) (evalSrc c_s.regs src)),
        pc := pc + 1 }
      rw [show ({ c_s with
            regs := c_s.regs.set dst (evalAlu64 op (c_s.regs dst) (evalSrc c_s.regs src)),
            pc := c_s.pc + 1 } : State) = c_s' from by simp [c_s', hpc_eq]]
      cases ih c_s' rfl with
      | intro sf hsf =>
        rw [hfuel1] at hsf
        exists sf
  | alu32 pc abs_s op dst src t hprog _ _ _ hrec ih =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt1 : pc + 1 < prog.size := by have := verifies_pc_lt hrec; omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel1 : prog.size + 1 - (pc + 1) = prog.size - pc := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some (Instr.alu32 op dst src) from hpc_eq ▸ hprog]
      let c_s' : State := { c_s with
        regs := c_s.regs.set dst (evalAlu32 op (c_s.regs dst) (evalSrc c_s.regs src)),
        pc := pc + 1 }
      rw [show ({ c_s with
            regs := c_s.regs.set dst (evalAlu32 op (c_s.regs dst) (evalSrc c_s.regs src)),
            pc := c_s.pc + 1 } : State) = c_s' from by simp [c_s', hpc_eq]]
      cases ih c_s' rfl with
      | intro sf hsf =>
        rw [hfuel1] at hsf
        exists sf
  | neg64 pc abs_s dst hprog _ hrec ih =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt1 : pc + 1 < prog.size := by have := verifies_pc_lt hrec; omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel1 : prog.size + 1 - (pc + 1) = prog.size - pc := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some (Instr.neg64 dst) from hpc_eq ▸ hprog]
      let c_s' : State := { c_s with
        regs := c_s.regs.set dst (- c_s.regs dst), pc := pc + 1 }
      rw [show ({ c_s with
            regs := c_s.regs.set dst (- c_s.regs dst),
            pc := c_s.pc + 1 } : State) = c_s' from by simp [c_s', hpc_eq]]
      cases ih c_s' rfl with
      | intro sf hsf =>
        rw [hfuel1] at hsf; exists sf
  | neg32 pc abs_s dst hprog _ hrec ih =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt1 : pc + 1 < prog.size := by have := verifies_pc_lt hrec; omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel1 : prog.size + 1 - (pc + 1) = prog.size - pc := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some (Instr.neg32 dst) from hpc_eq ▸ hprog]
      let c_s' : State := { c_s with
        regs := c_s.regs.set dst (zext32 (- c_s.regs dst)), pc := pc + 1 }
      rw [show ({ c_s with
            regs := c_s.regs.set dst (zext32 (- c_s.regs dst)),
            pc := c_s.pc + 1 } : State) = c_s' from by simp [c_s', hpc_eq]]
      cases ih c_s' rfl with
      | intro sf hsf =>
        rw [hfuel1] at hsf; exists sf
  | endian pc abs_s e sz dst hprog _ hrec ih =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt1 : pc + 1 < prog.size := by have := verifies_pc_lt hrec; omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel1 : prog.size + 1 - (pc + 1) = prog.size - pc := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some (Instr.endian e sz dst) from hpc_eq ▸ hprog]
      let c_s' : State := { c_s with
        regs := c_s.regs.set dst (evalEndian e sz (c_s.regs dst)), pc := pc + 1 }
      rw [show ({ c_s with
            regs := c_s.regs.set dst (evalEndian e sz (c_s.regs dst)),
            pc := c_s.pc + 1 } : State) = c_s' from by simp [c_s', hpc_eq]]
      cases ih c_s' rfl with
      | intro sf hsf =>
        rw [hfuel1] at hsf; exists sf
  | ja pc abs_s off pc' hprog hpc'eq hnn hrec ih =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt' : pc'.toNat < prog.size := verifies_pc_lt hrec
      have hfwd : pc < pc'.toNat := by
        have h0 := hnb pc hlt
        simp only [hprog, isForwardJump] at h0
        have heq : pc'.toNat = (↑pc + 1 + offset16ToInt off).toNat := by
          simp [hpc'eq]
        omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel' : prog.size + 1 - pc'.toNat ≤ prog.size - pc := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some (Instr.ja off) from hpc_eq ▸ hprog]
      have hpc'_eq2 : (c_s.pc : Int) + 1 + offset16ToInt off = pc' := by
        rw [hpc_eq]; exact hpc'eq.symm
      rw [hpc'_eq2, dif_pos hnn]
      cases ih { c_s with pc := pc'.toNat } rfl with
      | intro sf hsf =>
        exists sf
        exact interp_mono prog oracle _ _ _ _ hfuel' hsf
  | jmp64 pc abs_s op dst src off pc' hprog _ _ hpc'eq hnn hrec_taken hrec_fall ih_taken ih_fall =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt_taken : pc'.toNat < prog.size := verifies_pc_lt hrec_taken
      have hlt_fall : pc + 1 < prog.size := by have := verifies_pc_lt hrec_fall; omega
      have hfwd : pc < pc'.toNat := by
        have h0 := hnb pc hlt
        simp only [hprog, isForwardJump] at h0
        have heq : pc'.toNat = (↑pc + 1 + offset16ToInt off).toNat := by simp [hpc'eq]
        omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel_taken : prog.size + 1 - pc'.toNat ≤ prog.size - pc := by omega
      have hfuel_fall : prog.size + 1 - (pc + 1) = prog.size - pc := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some (Instr.jmp64 op dst src off) from hpc_eq ▸ hprog]
      by_cases hcond : evalJmp64 op (c_s.regs dst) (evalSrc c_s.regs src) = true
      · simp only [hcond, ite_true]
        have hpc'_eq2 : (c_s.pc : Int) + 1 + offset16ToInt off = pc' := by
          rw [hpc_eq]; exact hpc'eq.symm
        rw [hpc'_eq2, dif_pos hnn]
        cases ih_taken { c_s with pc := pc'.toNat } rfl with
        | intro sf hsf =>
          exists sf
          exact interp_mono prog oracle _ _ _ _ hfuel_taken hsf
      · simp only [Bool.not_eq_true] at hcond
        simp only [hcond, Bool.false_eq_true, ite_false]
        rw [hpc_eq]
        cases ih_fall { c_s with pc := pc + 1 } rfl with
        | intro sf hsf =>
          rw [hfuel_fall] at hsf; exists sf
  | jmp32 pc abs_s op dst src off pc' hprog _ _ hpc'eq hnn hrec_taken hrec_fall ih_taken ih_fall =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt_taken : pc'.toNat < prog.size := verifies_pc_lt hrec_taken
      have hlt_fall : pc + 1 < prog.size := by have := verifies_pc_lt hrec_fall; omega
      have hfwd : pc < pc'.toNat := by
        have h0 := hnb pc hlt
        simp only [hprog, isForwardJump] at h0
        have heq : pc'.toNat = (↑pc + 1 + offset16ToInt off).toNat := by simp [hpc'eq]
        omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel_taken : prog.size + 1 - pc'.toNat ≤ prog.size - pc := by omega
      have hfuel_fall : prog.size + 1 - (pc + 1) = prog.size - pc := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some (Instr.jmp32 op dst src off) from hpc_eq ▸ hprog]
      by_cases hcond : evalJmp32 op (c_s.regs dst) (evalSrc c_s.regs src) = true
      · simp only [hcond, ite_true]
        have hpc'_eq2 : (c_s.pc : Int) + 1 + offset16ToInt off = pc' := by
          rw [hpc_eq]; exact hpc'eq.symm
        rw [hpc'_eq2, dif_pos hnn]
        cases ih_taken { c_s with pc := pc'.toNat } rfl with
        | intro sf hsf =>
          exists sf
          exact interp_mono prog oracle _ _ _ _ hfuel_taken hsf
      · simp only [Bool.not_eq_true] at hcond
        simp only [hcond, Bool.false_eq_true, ite_false]
        rw [hpc_eq]
        cases ih_fall { c_s with pc := pc + 1 } rfl with
        | intro sf hsf =>
          rw [hfuel_fall] at hsf; exists sf
  | load pc abs_s sz dst src off hprog _ hrec ih =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt1 : pc + 1 < prog.size := by have := verifies_pc_lt hrec; omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel1 : prog.size + 1 - (pc + 1) = prog.size - pc := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some (Instr.load sz dst src off) from hpc_eq ▸ hprog]
      rw [hpc_eq]
      cases ih { c_s with
          regs := c_s.regs.set dst (readMem c_s.mem (c_s.regs src + BitVec.signExtend 64 off) sz),
          pc := pc + 1 } rfl with
      | intro sf hsf =>
        rw [hfuel1] at hsf; exists sf
  | store pc abs_s sz dst off src hprog _ _ hrec ih =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt1 : pc + 1 < prog.size := by have := verifies_pc_lt hrec; omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel1 : prog.size + 1 - (pc + 1) = prog.size - pc := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some (Instr.store sz dst off src) from hpc_eq ▸ hprog]
      rw [hpc_eq]
      cases ih { c_s with
          mem := writeMem c_s.mem
              (c_s.regs dst + BitVec.signExtend 64 off) (evalSrc c_s.regs src) sz,
          pc := pc + 1 } rfl with
      | intro sf hsf =>
        rw [hfuel1] at hsf; exists sf
  | lddw pc abs_s dst imm hprog hrec ih =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt2 : pc + 2 < prog.size := by have := verifies_pc_lt hrec; omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel2 : prog.size + 1 - (pc + 2) ≤ prog.size - pc := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some (Instr.lddw dst imm) from hpc_eq ▸ hprog]
      rw [hpc_eq]
      cases ih { c_s with regs := c_s.regs.set dst imm, pc := pc + 2 } rfl with
      | intro sf hsf =>
        exists sf
        exact interp_mono prog oracle _ _ _ _ hfuel2 hsf
  | atomic pc abs_s sz op fetch dst src off hprog _ _ _ hrec ih =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt1 : pc + 1 < prog.size := by have := verifies_pc_lt hrec; omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel1 : prog.size + 1 - (pc + 1) = prog.size - pc := by omega
      rw [hfuel]
      simp only [interp,
        show prog[c_s.pc]? = some (Instr.atomic sz op fetch dst src off) from hpc_eq ▸ hprog]
      rw [hpc_eq]
      -- Build the next state matching interp's internal let-bindings
      set addr   := c_s.regs dst + BitVec.signExtend 64 off with haddr
      set oldVal := readMem c_s.mem addr sz with holdVal
      set newVal := (match op with
        | AtomicOp.add     => oldVal + c_s.regs src
        | AtomicOp.or      => oldVal ||| c_s.regs src
        | AtomicOp.and     => oldVal &&& c_s.regs src
        | AtomicOp.xor     => oldVal ^^^ c_s.regs src
        | AtomicOp.xchg    => c_s.regs src
        | AtomicOp.cmpxchg =>
            if c_s.regs Reg.r0 = oldVal then c_s.regs src else oldVal) with hnewVal
      set mem'  := writeMem c_s.mem addr newVal sz with hmem'
      set regs' := (match op with
        | AtomicOp.cmpxchg => c_s.regs.set Reg.r0 oldVal
        | _                => if fetch then c_s.regs.set src oldVal else c_s.regs) with hregs'
      cases ih ({ regs := regs', mem := mem', pc := pc + 1 } : State) rfl with
      | intro sf hsf =>
        rw [hfuel1] at hsf; exists sf
  | call pc abs_s fid hprog _ _ _ _ _ _ hrec ih =>
      intro c_s hpc_eq
      have hlt : pc < prog.size := (Array.getElem?_eq_some_iff.mp hprog).choose
      have hlt1 : pc + 1 < prog.size := by have := verifies_pc_lt hrec; omega
      have hfuel : prog.size + 1 - pc = (prog.size - pc) + 1 := by omega
      have hfuel1 : prog.size + 1 - (pc + 1) = prog.size - pc := by omega
      rw [hfuel]
      simp only [interp, show prog[c_s.pc]? = some (Instr.call fid) from hpc_eq ▸ hprog]
      rw [hpc_eq]
      set regs' := (oracle fid c_s.regs c_s.mem).1 with hregs'
      set mem'  := (oracle fid c_s.regs c_s.mem).2 with hmem'
      cases ih ({ regs := regs', mem := mem', pc := pc + 1 } : State) rfl with
      | intro sf hsf =>
        rw [hfuel1] at hsf; exists sf

theorem wf_interp_terminates
    (prog : Program)
    (mapSize : ℕ)
    (callTypes : BitVec 32 → RegType)
    (oracle : CallOracle)
    (hwf : WellFormed prog mapSize callTypes)
    (s₀ : State)
    (hs₀ : s₀.pc = 0) :
    ∃ sf : State, interp prog oracle s₀ (prog.size + 1) = some sf := by
  cases hwf with
  | intro hnb rest =>
    cases rest with
    | intro _ hv =>
  have h := interp_terminates_of_verifies prog mapSize callTypes oracle hnb
               0 initialAState hv s₀ hs₀
  simpa using h

end Ebpf

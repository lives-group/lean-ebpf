import Ebpf.Semantics
import Ebpf.EbpfVerifier
import Ebpf.Interp

namespace Ebpf

/- Helper lemmas for PC advancement under NoBackEdges -/

lemma noBackEdges_ja_lt
    (prog : Program) (hnb : NoBackEdges prog)
    (pc : ℕ) (off : BitVec 16)
    (hpc : prog[pc]? = some (Instr.ja off))
    (hlt : pc < prog.size) :
    pc < ((pc : Int) + 1 + offset16ToInt off).toNat := by
  have h := hnb pc hlt
  simp only [hpc, isForwardJump] at h
  exact h

lemma noBackEdges_jmp64_lt
    (prog : Program) (hnb : NoBackEdges prog)
    (pc : ℕ) (op : JmpOp) (dst : Reg) (src : Src) (off : BitVec 16)
    (hpc : prog[pc]? = some (Instr.jmp64 op dst src off))
    (hlt : pc < prog.size) :
    pc < ((pc : Int) + 1 + offset16ToInt off).toNat := by
  have h := hnb pc hlt
  simp only [hpc, isForwardJump] at h
  exact h

lemma noBackEdges_jmp32_lt
    (prog : Program) (hnb : NoBackEdges prog)
    (pc : ℕ) (op : JmpOp) (dst : Reg) (src : Src) (off : BitVec 16)
    (hpc : prog[pc]? = some (Instr.jmp32 op dst src off))
    (hlt : pc < prog.size) :
    pc < ((pc : Int) + 1 + offset16ToInt off).toNat := by
  have h := hnb pc hlt
  simp only [hpc, isForwardJump] at h
  exact h

/- Fuel-free interpreter -/

private def evalAtomicNewVal (op : AtomicOp) (oldVal srcVal r0Val : BitVec 64) : BitVec 64 :=
  match op with
  | AtomicOp.add     => oldVal + srcVal
  | AtomicOp.or      => oldVal ||| srcVal
  | AtomicOp.and     => oldVal &&& srcVal
  | AtomicOp.xor     => oldVal ^^^ srcVal
  | AtomicOp.xchg    => srcVal
  | AtomicOp.cmpxchg => if r0Val = oldVal then srcVal else oldVal

private def evalAtomicNewRegs (op : AtomicOp) (fetch : Bool) (regs : RegFile)
    (src : Reg) (oldVal : BitVec 64) : RegFile :=
  match op with
  | AtomicOp.cmpxchg => regs.set Reg.r0 oldVal
  | _                => if fetch then regs.set src oldVal else regs

@[irreducible] def interpNF (prog : Program) (oracle : CallOracle) (hnb : NoBackEdges prog)
    (s : State) : Option State :=
  match hpc : prog[s.pc]? with
  | none            => none
  | some Instr.exit => some s
  | some (Instr.alu64 op dst src) =>
      let v := evalAlu64 op (s.regs dst) (evalSrc s.regs src)
      interpNF prog oracle hnb { s with regs := s.regs.set dst v, pc := s.pc + 1 }
  | some (Instr.alu32 op dst src) =>
      let v := evalAlu32 op (s.regs dst) (evalSrc s.regs src)
      interpNF prog oracle hnb { s with regs := s.regs.set dst v, pc := s.pc + 1 }
  | some (Instr.neg64 dst) =>
      interpNF prog oracle hnb
        { s with regs := s.regs.set dst (- s.regs dst), pc := s.pc + 1 }
  | some (Instr.neg32 dst) =>
      interpNF prog oracle hnb
        { s with regs := s.regs.set dst (zext32 (- s.regs dst)), pc := s.pc + 1 }
  | some (Instr.endian e sz dst) =>
      let v := evalEndian e sz (s.regs dst)
      interpNF prog oracle hnb { s with regs := s.regs.set dst v, pc := s.pc + 1 }
  | some (Instr.ja off) =>
      let pc' : Int := (s.pc : Int) + 1 + offset16ToInt off
      if _ : 0 ≤ pc' then
        interpNF prog oracle hnb { s with pc := pc'.toNat }
      else none
  | some (Instr.jmp64 op dst src off) =>
      if evalJmp64 op (s.regs dst) (evalSrc s.regs src) then
        let pc' : Int := (s.pc : Int) + 1 + offset16ToInt off
        if _ : 0 ≤ pc' then
          interpNF prog oracle hnb { s with pc := pc'.toNat }
        else none
      else
        interpNF prog oracle hnb { s with pc := s.pc + 1 }
  | some (Instr.jmp32 op dst src off) =>
      if evalJmp32 op (s.regs dst) (evalSrc s.regs src) then
        let pc' : Int := (s.pc : Int) + 1 + offset16ToInt off
        if _ : 0 ≤ pc' then
          interpNF prog oracle hnb { s with pc := pc'.toNat }
        else none
      else
        interpNF prog oracle hnb { s with pc := s.pc + 1 }
  | some (Instr.store sz dst off src) =>
      let addr := s.regs dst + BitVec.signExtend 64 off
      let mem' := writeMem s.mem addr (evalSrc s.regs src) sz
      interpNF prog oracle hnb { s with mem := mem', pc := s.pc + 1 }
  | some (Instr.load sz dst src off) =>
      let addr := s.regs src + BitVec.signExtend 64 off
      let v    := readMem s.mem addr sz
      interpNF prog oracle hnb { s with regs := s.regs.set dst v, pc := s.pc + 1 }
  | some (Instr.lddw dst imm) =>
      interpNF prog oracle hnb { s with regs := s.regs.set dst imm, pc := s.pc + 2 }
  | some (Instr.atomic sz op fetch dst src off) =>
      let addr   := s.regs dst + BitVec.signExtend 64 off
      let oldVal := readMem s.mem addr sz
      let newVal := evalAtomicNewVal op oldVal (s.regs src) (s.regs Reg.r0)
      let mem'   := writeMem s.mem addr newVal sz
      let regs'  := evalAtomicNewRegs op fetch s.regs src oldVal
      interpNF prog oracle hnb { regs := regs', mem := mem', pc := s.pc + 1 }
  | some (Instr.call fid) =>
      let (regs', mem') := oracle fid s.regs s.mem
      interpNF prog oracle hnb { regs := regs', mem := mem', pc := s.pc + 1 }
termination_by prog.size - s.pc
decreasing_by
  all_goals (
    have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
    first
    | omega
    | (have hfwd := noBackEdges_ja_lt    prog hnb s.pc off (by assumption) hlt; omega)
    | (have hfwd := noBackEdges_jmp64_lt prog hnb s.pc op dst src off (by assumption) hlt; omega)
    | (have hfwd := noBackEdges_jmp32_lt prog hnb s.pc op dst src off (by assumption) hlt; omega)
  )

/- Coherence theorem for interpNF -/

lemma prog_getElem?_none_of_ge (prog : Program) (pc : ℕ) (h : prog.size ≤ pc) :
    prog[pc]? = (none : Option Instr) := by
  cases hq : prog[pc]?
  · rfl
  · exact absurd (Array.getElem?_eq_some_iff.mp hq).choose (Nat.not_lt_of_le h)

lemma interpNF_eq' (prog : Program) (oracle : CallOracle) (hnb : NoBackEdges prog)
    (s : State) :
    interpNF prog oracle hnb s =
    match prog[s.pc]? with
    | none            => none
    | some Instr.exit => some s
    | some (Instr.alu64 op dst src) =>
        interpNF prog oracle hnb
          { s with regs := s.regs.set dst (evalAlu64 op (s.regs dst) (evalSrc s.regs src)),
                   pc   := s.pc + 1 }
    | some (Instr.alu32 op dst src) =>
        interpNF prog oracle hnb
          { s with regs := s.regs.set dst (evalAlu32 op (s.regs dst) (evalSrc s.regs src)),
                   pc   := s.pc + 1 }
    | some (Instr.neg64 dst) =>
        interpNF prog oracle hnb
          { s with regs := s.regs.set dst (- s.regs dst), pc := s.pc + 1 }
    | some (Instr.neg32 dst) =>
        interpNF prog oracle hnb
          { s with regs := s.regs.set dst (zext32 (- s.regs dst)), pc := s.pc + 1 }
    | some (Instr.endian e sz dst) =>
        interpNF prog oracle hnb
          { s with regs := s.regs.set dst (evalEndian e sz (s.regs dst)), pc := s.pc + 1 }
    | some (Instr.ja off) =>
        if _ : 0 ≤ ((s.pc : Int) + 1 + offset16ToInt off) then
          interpNF prog oracle hnb { s with pc := ((s.pc : Int) + 1 + offset16ToInt off).toNat }
        else none
    | some (Instr.jmp64 op dst src off) =>
        if evalJmp64 op (s.regs dst) (evalSrc s.regs src) then
          if _ : 0 ≤ ((s.pc : Int) + 1 + offset16ToInt off) then
            interpNF prog oracle hnb { s with pc := ((s.pc : Int) + 1 + offset16ToInt off).toNat }
          else none
        else
          interpNF prog oracle hnb { s with pc := s.pc + 1 }
    | some (Instr.jmp32 op dst src off) =>
        if evalJmp32 op (s.regs dst) (evalSrc s.regs src) then
          if _ : 0 ≤ ((s.pc : Int) + 1 + offset16ToInt off) then
            interpNF prog oracle hnb { s with pc := ((s.pc : Int) + 1 + offset16ToInt off).toNat }
          else none
        else
          interpNF prog oracle hnb { s with pc := s.pc + 1 }
    | some (Instr.store sz dst off src) =>
        interpNF prog oracle hnb
          { s with mem := writeMem s.mem (s.regs dst + BitVec.signExtend 64 off)
                                   (evalSrc s.regs src) sz,
                   pc  := s.pc + 1 }
    | some (Instr.load sz dst src off) =>
        interpNF prog oracle hnb
          { s with regs := s.regs.set dst
                             (readMem s.mem (s.regs src + BitVec.signExtend 64 off) sz),
                   pc   := s.pc + 1 }
    | some (Instr.lddw dst imm) =>
        interpNF prog oracle hnb { s with regs := s.regs.set dst imm, pc := s.pc + 2 }
    | some (Instr.atomic sz op fetch dst src off) =>
        let addr   := s.regs dst + BitVec.signExtend 64 off
        let oldVal := readMem s.mem addr sz
        let newVal := evalAtomicNewVal op oldVal (s.regs src) (s.regs Reg.r0)
        let mem'   := writeMem s.mem addr newVal sz
        let regs'  := evalAtomicNewRegs op fetch s.regs src oldVal
        interpNF prog oracle hnb { regs := regs', mem := mem', pc := s.pc + 1 }
    | some (Instr.call fid) =>
        interpNF prog oracle hnb
          { regs := (oracle fid s.regs s.mem).1, mem := (oracle fid s.regs s.mem).2,
            pc   := s.pc + 1 } := by
  rcases hpc : prog[s.pc]? with _ | instr
  · rw [interpNF.eq_1, hpc]
  · cases instr <;> rw [interpNF.eq_1, hpc]

private lemma interpNF_coherent_aux
    (prog : Program) (oracle : CallOracle) (hnb : NoBackEdges prog)
    (hok : OracleOk oracle) (n : ℕ) :
    ∀ (s₀ sf : State),
      prog.size - s₀.pc ≤ n →
      interpNF prog oracle hnb s₀ = some sf →
      ∃ _ : Steps prog s₀ sf, prog[sf.pc]? = some Instr.exit := by
  induction n with
  | zero =>
    intro s₀ sf hle h
    have hge : prog.size ≤ s₀.pc := by omega
    have hnone := prog_getElem?_none_of_ge prog s₀.pc hge
    rw [interpNF_eq'] at h; simp only [hnone] at h; simp at h
  | succ n ih =>
    intro s₀ sf hle h
    rw [interpNF_eq'] at h
    match hpc : prog[s₀.pc]? with
    | none =>
        simp only [hpc] at h; simp at h
    | some Instr.exit =>
        simp only [hpc] at h
        rw [show sf = s₀ from (Option.some.inj h).symm]
        exists Steps.refl s₀
    | some (Instr.alu64 op dst src) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        cases ih _ sf (by change prog.size - (s₀.pc + 1) ≤ n; omega) h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ (Step.alu64 s₀.regs s₀.mem s₀.pc op dst src _ hpc rfl) hsteps
    | some (Instr.alu32 op dst src) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        cases ih _ sf (by change prog.size - (s₀.pc + 1) ≤ n; omega) h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ (Step.alu32 s₀.regs s₀.mem s₀.pc op dst src _ hpc rfl) hsteps
    | some (Instr.neg64 dst) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        cases ih _ sf (by change prog.size - (s₀.pc + 1) ≤ n; omega) h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ (Step.neg64 s₀.regs s₀.mem s₀.pc dst hpc) hsteps
    | some (Instr.neg32 dst) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        cases ih _ sf (by change prog.size - (s₀.pc + 1) ≤ n; omega) h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ (Step.neg32 s₀.regs s₀.mem s₀.pc dst hpc) hsteps
    | some (Instr.endian e sz dst) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        cases ih _ sf (by change prog.size - (s₀.pc + 1) ≤ n; omega) h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ (Step.endian s₀.regs s₀.mem s₀.pc e sz dst _ hpc rfl) hsteps
    | some (Instr.ja off) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        split_ifs at h with hnn
        · have hfwd := noBackEdges_ja_lt prog hnb s₀.pc off hpc hlt
          cases ih _ sf
              (by change prog.size - (↑s₀.pc + 1 + offset16ToInt off).toNat ≤ n; omega) h with
          | intro hsteps hexit =>
            exists Steps.step _ _ _ (Step.ja s₀.regs s₀.mem s₀.pc off _ hpc rfl hnn) hsteps
    | some (Instr.jmp64 op dst src off) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        by_cases hcond : evalJmp64 op (s₀.regs dst) (evalSrc s₀.regs src) = true
        · simp only [hcond, ite_true] at h
          split_ifs at h with hnn
          · have hfwd := noBackEdges_jmp64_lt prog hnb s₀.pc op dst src off hpc hlt
            cases ih _ sf
                (by change prog.size - (↑s₀.pc + 1 + offset16ToInt off).toNat ≤ n; omega) h with
            | intro hsteps hexit =>
              exists Steps.step _ _ _
                     (Step.jmp64_taken s₀.regs s₀.mem s₀.pc op dst src off _ hpc hcond rfl hnn)
                     hsteps
        · simp only [Bool.not_eq_true] at hcond
          simp only [hcond, Bool.false_eq_true, ite_false] at h
          cases ih _ sf (by change prog.size - (s₀.pc + 1) ≤ n; omega) h with
          | intro hsteps hexit =>
            exists Steps.step _ _ _
                   (Step.jmp64_fallthrough s₀.regs s₀.mem s₀.pc op dst src off hpc hcond)
                   hsteps
    | some (Instr.jmp32 op dst src off) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        by_cases hcond : evalJmp32 op (s₀.regs dst) (evalSrc s₀.regs src) = true
        · simp only [hcond, ite_true] at h
          split_ifs at h with hnn
          · have hfwd := noBackEdges_jmp32_lt prog hnb s₀.pc op dst src off hpc hlt
            cases ih _ sf
                (by change prog.size - (↑s₀.pc + 1 + offset16ToInt off).toNat ≤ n; omega) h with
            | intro hsteps hexit =>
              exists Steps.step _ _ _
                     (Step.jmp32_taken s₀.regs s₀.mem s₀.pc op dst src off _ hpc hcond rfl hnn)
                     hsteps
        · simp only [Bool.not_eq_true] at hcond
          simp only [hcond, Bool.false_eq_true, ite_false] at h
          cases ih _ sf (by change prog.size - (s₀.pc + 1) ≤ n; omega) h with
          | intro hsteps hexit =>
            exists Steps.step _ _ _
                   (Step.jmp32_fallthrough s₀.regs s₀.mem s₀.pc op dst src off hpc hcond)
                   hsteps
    | some (Instr.store sz dst off src) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        cases ih _ sf (by change prog.size - (s₀.pc + 1) ≤ n; omega) h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _
                 (Step.store s₀.regs s₀.mem s₀.pc sz dst off src
                   (s₀.regs dst + BitVec.signExtend 64 off)
                   (writeMem s₀.mem (s₀.regs dst + BitVec.signExtend 64 off)
                     (evalSrc s₀.regs src) sz)
                   hpc rfl rfl)
                 hsteps
    | some (Instr.load sz dst src off) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        cases ih _ sf (by change prog.size - (s₀.pc + 1) ≤ n; omega) h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _
                 (Step.load s₀.regs s₀.mem s₀.pc sz dst src off
                   (s₀.regs src + BitVec.signExtend 64 off)
                   (readMem s₀.mem (s₀.regs src + BitVec.signExtend 64 off) sz)
                   hpc rfl rfl)
                 hsteps
    | some (Instr.lddw dst imm) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        cases ih _ sf (by change prog.size - (s₀.pc + 2) ≤ n; omega) h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _ (Step.lddw s₀.regs s₀.mem s₀.pc dst imm hpc) hsteps
    | some (Instr.atomic sz op fetch dst src off) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        let addr   := s₀.regs dst + BitVec.signExtend 64 off
        let oldVal := readMem s₀.mem addr sz
        let newVal := evalAtomicNewVal op oldVal (s₀.regs src) (s₀.regs Reg.r0)
        let mem'   := writeMem s₀.mem addr newVal sz
        let regs'  := evalAtomicNewRegs op fetch s₀.regs src oldVal
        cases ih { regs := regs', mem := mem', pc := s₀.pc + 1 } sf
            (by change prog.size - (s₀.pc + 1) ≤ n; omega) h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _
                 (Step.atomic_op s₀.regs s₀.mem s₀.pc sz op fetch dst src off
                   addr oldVal newVal mem' regs' hpc rfl rfl rfl rfl rfl)
                 hsteps
    | some (Instr.call fid) =>
        simp only [hpc] at h
        have hlt : s₀.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        set regs' := (oracle fid s₀.regs s₀.mem).1 with hregs'_def
        set mem'  := (oracle fid s₀.regs s₀.mem).2 with hmem'_def
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
          · simp [if_neg heq] at ha
        cases ih { regs := regs', mem := mem', pc := s₀.pc + 1 } sf
            (by change prog.size - (s₀.pc + 1) ≤ n; omega) h with
        | intro hsteps hexit =>
          exists Steps.step _ _ _
                 (Step.call s₀.regs regs' s₀.mem mem' s₀.pc fid fp hpc hcallee hfp)
                 hsteps

theorem interpNF_coherent
    (prog : Program) (oracle : CallOracle) (hnb : NoBackEdges prog)
    (hok : OracleOk oracle)
    (s₀ sf : State)
    (h : interpNF prog oracle hnb s₀ = some sf) :
    ∃ _ : Steps prog s₀ sf, prog[sf.pc]? = some Instr.exit :=
  interpNF_coherent_aux prog oracle hnb hok prog.size s₀ sf (Nat.sub_le _ _) h

end Ebpf

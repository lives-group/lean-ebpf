import Ebpf.InterpNF
import Ebpf.LogicSoundness

namespace Ebpf

/- Bridge: fuel-based ↔ fuel-free interpreter -/

private lemma interp_eq_interpNF
    (prog : Program) (oracle : CallOracle) (hnb : NoBackEdges prog) :
    ∀ (n : ℕ) (s : State), prog.size - s.pc ≤ n →
    interp prog oracle s (n + 1) = interpNF prog oracle hnb s := by
  intro n
  induction n with
  | zero =>
    intro s hle
    have hge : prog.size ≤ s.pc := by omega
    simp only [interp, interpNF_eq', prog_getElem?_none_of_ge prog s.pc hge]
  | succ n ih =>
    intro s hle
    match hpc : prog[s.pc]? with
    | none =>
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
    | some Instr.exit =>
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
    | some (Instr.alu64 op dst src) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        exact ih _ (by change prog.size - (s.pc + 1) ≤ n; omega)
    | some (Instr.alu32 op dst src) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        exact ih _ (by change prog.size - (s.pc + 1) ≤ n; omega)
    | some (Instr.neg64 dst) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        exact ih _ (by change prog.size - (s.pc + 1) ≤ n; omega)
    | some (Instr.neg32 dst) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        exact ih _ (by change prog.size - (s.pc + 1) ≤ n; omega)
    | some (Instr.endian e sz dst) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        exact ih _ (by change prog.size - (s.pc + 1) ≤ n; omega)
    | some (Instr.ja off) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        have hfwd := noBackEdges_ja_lt prog hnb s.pc off hpc hlt
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        split_ifs with hnn
        · exact ih _ (by
            change prog.size - ((s.pc : Int) + 1 + offset16ToInt off).toNat ≤ n; omega)
        · rfl
    | some (Instr.jmp64 op dst src off) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        by_cases hcond : evalJmp64 op (s.regs dst) (evalSrc s.regs src) = true
        · simp only [hcond, ite_true]
          split_ifs with hnn
          · have hfwd := noBackEdges_jmp64_lt prog hnb s.pc op dst src off hpc hlt
            exact ih _ (by
              change prog.size - ((s.pc : Int) + 1 + offset16ToInt off).toNat ≤ n; omega)
          · rfl
        · simp only [Bool.not_eq_true] at hcond
          simp only [hcond, Bool.false_eq_true, ite_false]
          exact ih _ (by change prog.size - (s.pc + 1) ≤ n; omega)
    | some (Instr.jmp32 op dst src off) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        by_cases hcond : evalJmp32 op (s.regs dst) (evalSrc s.regs src) = true
        · simp only [hcond, ite_true]
          split_ifs with hnn
          · have hfwd := noBackEdges_jmp32_lt prog hnb s.pc op dst src off hpc hlt
            exact ih _ (by
              change prog.size - ((s.pc : Int) + 1 + offset16ToInt off).toNat ≤ n; omega)
          · rfl
        · simp only [Bool.not_eq_true] at hcond
          simp only [hcond, Bool.false_eq_true, ite_false]
          exact ih _ (by change prog.size - (s.pc + 1) ≤ n; omega)
    | some (Instr.store sz dst off src) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        exact ih _ (by change prog.size - (s.pc + 1) ≤ n; omega)
    | some (Instr.load sz dst src off) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        exact ih _ (by change prog.size - (s.pc + 1) ≤ n; omega)
    | some (Instr.lddw dst imm) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        exact ih _ (by change prog.size - (s.pc + 2) ≤ n; omega)
    | some (Instr.atomic sz op fetch dst src off) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        exact ih _ (by change prog.size - (s.pc + 1) ≤ n; omega)
    | some (Instr.call fid) =>
        have hlt : s.pc < prog.size := (Array.getElem?_eq_some_iff.mp hpc).choose
        conv_lhs => unfold interp; simp only [hpc]
        conv_rhs => rw [interpNF_eq']; simp only [hpc]
        exact ih _ (by change prog.size - (s.pc + 1) ≤ n; omega)

/- Soundness theorems for interpNF -/

theorem interpNF_terminates
    (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
    (oracle : CallOracle)
    (hwf : WellFormed prog mapSize callTypes)
    (s₀ : State) (hs₀ : s₀.pc = 0) :
    ∃ sf : State, interpNF prog oracle hwf.1 s₀ = some sf := by
  cases wf_interp_terminates prog mapSize callTypes oracle hwf s₀ hs₀ with
  | intro sf hinterp =>
    exists sf
    exact (interp_eq_interpNF prog oracle hwf.1 prog.size s₀ (by omega)).symm.trans hinterp

theorem sem_triple_interpNF_sound
    (prog : Program) (pc : ℕ) (P Q : Assert)
    (hst : SemTriple prog pc P Q)
    (oracle : CallOracle)
    (hnb : NoBackEdges prog)
    (hok : OracleOk oracle)
    (h1 h2 : Heap)
    (s sf : State)
    (hpc : s.pc = pc)
    (hP : P s.regs h1)
    (hcons : Heap.Consistent (Heap.union h1 h2) s.mem)
    (hdisj : Heap.Disjoint h1 h2)
    (hhs : OracleHeapSafe oracle (Heap.union h1 h2))
    (hint : interpNF prog oracle hnb s = some sf) :
    ∃ hf1 : Heap,
      Q sf.regs hf1 ∧
      Heap.Consistent (Heap.union hf1 h2) sf.mem ∧
      Heap.Disjoint hf1 h2 :=
  sem_triple_interp_sound prog pc P Q hst oracle hok h1 h2 s sf _
    hpc hP hcons hdisj hhs
    ((interp_eq_interpNF prog oracle hnb (prog.size - s.pc) s le_rfl).trans hint)

theorem wf_interpNF_sound
    (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
    (Q : Assert)
    (hwf : WellFormed prog mapSize callTypes)
    (oracle : CallOracle) (hok : OracleOk oracle)
    (h1 h2 : Heap) (s sf : State)
    (hpc : s.pc = 0)
    (hP : vcgWP prog Q (prog.size + 1) 0 s.regs h1)
    (hcons : Heap.Consistent (Heap.union h1 h2) s.mem)
    (hdisj : Heap.Disjoint h1 h2)
    (hhs : OracleHeapSafe oracle (Heap.union h1 h2))
    (hint : interpNF prog oracle hwf.1 s = some sf) :
    ∃ hf1 : Heap,
      Q sf.regs hf1 ∧
      Heap.Consistent (Heap.union hf1 h2) sf.mem ∧
      Heap.Disjoint hf1 h2 :=
  sem_triple_interpNF_sound prog 0 _ Q (wf_sem_sound prog mapSize callTypes Q hwf)
    oracle hwf.1 hok h1 h2 s sf hpc hP hcons hdisj hhs hint

end Ebpf

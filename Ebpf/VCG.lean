import Ebpf.EbpfLogic
import Ebpf.EbpfVerifier

set_option linter.style.emptyLine false

namespace Ebpf

/- Verification Condition Generator (VCG) -/

def vcgWP (prog : Program) (Q : Assert) : ℕ → ℕ → Assert
  | 0,      _  => Q
  | (n+1), pc  =>
      match prog[pc]? with
      | none => Q
      | some Instr.exit => Q
      | some (Instr.alu64 op dst src) =>
          wp_alu64 op dst src (vcgWP prog Q n (pc + 1))
      | some (Instr.alu32 op dst src) =>
          wp_alu32  op dst src (vcgWP prog Q n (pc + 1))
      | some (Instr.neg64 dst) =>
          wp_neg64 dst (vcgWP prog Q n (pc + 1))
      | some (Instr.neg32 dst) =>
          wp_neg32  dst (vcgWP prog Q n (pc + 1))
      | some (Instr.endian e w dst) =>
          wp_endian e w dst (vcgWP prog Q n (pc + 1))
      | some (Instr.lddw dst imm) =>
          wp_lddw   dst imm (vcgWP prog Q n (pc + 2))
      | some (Instr.load sz dst src off)  =>
          wp_load   sz dst src off  (vcgWP prog Q n (pc + 1))
      | some (Instr.store sz dst off src) =>
          wp_store  sz dst off src  (vcgWP prog Q n (pc + 1))
      | some (Instr.call _) =>
          wp_call (vcgWP prog Q n (pc + 1))
      | some (Instr.atomic sz op f dst src off) =>
          wp_atomic sz op f dst src off (vcgWP prog Q n (pc + 1))
      | some (Instr.ja off) =>
          vcgWP prog Q n ((pc : Int) + 1 + offset16ToInt off).toNat
      | some (Instr.jmp64 op dst src off) =>
          let tgt := ((pc : Int) + 1 + offset16ToInt off).toNat
          wp_jmp64 op dst src (vcgWP prog Q n tgt) (vcgWP prog Q n (pc + 1))
      | some (Instr.jmp32 op dst src off) =>
          let tgt := ((pc : Int) + 1 + offset16ToInt off).toNat
          wp_jmp32 op dst src (vcgWP prog Q n tgt) (vcgWP prog Q n (pc + 1))

private lemma getElem?_lt' {α : Type*} (a : Array α) {i : ℕ} {v : α}
    (h : a[i]? = some v) : i < a.size :=
  (Array.getElem?_eq_some_iff.mp h).elim fun hlt _ => hlt

private lemma vcg_pc_lt {prog : Program} {mapSize : ℕ}
    {callTypes : BitVec 32 → RegType} {pc : ℕ} {abs : AState}
    (hv : Verifies prog mapSize callTypes pc abs) : pc < prog.size := by
  cases verifier_progress prog mapSize callTypes pc abs hv with
  | intro _ hprog =>
    exact getElem?_lt' prog hprog

private lemma no_back_edge_ja {prog : Program} {pc : ℕ} {off : BitVec 16}
    (hnb : NoBackEdges prog) (hlt : pc < prog.size)
    (hprog : prog[pc]? = some (Instr.ja off)) :
    pc < ((pc : Int) + 1 + offset16ToInt off).toNat := by
  have h := hnb pc hlt
  simp only [hprog, isForwardJump] at h
  exact h

private lemma no_back_edge_jmp64 {prog : Program} {pc : ℕ}
    {op : JmpOp} {dst : Reg} {src : Src} {off : BitVec 16}
    (hnb : NoBackEdges prog) (hlt : pc < prog.size)
    (hprog : prog[pc]? = some (Instr.jmp64 op dst src off)) :
    pc < ((pc : Int) + 1 + offset16ToInt off).toNat := by
  have h := hnb pc hlt
  simp only [hprog, isForwardJump] at h
  exact h

private lemma no_back_edge_jmp32 {prog : Program} {pc : ℕ}
    {op : JmpOp} {dst : Reg} {src : Src} {off : BitVec 16}
    (hnb : NoBackEdges prog) (hlt : pc < prog.size)
    (hprog : prog[pc]? = some (Instr.jmp32 op dst src off)) :
    pc < ((pc : Int) + 1 + offset16ToInt off).toNat := by
  have h := hnb pc hlt
  simp only [hprog, isForwardJump] at h
  exact h

theorem vcg_soundness (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
    (Q : Assert) (n pc : ℕ) (abs : AState)
    (hn : n ≥ prog.size + 1 - pc)
    (hnb : NoBackEdges prog)
    (hv : Verifies prog mapSize callTypes pc abs) :
    HTriple prog pc (vcgWP prog Q n pc) Q := by
  induction n generalizing pc abs with
  | zero =>
      have hlt : pc < prog.size := vcg_pc_lt hv
      omega
  | succ k ih =>
      have hlt : pc < prog.size := vcg_pc_lt hv
      cases hv with
      | exit pc s hprog _ _ =>
          simp only [vcgWP, hprog]
          exact HTriple.exit pc Q hprog
      | alu64 pc s op dst src t hprog _ _ _ hrec =>
          simp only [vcgWP, hprog]
          exact HTriple.alu64 pc op dst src _ Q hprog (ih (pc + 1) _ (by omega) hrec)
      | alu32 pc s op dst src t hprog _ _ _ hrec =>
          simp only [vcgWP, hprog]
          exact HTriple.alu32 pc op dst src _ Q hprog (ih (pc + 1) _ (by omega) hrec)
      | neg64 pc s dst hprog _ hrec =>
          simp only [vcgWP, hprog]
          exact HTriple.neg64 pc dst _ Q hprog (ih (pc + 1) _ (by omega) hrec)
      | neg32 pc s dst hprog _ hrec =>
          simp only [vcgWP, hprog]
          exact HTriple.neg32 pc dst _ Q hprog (ih (pc + 1) _ (by omega) hrec)
      | endian pc s e sz dst hprog _ hrec =>
          simp only [vcgWP, hprog]
          exact HTriple.endian pc e sz dst _ Q hprog (ih (pc + 1) _ (by omega) hrec)
      | lddw pc s dst imm hprog hrec =>
          simp only [vcgWP, hprog]
          exact HTriple.lddw pc dst imm _ Q hprog (ih (pc + 2) _ (by omega) hrec)
      | load pc s sz dst src off hprog _ hrec =>
          simp only [vcgWP, hprog]
          exact HTriple.load pc sz dst src off _ Q hprog (ih (pc + 1) _ (by omega) hrec)
      | store pc s sz dst off src hprog _ _ hrec =>
          simp only [vcgWP, hprog]
          exact HTriple.store pc sz dst off src _ Q hprog (ih (pc + 1) _ (by omega) hrec)
      | atomic pc s sz op fetch dst src off hprog _ _ _ hrec =>
          simp only [vcgWP, hprog]
          exact HTriple.atomic pc sz op fetch dst src off _ Q hprog
            (ih (pc + 1) _ (by omega) hrec)
      | call pc s fid hprog _ _ _ _ _ _ hrec =>
          simp only [vcgWP, hprog]
          exact HTriple.call pc fid _ Q hprog (ih (pc + 1) _ (by omega) hrec)
      | ja pc s off pc' hprog hpc'_eq h0 hrec =>
          have hfwd : pc < pc'.toNat := by
            have := no_back_edge_ja hnb hlt hprog
            rwa [← hpc'_eq] at this
          simp only [vcgWP, hprog]
          rw [show ((pc : Int) + 1 + offset16ToInt off).toNat = pc'.toNat
              from by rw [hpc'_eq]]
          exact HTriple.ja pc off pc' _ Q hprog hpc'_eq h0 (ih pc'.toNat _ (by omega) hrec)
      | jmp64 pc s op dst src off pc' hprog _ _ hpc'_eq h0 hrec_t hrec_f =>
          have hfwd : pc < pc'.toNat := by
            have := no_back_edge_jmp64 hnb hlt hprog
            rwa [← hpc'_eq] at this
          simp only [vcgWP, hprog]
          rw [show ((pc : Int) + 1 + offset16ToInt off).toNat = pc'.toNat
              from by rw [hpc'_eq]]
          exact HTriple.jmp64 pc op dst src off pc' _ _ Q hprog hpc'_eq h0
            (ih pc'.toNat _ (by omega) hrec_t)
            (ih (pc + 1) _ (by omega) hrec_f)
      | jmp32 pc s op dst src off pc' hprog _ _ hpc'_eq h0 hrec_t hrec_f =>
          have hfwd : pc < pc'.toNat := by
            have := no_back_edge_jmp32 hnb hlt hprog
            rwa [← hpc'_eq] at this
          simp only [vcgWP, hprog]
          rw [show ((pc : Int) + 1 + offset16ToInt off).toNat = pc'.toNat
              from by rw [hpc'_eq]]
          exact HTriple.jmp32 pc op dst src off pc' _ _ Q hprog hpc'_eq h0
            (ih pc'.toNat _ (by omega) hrec_t)
            (ih (pc + 1) _ (by omega) hrec_f)

theorem wf_vcg (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
    (Q : Assert) (hwf : WellFormed prog mapSize callTypes) :
    HTriple prog 0 (vcgWP prog Q (prog.size + 1) 0) Q :=
  vcg_soundness prog mapSize callTypes Q (prog.size + 1) 0 initialAState
    (by omega) hwf.1 hwf.2.2

end Ebpf

import Ebpf.EbpfLogic
import Ebpf.EbpfVerifier
import Ebpf.VCG
import Ebpf.LogicSoundness

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

namespace Ebpf


private def filterAState : AState where
  regs := fun r => match r with
    | Reg.r1  => RegType.ptr_ctx
    | Reg.r10 => RegType.ptr_stack 0
    | _       => RegType.scalar
  stack := fun _ => false
  refcount := 0


def arpFilter : Program := #[
  Instr.load  Size.half Reg.r2 Reg.r1 12,
  Instr.alu64 AluOp.mov Reg.r0 (Src.imm 1),
  Instr.jmp64 JmpOp.jne Reg.r2 (Src.imm 0x0806) 1,
  Instr.exit,
  Instr.alu64 AluOp.mov Reg.r0 (Src.imm 0),
  Instr.exit
]

def arpPre : Assert :=
  fun rf h => rf Reg.r1 = 0 ∧ readHeap h 12 Size.half = some 0x0806

def arpPost : Assert := fun rf _ => rf Reg.r0 = 1

private lemma arpFilter_pc0 : arpFilter[0]? = some (Instr.load Size.half Reg.r2 Reg.r1 12) :=
  by decide
private lemma arpFilter_pc1 : arpFilter[1]? = some (Instr.alu64 AluOp.mov Reg.r0 (Src.imm 1)) :=
  by decide
private lemma arpFilter_pc2 :
    arpFilter[2]? = some (Instr.jmp64 JmpOp.jne Reg.r2 (Src.imm 0x0806) 1) := by decide
private lemma arpFilter_pc3 : arpFilter[3]? = some Instr.exit := by decide
private lemma arpFilter_pc4 : arpFilter[4]? = some (Instr.alu64 AluOp.mov Reg.r0 (Src.imm 0)) :=
  by decide
private lemma arpFilter_pc5 : arpFilter[5]? = some Instr.exit := by decide

private lemma arpFilter_noBackEdges : NoBackEdges arpFilter :=
  (noBackEdgesB_iff arpFilter).mpr (by decide)

private lemma arpFilter_verifies :
    Verifies arpFilter 0 (fun _ => RegType.scalar) 0 filterAState :=
  verifiesB_sound arpFilter 0 (fun _ => RegType.scalar) 0 filterAState (by decide)


private lemma arpFilter_vcg_triple :
    HTriple arpFilter 0 (vcgWP arpFilter arpPost (arpFilter.size + 1) 0) arpPost :=
  vcg_soundness arpFilter 0 (fun _ => RegType.scalar) arpPost
    (arpFilter.size + 1) 0 filterAState
    (by omega)
    arpFilter_noBackEdges
    arpFilter_verifies

private lemma arpPre_entails_VCG : arpPre ⊢ₐ vcgWP arpFilter arpPost (arpFilter.size + 1) 0 := by
  intro rf h ⟨hr1, hread⟩
  -- vcgWP reduces definitionally; unfold to explicit form
  change wp_load Size.half Reg.r2 Reg.r1 12
        (wp_alu64 AluOp.mov Reg.r0 (Src.imm 1)
          (wp_jmp64 JmpOp.jne Reg.r2 (Src.imm 0x0806)
            (wp_alu64 AluOp.mov Reg.r0 (Src.imm 0) arpPost)
            arpPost)) rf h
  simp only [wp_load]
  refine ⟨0x0806, ?haddr, ?hcont⟩
  · -- Address: r1 = 0, so r1 + signExtend 12 = 12
    have heq : rf Reg.r1 + BitVec.signExtend 64 (12 : BitVec 16) = 12 := by
      rw [hr1]; decide
    rw [heq]; exact hread
  · -- Continuation after loading 0x0806 into r2
    simp only [wp_alu64, wp_jmp64, evalAlu64, evalSrc, evalJmp64, arpPost, RegFile.set]
    constructor
    · -- Taken branch: jne 0x0806 0x0806 = false, so condition false → vacuous
      intro habs
      simp only [show Reg.r2 = Reg.r0 ↔ False from by decide,
                 if_false, if_true] at habs
      exact absurd habs (by decide)
    · -- Fallthrough: r0 = signExtend 1 = 1
      intro _
      simp only [if_true]
      decide

theorem arpFilter_correct : HTriple arpFilter 0 arpPre arpPost :=
  HTriple.consequence 0 _ arpPre arpPost arpPost
    arpPre_entails_VCG
    arpFilter_vcg_triple
    (fun _ _ h => h)


def tcpFilter : Program := #[
  Instr.load  Size.half Reg.r2 Reg.r1 12,
  Instr.jmp64 JmpOp.jne Reg.r2 (Src.imm 0x0800) 4,
  Instr.load  Size.byte Reg.r2 Reg.r1 23,
  Instr.jmp64 JmpOp.jne Reg.r2 (Src.imm 0x0006) 2,
  Instr.alu64 AluOp.mov Reg.r0 (Src.imm 1),
  Instr.exit,
  Instr.alu64 AluOp.mov Reg.r0 (Src.imm 0),
  Instr.exit
]

def tcpPre : Assert :=
  fun rf h => rf Reg.r1 = 0 ∧
              readHeap h 12 Size.half = some 0x0800 ∧
              readHeap h 23 Size.byte = some 0x06

def tcpPost : Assert := fun rf _ => rf Reg.r0 = 1

private lemma tcpFilter_pc0 : tcpFilter[0]? = some (Instr.load Size.half Reg.r2 Reg.r1 12) :=
  by decide
private lemma tcpFilter_pc1 :
    tcpFilter[1]? = some (Instr.jmp64 JmpOp.jne Reg.r2 (Src.imm 0x0800) 4) := by decide
private lemma tcpFilter_pc2 : tcpFilter[2]? = some (Instr.load Size.byte Reg.r2 Reg.r1 23) :=
  by decide
private lemma tcpFilter_pc3 :
    tcpFilter[3]? = some (Instr.jmp64 JmpOp.jne Reg.r2 (Src.imm 0x0006) 2) := by decide
private lemma tcpFilter_pc4 : tcpFilter[4]? = some (Instr.alu64 AluOp.mov Reg.r0 (Src.imm 1)) :=
  by decide
private lemma tcpFilter_pc5 : tcpFilter[5]? = some Instr.exit := by decide
private lemma tcpFilter_pc6 : tcpFilter[6]? = some (Instr.alu64 AluOp.mov Reg.r0 (Src.imm 0)) :=
  by decide
private lemma tcpFilter_pc7 : tcpFilter[7]? = some Instr.exit := by decide


private lemma tcpFilter_noBackEdges : NoBackEdges tcpFilter :=
  (noBackEdgesB_iff tcpFilter).mpr (by decide)

private lemma tcpFilter_verifies :
    Verifies tcpFilter 0 (fun _ => RegType.scalar) 0 filterAState :=
  verifiesB_sound tcpFilter 0 (fun _ => RegType.scalar) 0 filterAState (by decide)

private lemma tcpFilter_vcg_triple :
    HTriple tcpFilter 0 (vcgWP tcpFilter tcpPost (tcpFilter.size + 1) 0) tcpPost :=
  vcg_soundness tcpFilter 0 (fun _ => RegType.scalar) tcpPost
    (tcpFilter.size + 1) 0 filterAState
    (by omega)
    tcpFilter_noBackEdges
    tcpFilter_verifies


private abbrev tcpDropWP : Assert := wp_alu64 AluOp.mov Reg.r0 (Src.imm 0) tcpPost

private lemma tcpPre_entails_VCG : tcpPre ⊢ₐ vcgWP tcpFilter tcpPost (tcpFilter.size + 1) 0 := by
  intro rf h ⟨hr1, heth, hproto⟩
  change wp_load Size.half Reg.r2 Reg.r1 12
        (wp_jmp64 JmpOp.jne Reg.r2 (Src.imm 0x0800)
          tcpDropWP
          (wp_load Size.byte Reg.r2 Reg.r1 23
            (wp_jmp64 JmpOp.jne Reg.r2 (Src.imm 0x0006)
              tcpDropWP
              (wp_alu64 AluOp.mov Reg.r0 (Src.imm 1) tcpPost)))) rf h
  simp only [wp_load]
  refine ⟨0x0800, ?haddr12, ?hcont1⟩
  · have heq : rf Reg.r1 + BitVec.signExtend 64 (12 : BitVec 16) = 12 := by
      rw [hr1]; decide
    rw [heq]; exact heth
  · -- After loading 0x0800 into r2: jne(r2, 0x0800) = false → fall through
    simp only [wp_jmp64, evalJmp64, evalSrc, tcpDropWP, wp_alu64, evalAlu64, RegFile.set]
    simp only [if_true]
    constructor
    · -- Taken branch: 0x0800 ≠ 0x0800 is false → vacuous
      intro habs; exact absurd habs (by decide)
    · -- Fallthrough: proceed to check IP protocol
      intro _
      simp only [wp_load]
      -- r1 is unchanged after loading into r2
      have hr1' : rf.set Reg.r2 (0x0800 : BitVec 64) Reg.r1 = 0 := by
        simp [RegFile.set, show Reg.r1 ≠ Reg.r2 from by decide, hr1]
      -- Witness for the IP protocol load: 0x06 (TCP)
      refine ⟨0x06, ?haddr23, ?hcont2⟩
      · have heq : rf.set Reg.r2 (0x0800 : BitVec 64) Reg.r1
              + BitVec.signExtend 64 (23 : BitVec 16) = 23 := by
          rw [hr1']; decide
        rw [heq]; exact hproto
      · -- After loading 0x0006: jne(r2, 0x0006) = false → accept
        simp only [wp_jmp64, evalJmp64, evalSrc, wp_alu64, evalAlu64, tcpPost, RegFile.set]
        simp only [if_true]
        constructor
        · intro habs; exact absurd habs (by decide)
        · intro _; decide

theorem tcpFilter_correct : HTriple tcpFilter 0 tcpPre tcpPost :=
  HTriple.consequence 0 _ tcpPre tcpPost tcpPost
    tcpPre_entails_VCG
    tcpFilter_vcg_triple
    (fun _ _ h => h)


theorem arpFilter_sem_sound
    (oracle : CallOracle) (hok : OracleOk oracle)
    (h1 h2 : Heap) (s sf : State) (fuel : ℕ)
    (hpc : s.pc = 0) (hP : arpPre s.regs h1)
    (hcon : Heap.Consistent (Heap.union h1 h2) s.mem)
    (hdisj : Heap.Disjoint h1 h2)
    (hhs : OracleHeapSafe oracle (Heap.union h1 h2))
    (hint : interp arpFilter oracle s fuel = some sf) :
    ∃ hf1 : Heap,
      arpPost sf.regs hf1 ∧
      Heap.Consistent (Heap.union hf1 h2) sf.mem ∧
      Heap.Disjoint hf1 h2 :=
  sem_triple_interp_sound arpFilter 0 arpPre arpPost
    (htriple_sound arpFilter_correct)
    oracle hok h1 h2 s sf fuel hpc hP hcon hdisj hhs hint

theorem tcpFilter_sem_sound
    (oracle : CallOracle) (hok : OracleOk oracle)
    (h1 h2 : Heap) (s sf : State) (fuel : ℕ)
    (hpc : s.pc = 0) (hP : tcpPre s.regs h1)
    (hcon : Heap.Consistent (Heap.union h1 h2) s.mem)
    (hdisj : Heap.Disjoint h1 h2)
    (hhs : OracleHeapSafe oracle (Heap.union h1 h2))
    (hint : interp tcpFilter oracle s fuel = some sf) :
    ∃ hf1 : Heap,
      tcpPost sf.regs hf1 ∧
      Heap.Consistent (Heap.union hf1 h2) sf.mem ∧
      Heap.Disjoint hf1 h2 :=
  sem_triple_interp_sound tcpFilter 0 tcpPre tcpPost
    (htriple_sound tcpFilter_correct)
    oracle hok h1 h2 s sf fuel hpc hP hcon hdisj hhs hint

end Ebpf

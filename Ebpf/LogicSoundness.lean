import Ebpf.EbpfLogic
import Ebpf.Semantics
import Ebpf.VCG
import Ebpf.Interp

set_option linter.style.emptyLine false

namespace Ebpf


/- Semantic Soundness of the Separation Logic -/


private def isCallStep {prog : Program} {s sf : State} (_ : Step prog s sf) : Prop :=
  ∃ fid : BitVec 32, prog[s.pc]? = some (Instr.call fid)

private inductive HeapSafe (prog : Program) (h : Heap) :
    ∀ {s sf : State}, Steps prog s sf → Prop where
  | refl : ∀ (s : State), HeapSafe prog h (Steps.refl s)
  | step : ∀ {s s'' sf' : State} (hstep : Step prog s s'') (hsteps' : Steps prog s'' sf'),
      (isCallStep hstep → ∀ a, s''.mem a ≠ s.mem a → h a = none) →
      HeapSafe prog h hsteps' →
      HeapSafe prog h (Steps.step s s'' sf' hstep hsteps')

/- Frame-aware semantic triple -/

def SemTriple (prog : Program) (pc : ℕ) (P Q : Assert) : Prop :=
  ∀ (s : State) (h1 h2 : Heap),
    s.pc = pc →
    P s.regs h1 →
    Heap.Consistent (Heap.union h1 h2) s.mem →
    Heap.Disjoint h1 h2 →
    ∀ (sf : State) (hsteps : Steps prog s sf),
      prog[sf.pc]? = some Instr.exit →
      HeapSafe prog (Heap.union h1 h2) hsteps →
      ∃ hf1 : Heap,
        Q sf.regs hf1 ∧
        Heap.Consistent (Heap.union hf1 h2) sf.mem ∧
        Heap.Disjoint hf1 h2

/- Auxiliary: exit states are stuck -/

lemma exit_no_step (prog : Program) (s : State)
    (h : prog[s.pc]? = some Instr.exit) : ∀ s', ¬ Step prog s s' := by
  intro s' hstep
  cases hstep <;> simp_all

lemma steps_from_exit (prog : Program) (s sf : State)
    (hexit : prog[s.pc]? = some Instr.exit)
    (hsteps : Steps prog s sf) : sf = s := by
  cases hsteps with
  | refl => rfl
  | step s s'' sf' hstep _ => exact absurd hstep (exit_no_step prog s hexit s'')

/- Heap union helpers -/

private lemma heap_union_assoc (h1 h2 h3 : Heap) :
    Heap.union (Heap.union h1 h2) h3 = Heap.union h1 (Heap.union h2 h3) := by
  funext a
  simp only [Heap.union]
  cases h1 a <;> simp [Option.orElse]

private lemma heap_union_none_iff (h1 h2 : Heap) (a : BitVec 64) :
    Heap.union h1 h2 a = none ↔ h1 a = none ∧ h2 a = none := by
  simp only [Heap.union]
  cases h1 a <;> simp [Option.orElse]

private lemma disjoint_union_left {h1 h2 h3 : Heap}
    (h : Heap.Disjoint h1 (Heap.union h2 h3)) : Heap.Disjoint h1 h2 := by
  intro a
  rcases h a with hn | hun
  · left; assumption
  · exact Or.inr ((heap_union_none_iff h2 h3 a).mp hun).1

private lemma disjoint_assoc_right {h1 hR h2 : Heap}
    (hdisj12 : Heap.Disjoint h1 hR)
    (hdisj : Heap.Disjoint (Heap.union h1 hR) h2) :
    Heap.Disjoint h1 (Heap.union hR h2) := by
  intro a
  rcases hdisj12 a with hn1 | hnR
  · left; assumption
  · -- hR a = none, so (hR ∪ h2) a = h2 a
    have hRh2 : Heap.union hR h2 a = h2 a := by simp [Heap.union, hnR, Option.orElse]
    rw [hRh2]
    rcases hdisj a with hun | hn2
    · exact Or.inl ((heap_union_none_iff h1 hR a).mp hun).1
    · right; assumption

private lemma disjoint_union_of_disjoint_union {hf1 hR h1 h2 : Heap}
    (hdisjf : Heap.Disjoint hf1 (Heap.union hR h2))
    (hdisj : Heap.Disjoint (Heap.union h1 hR) h2) :
    Heap.Disjoint (Heap.union hf1 hR) h2 := by
  intro a
  rcases hdisj a with hun | hn2
  · -- (h1 ∪ hR) a = none  →  hR a = none
    have hnR : hR a = none := ((heap_union_none_iff h1 hR a).mp hun).2
    -- (hR ∪ h2) a ≠ none if h2 a ≠ none — use hdisjf to get hf1 a = none
    -- (hf1 ∪ hR) a = hf1 a.orElse (fun _ => none) = hf1 a
    have hfR : Heap.union hf1 hR a = hf1 a := by
      simp only [Heap.union, hnR]; cases hf1 a <;> rfl
    rw [hfR]
    rcases hdisjf a with hnf | hunRh2
    · left; assumption
    · exact Or.inr ((heap_union_none_iff hR h2 a).mp hunRh2).2
  · right; assumption

/- HeapSafe helper lemmas -/

private def heapSafe_head {prog : Program} {h : Heap}
    {s s1 sf : State} {hstep : Step prog s s1} {hsteps' : Steps prog s1 sf}
    (hsafe : HeapSafe prog h (Steps.step s s1 sf hstep hsteps')) :
    (isCallStep hstep → ∀ a, s1.mem a ≠ s.mem a → h a = none) :=
  match hsafe with
  | .step _ _ hhead _ => hhead

/-- Extract the tail of a HeapSafe sequence. -/
private def heapSafe_tail {prog : Program} {h : Heap}
    {s s1 sf : State} {hstep : Step prog s s1} {hsteps' : Steps prog s1 sf}
    (hsafe : HeapSafe prog h (Steps.step s s1 sf hstep hsteps')) :
    HeapSafe prog h hsteps' :=
  match hsafe with
  | .step _ _ _ htail => htail

/-- HeapSafe is preserved under point-wise-none-equivalent heaps. -/
private def heapSafe_congr {prog : Program} {h h' : Heap}
    (heq : ∀ a, h a = none ↔ h' a = none) :
    ∀ {s sf : State} {hsteps : Steps prog s sf},
    HeapSafe prog h hsteps → HeapSafe prog h' hsteps
  | _, _, _, .refl s => HeapSafe.refl s
  | _, _, _, .step hstep hsteps' hhead htail =>
      HeapSafe.step hstep hsteps'
        (fun hcall a hmod => (heq a).mp (hhead hcall a hmod))
        (heapSafe_congr heq htail)

private lemma writeHeap_none_iff (h : Heap) (addr : BitVec 64) (sz : Size) (val : BitVec 64)
    (hown : readHeap h addr sz ≠ none) (a : BitVec 64) :
    writeHeap h addr sz val a = none ↔ h a = none := by
  have own0 : h addr ≠ none := by
    intro heq; exact hown (by simp only [readHeap]; cases sz <;> simp [heq])
  cases sz with
  | byte =>
      simp only [writeHeap]
      by_cases ha : a = addr
      · subst ha; rw [if_pos rfl]
        constructor <;> intro hn <;> contradiction
      · simp only [if_neg ha]
  | half =>
      have own1 : h (addr + 1) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
          simp only [hb0, Option.bind_some, heq, Option.bind_none] at hown
          contradiction
      simp only [writeHeap]
      by_cases ha : a = addr
      · subst ha; rw [if_pos rfl]
        constructor <;> intro hn <;> contradiction
      · by_cases ha1 : a = addr + 1
        · subst ha1; simp only [if_neg ha]
          constructor <;> intro hn <;> contradiction
        · simp only [if_neg ha, if_neg ha1]
  | word =>
      have own1 : h (addr + 1) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
          simp only [hb0, Option.bind_some, heq, Option.bind_none] at hown
          contradiction
      have own2 : h (addr + 2) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h (addr + 1) with
        | none =>
          simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
          contradiction
        | some _ =>
          simp only [hb0, Option.bind_some, hb1, Option.bind_some, heq, Option.bind_none] at hown
          contradiction
      have own3 : h (addr + 3) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h (addr + 1) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb2 : h (addr + 2) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none] at hown
            contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, heq,
              Option.bind_none] at hown
            contradiction
      simp only [writeHeap]
      by_cases ha : a = addr
      · subst ha; rw [if_pos rfl]
        constructor <;> intro hn <;> contradiction
      · by_cases ha1 : a = addr + 1
        · subst ha1; simp only [if_neg ha]
          constructor <;> intro hn <;> contradiction
        · by_cases ha2 : a = addr + 2
          · subst ha2; simp only [if_neg ha, if_neg ha1]
            constructor <;> intro hn <;> contradiction
          · by_cases ha3 : a = addr + 3
            · subst ha3; simp only [if_neg ha, if_neg ha1, if_neg ha2]
              constructor <;> intro hn <;> contradiction
            · simp only [if_neg ha, if_neg ha1, if_neg ha2, if_neg ha3]
  | dword =>
      have own1 : h (addr + 1) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
          simp only [hb0, Option.bind_some, heq, Option.bind_none] at hown
          contradiction
      have own2 : h (addr + 2) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h (addr + 1) with
        | none =>
          simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
          contradiction
        | some _ =>
          simp only [hb0, Option.bind_some, hb1, Option.bind_some, heq, Option.bind_none] at hown
          contradiction
      have own3 : h (addr + 3) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h (addr + 1) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb2 : h (addr + 2) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none] at hown
            contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, heq,
              Option.bind_none] at hown
            contradiction
      have own4 : h (addr + 4) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h (addr + 1) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb2 : h (addr + 2) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb3 : h (addr + 3) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_none] at hown
            contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, heq, Option.bind_none] at hown
            contradiction
      have own5 : h (addr + 5) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h (addr + 1) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb2 : h (addr + 2) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb3 : h (addr + 3) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb4 : h (addr + 4) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_none] at hown
            contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_some, heq, Option.bind_none] at hown
            contradiction
      have own6 : h (addr + 6) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h (addr + 1) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb2 : h (addr + 2) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb3 : h (addr + 3) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb4 : h (addr + 4) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb5 : h (addr + 5) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_none] at hown
            contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_some, heq,
              Option.bind_none] at hown
            contradiction
      have own7 : h (addr + 7) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h (addr + 1) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb2 : h (addr + 2) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb3 : h (addr + 3) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb4 : h (addr + 4) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb5 : h (addr + 5) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb6 : h (addr + 6) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_some, hb6,
              Option.bind_none] at hown
            contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_some, hb6, heq,
              Option.bind_some, Option.bind_none] at hown
            contradiction
      simp only [writeHeap]
      by_cases ha : a = addr
      · subst ha; rw [if_pos rfl]
        constructor <;> intro hn <;> contradiction
      · by_cases ha1 : a = addr + 1
        · subst ha1; simp only [if_neg ha]
          constructor <;> intro hn <;> contradiction
        · by_cases ha2 : a = addr + 2
          · subst ha2; simp only [if_neg ha, if_neg ha1]
            constructor <;> intro hn <;> contradiction
          · by_cases ha3 : a = addr + 3
            · subst ha3; simp only [if_neg ha, if_neg ha1, if_neg ha2]
              constructor <;> intro hn <;> contradiction
            · by_cases ha4 : a = addr + 4
              · subst ha4; simp only [if_neg ha, if_neg ha1, if_neg ha2, if_neg ha3]
                constructor <;> intro hn <;> contradiction
              · by_cases ha5 : a = addr + 5
                · subst ha5
                  simp only [if_neg ha, if_neg ha1, if_neg ha2, if_neg ha3, if_neg ha4]
                  constructor <;> intro hn <;> contradiction
                · by_cases ha6 : a = addr + 6
                  · subst ha6
                    simp only [if_neg ha, if_neg ha1, if_neg ha2, if_neg ha3,
                               if_neg ha4, if_neg ha5]
                    constructor <;> intro hn <;> contradiction
                  · by_cases ha7 : a = addr + 7
                    · subst ha7
                      simp only [if_neg ha, if_neg ha1, if_neg ha2, if_neg ha3,
                                 if_neg ha4, if_neg ha5, if_neg ha6]
                      constructor <;> intro hn <;> contradiction
                    · simp only [if_neg ha, if_neg ha1, if_neg ha2, if_neg ha3,
                                 if_neg ha4, if_neg ha5, if_neg ha6, if_neg ha7]

private lemma heapSafe_writeHeap {prog : Program} {h h2 : Heap}
    {addr : BitVec 64} {sz : Size} {val : BitVec 64}
    (hown : readHeap h addr sz ≠ none)
    {s sf : State} {hsteps : Steps prog s sf}
    (hsafe : HeapSafe prog (Heap.union h h2) hsteps) :
    HeapSafe prog (Heap.union (writeHeap h addr sz val) h2) hsteps :=
  heapSafe_congr (fun a => by
    simp only [heap_union_none_iff]
    constructor
    · intro ⟨hn1, hn2⟩
      constructor
      · exact (writeHeap_none_iff h addr sz val hown a).mpr hn1
      · exact hn2
    · intro ⟨hn1, hn2⟩
      constructor
      · exact (writeHeap_none_iff h addr sz val hown a).mp hn1
      · exact hn2)
    hsafe

/- Heap–memory bridge lemmas -/

lemma consistent_read {h : Heap} {mem : Memory} {a : BitVec 64} {b : BitVec 8}
    (hcons : Heap.Consistent h mem) (ha : h a = some b) : mem a = b :=
  hcons a b ha

lemma consistent_union_left {h1 h2 : Heap} {mem : Memory}
    (hcons : Heap.Consistent (Heap.union h1 h2) mem) :
    Heap.Consistent h1 mem := by
  intro a b ha
  apply hcons
  simp [Heap.union, ha]

lemma consistent_union_right {h1 h2 : Heap} {mem : Memory}
    (hdisj : Heap.Disjoint h1 h2)
    (hcons : Heap.Consistent (Heap.union h1 h2) mem) :
    Heap.Consistent h2 mem := by
  intro a b ha
  apply hcons
  simp only [Heap.union]
  rcases hdisj a with h | h
  · simp [h, ha]   -- h1 a = none  →  (none).orElse _ = h2 a = some b
  · simp [h] at ha -- h2 a = none  →  contradicts ha

lemma consistent_union_of_consistent {h1 h2 : Heap} {mem : Memory}
    (_hdisj : Heap.Disjoint h1 h2)
    (hc1 : Heap.Consistent h1 mem)
    (hc2 : Heap.Consistent h2 mem) :
    Heap.Consistent (Heap.union h1 h2) mem := by
  intro a b hab
  simp only [Heap.union] at hab
  cases h : h1 a with
  | none   => simp only [h, Option.orElse_none] at hab; apply hc2; assumption
  | some x =>
      simp only [h, Option.orElse_some, Option.some.injEq] at hab
      subst hab; apply hc1; assumption

lemma consistent_empty (mem : Memory) : Heap.Consistent Heap.empty mem := by
  intro a b ha; simp [Heap.empty] at ha

lemma consistent_readHeap {h : Heap} {mem : Memory}
    (hcons : Heap.Consistent h mem)
    {addr : BitVec 64} {sz : Size} {v : BitVec 64}
    (hread : readHeap h addr sz = some v) :
    readMem mem addr sz = v := by
  cases sz with
  | byte =>
      simp only [readHeap, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hread
      obtain ⟨b, hb, hv⟩ := hread
      simp only [readMem, hcons addr b hb]; exact hv
  | half =>
      simp only [readHeap, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hread
      obtain ⟨b0, hb0, b1, hb1, hv⟩ := hread
      simp only [readMem, hcons addr b0 hb0, hcons (addr+1) b1 hb1]; exact hv
  | word =>
      simp only [readHeap, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hread
      obtain ⟨b0, hb0, b1, hb1, b2, hb2, b3, hb3, hv⟩ := hread
      simp only [readMem, hcons addr b0 hb0, hcons (addr+1) b1 hb1,
                 hcons (addr+2) b2 hb2, hcons (addr+3) b3 hb3]; exact hv
  | dword =>
      simp only [readHeap, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hread
      obtain ⟨b0, hb0, b1, hb1, b2, hb2, b3, hb3,
               b4, hb4, b5, hb5, b6, hb6, b7, hb7, hv⟩ := hread
      simp only [readMem, hcons addr b0 hb0, hcons (addr+1) b1 hb1,
                 hcons (addr+2) b2 hb2, hcons (addr+3) b3 hb3,
                 hcons (addr+4) b4 hb4, hcons (addr+5) b5 hb5,
                 hcons (addr+6) b6 hb6, hcons (addr+7) b7 hb7]; exact hv

lemma consistent_writeHeap {h : Heap} {mem : Memory}
    (hcons : Heap.Consistent h mem)
    {addr : BitVec 64} {sz : Size} {val : BitVec 64}
    (hown : readHeap h addr sz ≠ none) :
    Heap.Consistent (writeHeap h addr sz val) (writeMem mem addr val sz) := by
  intro a b ha
  cases sz with
  | byte =>
      simp only [writeHeap] at ha; simp only [writeMem]
      by_cases h1 : a = addr
      · simp only [if_pos h1, Option.some.injEq] at ha
        simp only [if_pos h1]; exact ha
      · simp only [if_neg h1] at ha; simp only [if_neg h1]; exact hcons a b ha
  | half =>
      simp only [writeHeap] at ha; simp only [writeMem]
      by_cases h1 : a = addr
      · simp only [if_pos h1, Option.some.injEq] at ha
        simp only [if_pos h1]; exact ha
      · by_cases h2 : a = addr + 1
        · simp only [if_neg h1, if_pos h2, Option.some.injEq] at ha
          simp only [if_neg h1, if_pos h2]; exact ha
        · simp only [if_neg h1, if_neg h2] at ha
          simp only [if_neg h1, if_neg h2]; exact hcons a b ha
  | word =>
      simp only [writeHeap] at ha; simp only [writeMem]
      by_cases h1 : a = addr
      · simp only [if_pos h1, Option.some.injEq] at ha
        simp only [if_pos h1]; exact ha
      · by_cases h2 : a = addr + 1
        · simp only [if_neg h1, if_pos h2, Option.some.injEq] at ha
          simp only [if_neg h1, if_pos h2]; exact ha
        · by_cases h3 : a = addr + 2
          · simp only [if_neg h1, if_neg h2, if_pos h3, Option.some.injEq] at ha
            simp only [if_neg h1, if_neg h2, if_pos h3]; exact ha
          · by_cases h4 : a = addr + 3
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4, Option.some.injEq] at ha
              simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; exact ha
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4] at ha
              simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4]; exact hcons a b ha
  | dword =>
      simp only [writeHeap] at ha; simp only [writeMem]
      by_cases h1 : a = addr
      · simp only [if_pos h1, Option.some.injEq] at ha
        simp only [if_pos h1]; exact ha
      · by_cases h2 : a = addr + 1
        · simp only [if_neg h1, if_pos h2, Option.some.injEq] at ha
          simp only [if_neg h1, if_pos h2]; exact ha
        · by_cases h3 : a = addr + 2
          · simp only [if_neg h1, if_neg h2, if_pos h3, Option.some.injEq] at ha
            simp only [if_neg h1, if_neg h2, if_pos h3]; exact ha
          · by_cases h4 : a = addr + 3
            · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4, Option.some.injEq] at ha
              simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; exact ha
            · by_cases h5 : a = addr + 4
              · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                           if_pos h5, Option.some.injEq] at ha
                simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; exact ha
              · by_cases h6 : a = addr + 5
                · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                             if_neg h5, if_pos h6, Option.some.injEq] at ha
                  simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                             if_neg h5, if_pos h6]; exact ha
                · by_cases h7 : a = addr + 6
                  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                               if_neg h5, if_neg h6, if_pos h7, Option.some.injEq] at ha
                    simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                               if_neg h5, if_neg h6, if_pos h7]; exact ha
                  · by_cases h8 : a = addr + 7
                    · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                                 if_neg h5, if_neg h6, if_neg h7, if_pos h8,
                                 Option.some.injEq] at ha
                      simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                                 if_neg h5, if_neg h6, if_neg h7, if_pos h8]; exact ha
                    · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                                 if_neg h5, if_neg h6, if_neg h7, if_neg h8] at ha
                      simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                                 if_neg h5, if_neg h6, if_neg h7, if_neg h8]
                      exact hcons a b ha

lemma disjoint_writeHeap {h1 h2 : Heap}
    (hdisj : Heap.Disjoint h1 h2)
    {addr : BitVec 64} {sz : Size} {val : BitVec 64}
    (hown : readHeap h1 addr sz ≠ none) :
    Heap.Disjoint (writeHeap h1 addr sz val) h2 := by
  have owned_h2_none : ∀ x, h1 x ≠ none → h2 x = none :=
    fun x hx => (hdisj x).resolve_left hx
  have own0 : h1 addr ≠ none := by
    intro heq; exact hown (by simp only [readHeap]; cases sz <;> simp [heq])
  intro a
  cases sz with
  | byte =>
      simp only [writeHeap]
      by_cases ha : a = addr
      · rw [ha]; exact Or.inr (owned_h2_none addr own0)
      · simp only [if_neg ha]; exact hdisj a
  | half =>
      have own1 : h1 (addr + 1) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h1 addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, heq, Option.bind_none] at hown
            contradiction
      simp only [writeHeap]
      by_cases ha : a = addr
      · rw [ha]; exact Or.inr (owned_h2_none addr own0)
      · by_cases ha1 : a = addr + 1
        · rw [ha1]; exact Or.inr (owned_h2_none (addr + 1) own1)
        · simp only [if_neg ha, if_neg ha1]; exact hdisj a
  | word =>
      have own1 : h1 (addr + 1) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h1 addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, heq, Option.bind_none] at hown
            contradiction
      have own2 : h1 (addr + 2) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h1 addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h1 (addr + 1) with
        | none =>
          simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
          contradiction
        | some _ =>
          simp only [hb0, Option.bind_some, hb1, Option.bind_some, heq, Option.bind_none] at hown
          contradiction
      have own3 : h1 (addr + 3) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h1 addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h1 (addr + 1) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb2 : h1 (addr + 2) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none] at hown
            contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, heq,
              Option.bind_none] at hown
            contradiction
      simp only [writeHeap]
      by_cases ha : a = addr
      · rw [ha]; exact Or.inr (owned_h2_none addr own0)
      · by_cases ha1 : a = addr + 1
        · rw [ha1]; exact Or.inr (owned_h2_none (addr + 1) own1)
        · by_cases ha2 : a = addr + 2
          · rw [ha2]; exact Or.inr (owned_h2_none (addr + 2) own2)
          · by_cases ha3 : a = addr + 3
            · rw [ha3]; exact Or.inr (owned_h2_none (addr + 3) own3)
            · simp only [if_neg ha, if_neg ha1, if_neg ha2, if_neg ha3]; exact hdisj a
  | dword =>
      have own1 : h1 (addr + 1) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h1 addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, heq, Option.bind_none] at hown
            contradiction
      have own2 : h1 (addr + 2) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h1 addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h1 (addr + 1) with
        | none =>
          simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
          contradiction
        | some _ =>
          simp only [hb0, Option.bind_some, hb1, Option.bind_some, heq, Option.bind_none] at hown
          contradiction
      have own3 : h1 (addr + 3) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h1 addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h1 (addr + 1) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb2 : h1 (addr + 2) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none] at hown
            contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, heq,
              Option.bind_none] at hown
            contradiction
      have own4 : h1 (addr + 4) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h1 addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h1 (addr + 1) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb2 : h1 (addr + 2) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb3 : h1 (addr + 3) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_none] at hown
            contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, heq, Option.bind_none] at hown
            contradiction
      have own5 : h1 (addr + 5) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h1 addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h1 (addr + 1) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb2 : h1 (addr + 2) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb3 : h1 (addr + 3) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb4 : h1 (addr + 4) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_none] at hown
            contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_some, heq, Option.bind_none] at hown
            contradiction
      have own6 : h1 (addr + 6) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h1 addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h1 (addr + 1) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb2 : h1 (addr + 2) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb3 : h1 (addr + 3) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb4 : h1 (addr + 4) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb5 : h1 (addr + 5) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_none] at hown
            contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_some, heq,
              Option.bind_none] at hown
            contradiction
      have own7 : h1 (addr + 7) ≠ none := by
        intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
        cases hb0 : h1 addr with
        | none => simp only [hb0, Option.bind_none] at hown; contradiction
        | some _ =>
        cases hb1 : h1 (addr + 1) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb2 : h1 (addr + 2) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb3 : h1 (addr + 3) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb4 : h1 (addr + 4) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb5 : h1 (addr + 5) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_none] at hown
            contradiction
        | some _ =>
        cases hb6 : h1 (addr + 6) with
        | none =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_some, hb6,
              Option.bind_none] at hown
            contradiction
        | some _ =>
            simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
              Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_some, hb6, heq,
              Option.bind_some, Option.bind_none] at hown
            contradiction
      simp only [writeHeap]
      by_cases ha : a = addr
      · rw [ha]; exact Or.inr (owned_h2_none addr own0)
      · by_cases ha1 : a = addr + 1
        · rw [ha1]; exact Or.inr (owned_h2_none (addr + 1) own1)
        · by_cases ha2 : a = addr + 2
          · rw [ha2]; exact Or.inr (owned_h2_none (addr + 2) own2)
          · by_cases ha3 : a = addr + 3
            · rw [ha3]; exact Or.inr (owned_h2_none (addr + 3) own3)
            · by_cases ha4 : a = addr + 4
              · rw [ha4]; exact Or.inr (owned_h2_none (addr + 4) own4)
              · by_cases ha5 : a = addr + 5
                · rw [ha5]; exact Or.inr (owned_h2_none (addr + 5) own5)
                · by_cases ha6 : a = addr + 6
                  · rw [ha6]; exact Or.inr (owned_h2_none (addr + 6) own6)
                  · by_cases ha7 : a = addr + 7
                    · rw [ha7]; exact Or.inr (owned_h2_none (addr + 7) own7)
                    · simp only [if_neg ha, if_neg ha1, if_neg ha2, if_neg ha3,
                                 if_neg ha4, if_neg ha5, if_neg ha6, if_neg ha7]
                      exact hdisj a

lemma consistent_union_writeHeap {h1 h2 : Heap} {mem : Memory}
    (hdisj : Heap.Disjoint h1 h2)
    (hcons : Heap.Consistent (Heap.union h1 h2) mem)
    {addr : BitVec 64} {sz : Size} {val : BitVec 64}
    (hown : readHeap h1 addr sz ≠ none) :
    Heap.Consistent (Heap.union (writeHeap h1 addr sz val) h2)
                    (writeMem mem addr val sz) := by
  have hc1  : Heap.Consistent h1 mem := consistent_union_left hcons
  have hc2  : Heap.Consistent h2 mem := consistent_union_right hdisj hcons
  have hdisj' : Heap.Disjoint (writeHeap h1 addr sz val) h2 := disjoint_writeHeap hdisj hown
  have hc1' : Heap.Consistent (writeHeap h1 addr sz val) (writeMem mem addr val sz) :=
    consistent_writeHeap hc1 hown
  have hc2' : Heap.Consistent h2 (writeMem mem addr val sz) := by
    intro a b ha
    have h1none : h1 a = none := (hdisj a).resolve_right (fun h => by simp [h] at ha)
    have not_in_chunk : ∀ x, h1 x ≠ none → h2 x = none :=
      fun x hx => (hdisj x).resolve_left hx
    have own0 : h1 addr ≠ none := by
      intro heq; exact hown (by simp only [readHeap]; cases sz <;> simp [heq])
    cases sz with
    | byte =>
        simp only [writeMem]
        by_cases heq : a = addr
        · exact absurd (not_in_chunk addr own0) (by subst heq; simp [ha])
        · simp only [if_neg heq]; apply hc2; assumption
    | half =>
        have own1 : h1 (addr + 1) ≠ none := by
          intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
          cases hb0 : h1 addr with
          | none => simp only [hb0, Option.bind_none] at hown; contradiction
          | some _ =>
              simp only [hb0, Option.bind_some, heq, Option.bind_none] at hown
              contradiction
        simp only [writeMem]
        by_cases heq : a = addr
        · exact absurd (not_in_chunk addr own0) (by subst heq; simp [ha])
        · by_cases heq1 : a = addr + 1
          · have h := not_in_chunk _ own1; rw [← heq1] at h; exact absurd ha (by simp [h])
          · simp only [if_neg heq, if_neg heq1]; apply hc2; assumption
    | word =>
        have own1 : h1 (addr + 1) ≠ none := by
          intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
          cases hb0 : h1 addr with
          | none => simp only [hb0, Option.bind_none] at hown; contradiction
          | some _ =>
              simp only [hb0, Option.bind_some, heq, Option.bind_none] at hown
              contradiction
        have own2 : h1 (addr + 2) ≠ none := by
          intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
          cases hb0 : h1 addr with
          | none => simp only [hb0, Option.bind_none] at hown; contradiction
          | some _ =>
          cases hb1 : h1 (addr + 1) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
              contradiction
          | some _ =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, heq, Option.bind_none,
                ] at hown
              contradiction
        have own3 : h1 (addr + 3) ≠ none := by
          intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
          cases hb0 : h1 addr with
          | none => simp only [hb0, Option.bind_none] at hown; contradiction
          | some _ =>
          cases hb1 : h1 (addr + 1) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
              contradiction
          | some _ =>
          cases hb2 : h1 (addr + 2) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none,
                ] at hown
              contradiction
          | some _ =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, heq,
                Option.bind_none] at hown
              contradiction
        simp only [writeMem]
        by_cases heq : a = addr
        · exact absurd (not_in_chunk addr own0) (by subst heq; simp [ha])
        · by_cases heq1 : a = addr + 1
          · have h := not_in_chunk _ own1; rw [← heq1] at h; exact absurd ha (by simp [h])
          · by_cases heq2 : a = addr + 2
            · have h := not_in_chunk _ own2; rw [← heq2] at h; exact absurd ha (by simp [h])
            · by_cases heq3 : a = addr + 3
              · have h := not_in_chunk _ own3; rw [← heq3] at h; exact absurd ha (by simp [h])
              · simp only [if_neg heq, if_neg heq1, if_neg heq2, if_neg heq3]
                apply hc2; assumption
    | dword =>
        have own1 : h1 (addr + 1) ≠ none := by
          intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
          cases hb0 : h1 addr with
          | none => simp only [hb0, Option.bind_none] at hown; contradiction
          | some _ =>
              simp only [hb0, Option.bind_some, heq, Option.bind_none] at hown
              contradiction
        have own2 : h1 (addr + 2) ≠ none := by
          intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
          cases hb0 : h1 addr with
          | none => simp only [hb0, Option.bind_none] at hown; contradiction
          | some _ =>
          cases hb1 : h1 (addr + 1) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
              contradiction
          | some _ =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, heq, Option.bind_none,
                ] at hown
              contradiction
        have own3 : h1 (addr + 3) ≠ none := by
          intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
          cases hb0 : h1 addr with
          | none => simp only [hb0, Option.bind_none] at hown; contradiction
          | some _ =>
          cases hb1 : h1 (addr + 1) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
              contradiction
          | some _ =>
          cases hb2 : h1 (addr + 2) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none,
                ] at hown
              contradiction
          | some _ =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, heq,
                Option.bind_none] at hown
              contradiction
        have own4 : h1 (addr + 4) ≠ none := by
          intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
          cases hb0 : h1 addr with
          | none => simp only [hb0, Option.bind_none] at hown; contradiction
          | some _ =>
          cases hb1 : h1 (addr + 1) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
              contradiction
          | some _ =>
          cases hb2 : h1 (addr + 2) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none,
                ] at hown
              contradiction
          | some _ =>
          cases hb3 : h1 (addr + 3) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_none] at hown
              contradiction
          | some _ =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_some, heq, Option.bind_none] at hown
              contradiction
        have own5 : h1 (addr + 5) ≠ none := by
          intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
          cases hb0 : h1 addr with
          | none => simp only [hb0, Option.bind_none] at hown; contradiction
          | some _ =>
          cases hb1 : h1 (addr + 1) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
              contradiction
          | some _ =>
          cases hb2 : h1 (addr + 2) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none,
                ] at hown
              contradiction
          | some _ =>
          cases hb3 : h1 (addr + 3) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_none] at hown
              contradiction
          | some _ =>
          cases hb4 : h1 (addr + 4) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_some, hb4, Option.bind_none] at hown
              contradiction
          | some _ =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_some, hb4, Option.bind_some, heq, Option.bind_none] at hown
              contradiction
        have own6 : h1 (addr + 6) ≠ none := by
          intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
          cases hb0 : h1 addr with
          | none => simp only [hb0, Option.bind_none] at hown; contradiction
          | some _ =>
          cases hb1 : h1 (addr + 1) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
              contradiction
          | some _ =>
          cases hb2 : h1 (addr + 2) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none,
                ] at hown
              contradiction
          | some _ =>
          cases hb3 : h1 (addr + 3) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_none] at hown
              contradiction
          | some _ =>
          cases hb4 : h1 (addr + 4) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_some, hb4, Option.bind_none] at hown
              contradiction
          | some _ =>
          cases hb5 : h1 (addr + 5) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_none] at hown
              contradiction
          | some _ =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_some, heq,
                Option.bind_none] at hown
              contradiction
        have own7 : h1 (addr + 7) ≠ none := by
          intro heq; simp only [readHeap, Option.bind_eq_bind] at hown
          cases hb0 : h1 addr with
          | none => simp only [hb0, Option.bind_none] at hown; contradiction
          | some _ =>
          cases hb1 : h1 (addr + 1) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_none] at hown
              contradiction
          | some _ =>
          cases hb2 : h1 (addr + 2) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_none,
                ] at hown
              contradiction
          | some _ =>
          cases hb3 : h1 (addr + 3) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_none] at hown
              contradiction
          | some _ =>
          cases hb4 : h1 (addr + 4) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_some, hb4, Option.bind_none] at hown
              contradiction
          | some _ =>
          cases hb5 : h1 (addr + 5) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_none] at hown
              contradiction
          | some _ =>
          cases hb6 : h1 (addr + 6) with
          | none =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_some, hb6,
                Option.bind_none] at hown
              contradiction
          | some _ =>
              simp only [hb0, Option.bind_some, hb1, Option.bind_some, hb2, Option.bind_some, hb3,
                Option.bind_some, hb4, Option.bind_some, hb5, Option.bind_some, hb6, heq,
                Option.bind_some, Option.bind_none] at hown
              contradiction
        simp only [writeMem]
        by_cases heq : a = addr
        · exact absurd (not_in_chunk addr own0) (by subst heq; simp [ha])
        · by_cases heq1 : a = addr + 1
          · have h := not_in_chunk _ own1; rw [← heq1] at h; exact absurd ha (by simp [h])
          · by_cases heq2 : a = addr + 2
            · have h := not_in_chunk _ own2; rw [← heq2] at h; exact absurd ha (by simp [h])
            · by_cases heq3 : a = addr + 3
              · have h := not_in_chunk _ own3; rw [← heq3] at h; exact absurd ha (by simp [h])
              · by_cases heq4 : a = addr + 4
                · have h := not_in_chunk _ own4; rw [← heq4] at h; exact absurd ha (by simp [h])
                · by_cases heq5 : a = addr + 5
                  · have h := not_in_chunk _ own5; rw [← heq5] at h; exact absurd ha (by simp [h])
                  · by_cases heq6 : a = addr + 6
                    · have h := not_in_chunk _ own6; rw [← heq6] at h; exact absurd ha (by simp [h])
                    · by_cases heq7 : a = addr + 7
                      · have h := not_in_chunk _ own7
                        rw [← heq7] at h; exact absurd ha (by simp [h])
                      · simp only [if_neg heq, if_neg heq1, if_neg heq2, if_neg heq3,
                                   if_neg heq4, if_neg heq5, if_neg heq6, if_neg heq7]
                        apply hc2; assumption
  exact consistent_union_of_consistent hdisj' hc1' hc2'

lemma heaponly_reg_change {R : Assert} (hR : Assert.HeapOnly R)
    {rf rf' : RegFile} {h : Heap} (hRrfh : R rf h) : R rf' h :=
  hR rf rf' h hRrfh

/- Instruction-level one-step soundness -/


lemma step_alu64_inv {prog : Program} {s sf : State}
    {op : AluOp} {dst : Reg} {src : Src}
    (hprog : prog[s.pc]? = some (Instr.alu64 op dst src))
    (hstep : Step prog s sf) :
    sf.regs = s.regs.set dst (evalAlu64 op (s.regs dst) (evalSrc s.regs src)) ∧
    sf.mem = s.mem ∧
    sf.pc = s.pc + 1 := by
  cases hstep <;> simp_all [Instr.alu64.injEq]

lemma step_alu32_inv {prog : Program} {s sf : State}
    {op : AluOp} {dst : Reg} {src : Src}
    (hprog : prog[s.pc]? = some (Instr.alu32 op dst src))
    (hstep : Step prog s sf) :
    sf.regs = s.regs.set dst (evalAlu32 op (s.regs dst) (evalSrc s.regs src)) ∧
    sf.mem = s.mem ∧
    sf.pc = s.pc + 1 := by
  cases hstep <;> simp_all [Instr.alu32.injEq]

lemma step_neg64_inv {prog : Program} {s sf : State}
    {dst : Reg}
    (hprog : prog[s.pc]? = some (Instr.neg64 dst))
    (hstep : Step prog s sf) :
    sf.regs = s.regs.set dst (- s.regs dst) ∧
    sf.mem = s.mem ∧
    sf.pc = s.pc + 1 := by
  cases hstep <;> simp_all [Instr.neg64.injEq]

lemma step_neg32_inv {prog : Program} {s sf : State}
    {dst : Reg}
    (hprog : prog[s.pc]? = some (Instr.neg32 dst))
    (hstep : Step prog s sf) :
    sf.regs = s.regs.set dst (zext32 (- s.regs dst)) ∧
    sf.mem = s.mem ∧
    sf.pc = s.pc + 1 := by
  cases hstep <;> simp_all [Instr.neg32.injEq]

lemma step_endian_inv {prog : Program} {s sf : State}
    {e : Endian} {sz : Size} {dst : Reg}
    (hprog : prog[s.pc]? = some (Instr.endian e sz dst))
    (hstep : Step prog s sf) :
    sf.regs = s.regs.set dst (evalEndian e sz (s.regs dst)) ∧
    sf.mem = s.mem ∧
    sf.pc = s.pc + 1 := by
  cases hstep <;> simp_all [Instr.endian.injEq]

lemma step_lddw_inv {prog : Program} {s sf : State}
    {dst : Reg} {imm : BitVec 64}
    (hprog : prog[s.pc]? = some (Instr.lddw dst imm))
    (hstep : Step prog s sf) :
    sf.regs = s.regs.set dst imm ∧
    sf.mem = s.mem ∧
    sf.pc = s.pc + 2 := by
  cases hstep <;> simp_all [Instr.lddw.injEq]

lemma step_ja_inv {prog : Program} {s sf : State}
    {off : BitVec 16}
    (hprog : prog[s.pc]? = some (Instr.ja off))
    (hstep : Step prog s sf) :
    sf.regs = s.regs ∧
    sf.mem = s.mem ∧
    sf.pc = ((s.pc : Int) + 1 + offset16ToInt off).toNat := by
  cases hstep <;> simp_all [Instr.ja.injEq]

lemma step_jmp64_taken_inv {prog : Program} {s sf : State}
    {op : JmpOp} {dst : Reg} {src : Src} {off : BitVec 16}
    (hprog : prog[s.pc]? = some (Instr.jmp64 op dst src off))
    (htaken : evalJmp64 op (s.regs dst) (evalSrc s.regs src) = true)
    (hstep : Step prog s sf) :
    sf.regs = s.regs ∧
    sf.mem = s.mem ∧
    sf.pc = ((s.pc : Int) + 1 + offset16ToInt off).toNat := by
  cases hstep <;> simp_all [Instr.jmp64.injEq]

lemma step_jmp64_fall_inv {prog : Program} {s sf : State}
    {op : JmpOp} {dst : Reg} {src : Src} {off : BitVec 16}
    (hprog : prog[s.pc]? = some (Instr.jmp64 op dst src off))
    (hfall : evalJmp64 op (s.regs dst) (evalSrc s.regs src) = false)
    (hstep : Step prog s sf) :
    sf.regs = s.regs ∧
    sf.mem = s.mem ∧
    sf.pc = s.pc + 1 := by
  cases hstep <;> simp_all [Instr.jmp64.injEq]

lemma step_jmp32_taken_inv {prog : Program} {s sf : State}
    {op : JmpOp} {dst : Reg} {src : Src} {off : BitVec 16}
    (hprog : prog[s.pc]? = some (Instr.jmp32 op dst src off))
    (htaken : evalJmp32 op (s.regs dst) (evalSrc s.regs src) = true)
    (hstep : Step prog s sf) :
    sf.regs = s.regs ∧
    sf.mem = s.mem ∧
    sf.pc = ((s.pc : Int) + 1 + offset16ToInt off).toNat := by
  cases hstep <;> simp_all [Instr.jmp32.injEq]

lemma step_jmp32_fall_inv {prog : Program} {s sf : State}
    {op : JmpOp} {dst : Reg} {src : Src} {off : BitVec 16}
    (hprog : prog[s.pc]? = some (Instr.jmp32 op dst src off))
    (hfall : evalJmp32 op (s.regs dst) (evalSrc s.regs src) = false)
    (hstep : Step prog s sf) :
    sf.regs = s.regs ∧
    sf.mem = s.mem ∧
    sf.pc = s.pc + 1 := by
  cases hstep <;> simp_all [Instr.jmp32.injEq]

lemma step_load_inv {prog : Program} {s sf : State}
    {sz : Size} {dst src_reg : Reg} {off : BitVec 16}
    (hprog : prog[s.pc]? = some (Instr.load sz dst src_reg off))
    (hstep : Step prog s sf) :
    sf.regs = s.regs.set dst (readMem s.mem (s.regs src_reg + BitVec.signExtend 64 off) sz) ∧
    sf.mem = s.mem ∧
    sf.pc = s.pc + 1 := by
  cases hstep <;> simp_all [Instr.load.injEq]

lemma step_store_inv {prog : Program} {s sf : State}
    {sz : Size} {dst : Reg} {off : BitVec 16} {src : Src}
    (hprog : prog[s.pc]? = some (Instr.store sz dst off src))
    (hstep : Step prog s sf) :
    sf.regs = s.regs ∧
    sf.mem = writeMem s.mem (s.regs dst + BitVec.signExtend 64 off) (evalSrc s.regs src) sz ∧
    sf.pc = s.pc + 1 := by
  cases hstep <;> simp_all [Instr.store.injEq]

lemma step_lddw_pc {prog : Program} {s sf : State}
    {dst : Reg} {imm : BitVec 64}
    (hprog : prog[s.pc]? = some (Instr.lddw dst imm))
    (hstep : Step prog s sf) :
    sf.pc = s.pc + 2 := (step_lddw_inv hprog hstep).2.2

private abbrev atomicNewVal (op : AtomicOp) (oldVal srcVal r0Val : BitVec 64) : BitVec 64 :=
  match op with
  | AtomicOp.add     => oldVal + srcVal
  | AtomicOp.or      => oldVal ||| srcVal
  | AtomicOp.and     => oldVal &&& srcVal
  | AtomicOp.xor     => oldVal ^^^ srcVal
  | AtomicOp.xchg    => srcVal
  | AtomicOp.cmpxchg => if r0Val = oldVal then srcVal else oldVal

private abbrev atomicNewRegs (op : AtomicOp) (fetch : Bool)
    (regs : RegFile) (src : Reg) (oldVal : BitVec 64) : RegFile :=
  match op with
  | AtomicOp.cmpxchg => regs.set Reg.r0 oldVal
  | _                => if fetch then regs.set src oldVal else regs

set_option linter.flexible false in
lemma step_atomic_inv {prog : Program} {s sf : State}
    {sz : Size} {op : AtomicOp} {fetch : Bool} {dst src : Reg} {off : BitVec 16}
    (hprog : prog[s.pc]? = some (Instr.atomic sz op fetch dst src off))
    (hstep : Step prog s sf) :
    sf.mem  = writeMem s.mem
                (s.regs dst + BitVec.signExtend 64 off)
                (atomicNewVal op
                  (readMem s.mem (s.regs dst + BitVec.signExtend 64 off) sz)
                  (s.regs src) (s.regs Reg.r0))
                sz ∧
    sf.regs = atomicNewRegs op fetch s.regs src
                (readMem s.mem (s.regs dst + BitVec.signExtend 64 off) sz) ∧
    sf.pc   = s.pc + 1 := by
  cases hstep <;> simp_all [Instr.atomic.injEq]
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _›
  subst_vars; cases op <;> cases fetch <;>
  simp [atomicNewVal, atomicNewRegs]

set_option linter.flexible false in
lemma step_call_inv {prog : Program} {s sf : State}
    {fid : BitVec 32}
    (hprog : prog[s.pc]? = some (Instr.call fid))
    (hstep : Step prog s sf) :
    (∀ r, r ∈ ([Reg.r6, Reg.r7, Reg.r8, Reg.r9, Reg.r10] : List Reg) →
          sf.regs r = s.regs r) ∧
    (∃ fp : Heap, ∀ a, fp a = none → sf.mem a = s.mem a) ∧
    sf.pc = s.pc + 1 := by
  cases hstep <;> simp_all [Instr.call.injEq]
  exact ⟨_, by assumption⟩

/- Structural soundness rules -/

lemma sem_rule_exit {prog : Program} {pc : ℕ} {Q : Assert}
    (hprog : prog[pc]? = some Instr.exit) :
    SemTriple prog pc Q Q := by
  intro s h1 h2 hpc hQ hcons hdisj sf hsteps hexit hsafe
  have hprog' : prog[s.pc]? = some Instr.exit := by rw [hpc]; exact hprog
  have hsf : sf = s := steps_from_exit prog s sf hprog' hsteps
  subst hsf
  exists h1

lemma sem_rule_consequence {prog : Program} {pc : ℕ} {P P' Q Q' : Assert}
    (hP : P' ⊢ₐ P)
    (ih : SemTriple prog pc P Q)
    (hQ : Q ⊢ₐ Q') :
    SemTriple prog pc P' Q' := by
  intro s h1 h2 hpc hP' hcons hdisj sf hsteps hexit hsafe
  cases ih s h1 h2 hpc (hP s.regs h1 hP') hcons hdisj sf hsteps hexit hsafe with
  | intro hf1 rest =>
    cases rest with
    | intro hQhf1 rest =>
      cases rest with
      | intro hconsf hdisjf =>
        exists hf1
        constructor
        · exact hQ sf.regs hf1 hQhf1
        constructor
        · exact hconsf
        · exact hdisjf

lemma sem_rule_disj {prog : Program} {pc : ℕ} {P1 P2 Q : Assert}
    (ih1 : SemTriple prog pc P1 Q)
    (ih2 : SemTriple prog pc P2 Q) :
    SemTriple prog pc (P1.or P2) Q := by
  intro s h1 h2 hpc hPor hcons hdisj sf hsteps hexit hsafe
  cases hPor with
  | inl hP1 => apply ih1 <;> assumption
  | inr hP2 => apply ih2 <;> assumption

lemma sem_rule_exists {prog : Program} {pc : ℕ} {α : Type}
    {P : α → Assert} {Q : Assert}
    (ih : ∀ x : α, SemTriple prog pc (P x) Q) :
    SemTriple prog pc (Assert.exists_ P) Q := by
  intro s h1 h2 hpc hPex hcons hdisj sf hsteps hexit hsafe
  cases hPex with
  | intro x hPx =>
    apply ih <;> assumption

lemma sem_rule_frame {prog : Program} {pc : ℕ} {P Q R : Assert}
    (hheap : Assert.HeapOnly R)
    (ih : SemTriple prog pc P Q) :
    SemTriple prog pc (P ⋆ R) (Q ⋆ R) := by
  intro s h h2 hpc hPR hcons hdisj sf hsteps hexit hsafe
  cases hPR with
  | intro h1 rest =>
    cases rest with
    | intro hR_heap rest =>
      cases rest with
      | intro hdisj12 rest =>
        cases rest with
        | intro hunion rest =>
          cases rest with
          | intro hP hR =>
            subst hunion
            have hdisj1_Rh2 : Heap.Disjoint h1 (Heap.union hR_heap h2) :=
              disjoint_assoc_right hdisj12 hdisj
            have hcons' : Heap.Consistent (Heap.union h1 (Heap.union hR_heap h2)) s.mem := by
              rw [← heap_union_assoc]; exact hcons
            have hsafe' : HeapSafe prog (Heap.union h1 (Heap.union hR_heap h2)) hsteps := by
              rw [← heap_union_assoc]; exact hsafe
            cases ih s h1 (Heap.union hR_heap h2) hpc hP hcons'
                hdisj1_Rh2 sf hsteps hexit hsafe' with
            | intro hf1 rest =>
              cases rest with
              | intro hQhf1 rest =>
                cases rest with
                | intro hconsf hdisjf =>
                  have hRsf : R sf.regs hR_heap := heaponly_reg_change hheap hR
                  have hdisj_f1_R : Heap.Disjoint hf1 hR_heap :=
                    disjoint_union_left hdisjf
                  have hdisj_fR_h2 : Heap.Disjoint (Heap.union hf1 hR_heap) h2 :=
                    disjoint_union_of_disjoint_union hdisjf hdisj
                  have hconsf' :
                      Heap.Consistent (Heap.union (Heap.union hf1 hR_heap) h2) sf.mem := by
                    rw [heap_union_assoc]; exact hconsf
                  exists Heap.union hf1 hR_heap
                  constructor
                  · exists hf1; exists hR_heap
                  constructor
                  · exact hconsf'
                  · exact hdisj_fR_h2

/- Instruction rule soundness -/

private lemma mem_preserving_step {_ : Program} {s sf : State}
    {pc' : ℕ} {regs' : RegFile}
    (_hpc' : sf.pc = pc')
    (hmem : sf.mem = s.mem)
    (_hregs : sf.regs = regs')
    (h1 h2 : Heap)
    (hcons : Heap.Consistent (Heap.union h1 h2) s.mem)
    (hdisj : Heap.Disjoint h1 h2) :
    Heap.Consistent (Heap.union h1 h2) sf.mem ∧ Heap.Disjoint h1 h2 := by
  rw [hmem]
  constructor
  · exact hcons
  · exact hdisj

lemma sem_rule_alu64 {prog : Program} {pc : ℕ}
    {op : AluOp} {dst : Reg} {src : Src} {R Q : Assert}
    (hprog : prog[pc]? = some (Instr.alu64 op dst src))
    (ih : SemTriple prog (pc + 1) R Q) :
    SemTriple prog pc (wp_alu64 op dst src R) Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.alu64 op dst src) := by rw [hpc]; exact hprog
      cases step_alu64_inv hprog' hstep with
      | intro hregs rest =>
        cases rest with
        | intro hmem hpc1 =>
          simp only [wp_alu64] at hP
          have hs1pc : s1.pc = pc + 1 := by omega
          have hs1mem : s1.mem = s.mem := hmem
          have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by rw [hs1mem]; exact hcons
          have hs1regs :
              s1.regs = s.regs.set dst (evalAlu64 op (s.regs dst) (evalSrc s.regs src)) :=
            hregs
          rw [← hs1regs] at hP
          have htail := heapSafe_tail hsafe
          apply ih <;> assumption

lemma sem_rule_alu32 {prog : Program} {pc : ℕ}
    {op : AluOp} {dst : Reg} {src : Src} {R Q : Assert}
    (hprog : prog[pc]? = some (Instr.alu32 op dst src))
    (ih : SemTriple prog (pc + 1) R Q) :
    SemTriple prog pc (wp_alu32 op dst src R) Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.alu32 op dst src) := by rw [hpc]; exact hprog
      cases step_alu32_inv hprog' hstep with
      | intro hregs rest =>
        cases rest with
        | intro hmem hpc1 =>
          simp only [wp_alu32] at hP
          have hs1pc : s1.pc = pc + 1 := by omega
          have hs1mem : s1.mem = s.mem := hmem
          have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by rw [hs1mem]; exact hcons
          have hs1regs :
              s1.regs = s.regs.set dst (evalAlu32 op (s.regs dst) (evalSrc s.regs src)) :=
            hregs
          rw [← hs1regs] at hP
          have htail := heapSafe_tail hsafe
          apply ih <;> assumption

lemma sem_rule_neg64 {prog : Program} {pc : ℕ}
    {dst : Reg} {R Q : Assert}
    (hprog : prog[pc]? = some (Instr.neg64 dst))
    (ih : SemTriple prog (pc + 1) R Q) :
    SemTriple prog pc (wp_neg64 dst R) Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.neg64 dst) := by rw [hpc]; exact hprog
      cases step_neg64_inv hprog' hstep with
      | intro hregs rest =>
        cases rest with
        | intro hmem hpc1 =>
          simp only [wp_neg64] at hP
          have hs1pc : s1.pc = pc + 1 := by omega
          have hs1mem : s1.mem = s.mem := hmem
          have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by rw [hs1mem]; exact hcons
          have hs1regs : s1.regs = s.regs.set dst (- s.regs dst) := hregs
          rw [← hs1regs] at hP
          have htail := heapSafe_tail hsafe
          apply ih <;> assumption

lemma sem_rule_neg32 {prog : Program} {pc : ℕ}
    {dst : Reg} {R Q : Assert}
    (hprog : prog[pc]? = some (Instr.neg32 dst))
    (ih : SemTriple prog (pc + 1) R Q) :
    SemTriple prog pc (wp_neg32 dst R) Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.neg32 dst) := by rw [hpc]; exact hprog
      cases step_neg32_inv hprog' hstep with
      | intro hregs rest =>
        cases rest with
        | intro hmem hpc1 =>
          simp only [wp_neg32] at hP
          have hs1pc : s1.pc = pc + 1 := by omega
          have hs1mem : s1.mem = s.mem := hmem
          have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by rw [hs1mem]; exact hcons
          have hs1regs : s1.regs = s.regs.set dst (zext32 (- s.regs dst)) := hregs
          rw [← hs1regs] at hP
          have htail := heapSafe_tail hsafe
          apply ih <;> assumption

lemma sem_rule_endian {prog : Program} {pc : ℕ}
    {e : Endian} {sz : Size} {dst : Reg} {R Q : Assert}
    (hprog : prog[pc]? = some (Instr.endian e sz dst))
    (ih : SemTriple prog (pc + 1) R Q) :
    SemTriple prog pc (wp_endian e sz dst R) Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.endian e sz dst) := by rw [hpc]; exact hprog
      cases step_endian_inv hprog' hstep with
      | intro hregs rest =>
        cases rest with
        | intro hmem hpc1 =>
          simp only [wp_endian] at hP
          have hs1pc : s1.pc = pc + 1 := by omega
          have hs1mem : s1.mem = s.mem := hmem
          have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by rw [hs1mem]; exact hcons
          have hs1regs : s1.regs = s.regs.set dst (evalEndian e sz (s.regs dst)) := hregs
          rw [← hs1regs] at hP
          have htail := heapSafe_tail hsafe
          apply ih <;> assumption

lemma sem_rule_lddw {prog : Program} {pc : ℕ}
    {dst : Reg} {imm : BitVec 64} {R Q : Assert}
    (hprog : prog[pc]? = some (Instr.lddw dst imm))
    (ih : SemTriple prog (pc + 2) R Q) :
    SemTriple prog pc (wp_lddw dst imm R) Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.lddw dst imm) := by rw [hpc]; exact hprog
      cases step_lddw_inv hprog' hstep with
      | intro hregs rest =>
        cases rest with
        | intro hmem hpc1 =>
          simp only [wp_lddw] at hP
          have hs1pc : s1.pc = pc + 2 := by omega
          have hs1mem : s1.mem = s.mem := hmem
          have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by rw [hs1mem]; exact hcons
          have hs1regs : s1.regs = s.regs.set dst imm := hregs
          rw [← hs1regs] at hP
          have htail := heapSafe_tail hsafe
          apply ih <;> assumption

lemma sem_rule_ja {prog : Program} {pc : ℕ}
    {off : BitVec 16} {pc' : Int} {R Q : Assert}
    (hprog : prog[pc]? = some (Instr.ja off))
    (hpc'_eq : pc' = (pc : Int) + 1 + offset16ToInt off)
    (_h0 : 0 ≤ pc')
    (ih : SemTriple prog pc'.toNat R Q) :
    SemTriple prog pc R Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.ja off) := by rw [hpc]; exact hprog
      cases step_ja_inv hprog' hstep with
      | intro hregs rest =>
        cases rest with
        | intro hmem hpc1 =>
          have hs1pc : s1.pc = pc'.toNat := by rw [hpc1, hpc, hpc'_eq]
          have hs1mem : s1.mem = s.mem := hmem
          have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by rw [hs1mem]; exact hcons
          have hs1regs : s1.regs = s.regs := hregs
          rw [← hs1regs] at hP
          have htail := heapSafe_tail hsafe
          apply ih <;> assumption

lemma sem_rule_jmp64 {prog : Program} {pc : ℕ}
    {op : JmpOp} {dst : Reg} {src : Src} {off : BitVec 16} {pc' : Int}
    {R_taken R_fall Q : Assert}
    (hprog : prog[pc]? = some (Instr.jmp64 op dst src off))
    (hpc'_eq : pc' = (pc : Int) + 1 + offset16ToInt off)
    (_h0 : 0 ≤ pc')
    (ih_taken : SemTriple prog pc'.toNat R_taken Q)
    (ih_fall : SemTriple prog (pc + 1) R_fall Q) :
    SemTriple prog pc (wp_jmp64 op dst src R_taken R_fall) Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.jmp64 op dst src off) := by rw [hpc]; exact hprog
      simp only [wp_jmp64] at hP
      have htail := heapSafe_tail hsafe
      by_cases hcond : evalJmp64 op (s.regs dst) (evalSrc s.regs src) = true
      · cases step_jmp64_taken_inv hprog' hcond hstep with
        | intro hregs rest =>
          cases rest with
          | intro hmem hpc1 =>
            have hs1pc : s1.pc = pc'.toNat := by rw [hpc1, hpc, hpc'_eq]
            have hs1mem : s1.mem = s.mem := hmem
            have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by rw [hs1mem]; exact hcons
            have hs1regs : s1.regs = s.regs := hregs
            rw [← hs1regs] at hP
            have hPtaken := hP.1 (by rw [hs1regs]; exact hcond)
            apply ih_taken <;> assumption
      · push_neg at hcond
        have hfall : evalJmp64 op (s.regs dst) (evalSrc s.regs src) = false := by
          cases heq : evalJmp64 op (s.regs dst) (evalSrc s.regs src) <;> simp_all
        cases step_jmp64_fall_inv hprog' hfall hstep with
        | intro hregs rest =>
          cases rest with
          | intro hmem hpc1 =>
            have hs1pc : s1.pc = pc + 1 := by omega
            have hs1mem : s1.mem = s.mem := hmem
            have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by rw [hs1mem]; exact hcons
            have hs1regs : s1.regs = s.regs := hregs
            rw [← hs1regs] at hP
            have hPfall := hP.2 (by rw [hs1regs]; exact hfall)
            apply ih_fall <;> assumption

lemma sem_rule_jmp32 {prog : Program} {pc : ℕ}
    {op : JmpOp} {dst : Reg} {src : Src} {off : BitVec 16} {pc' : Int}
    {R_taken R_fall Q : Assert}
    (hprog : prog[pc]? = some (Instr.jmp32 op dst src off))
    (hpc'_eq : pc' = (pc : Int) + 1 + offset16ToInt off)
    (_h0 : 0 ≤ pc')
    (ih_taken : SemTriple prog pc'.toNat R_taken Q)
    (ih_fall : SemTriple prog (pc + 1) R_fall Q) :
    SemTriple prog pc (wp_jmp32 op dst src R_taken R_fall) Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.jmp32 op dst src off) := by rw [hpc]; exact hprog
      simp only [wp_jmp32] at hP
      have htail := heapSafe_tail hsafe
      by_cases hcond : evalJmp32 op (s.regs dst) (evalSrc s.regs src) = true
      · cases step_jmp32_taken_inv hprog' hcond hstep with
        | intro hregs rest =>
          cases rest with
          | intro hmem hpc1 =>
            have hs1pc : s1.pc = pc'.toNat := by rw [hpc1, hpc, hpc'_eq]
            have hs1mem : s1.mem = s.mem := hmem
            have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by rw [hs1mem]; exact hcons
            have hs1regs : s1.regs = s.regs := hregs
            rw [← hs1regs] at hP
            have hPtaken := hP.1 (by rw [hs1regs]; exact hcond)
            apply ih_taken <;> assumption
      · push_neg at hcond
        have hfall : evalJmp32 op (s.regs dst) (evalSrc s.regs src) = false := by
          cases heq : evalJmp32 op (s.regs dst) (evalSrc s.regs src) <;> simp_all
        cases step_jmp32_fall_inv hprog' hfall hstep with
        | intro hregs rest =>
          cases rest with
          | intro hmem hpc1 =>
            have hs1pc : s1.pc = pc + 1 := by omega
            have hs1mem : s1.mem = s.mem := hmem
            have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by rw [hs1mem]; exact hcons
            have hs1regs : s1.regs = s.regs := hregs
            rw [← hs1regs] at hP
            have hPfall := hP.2 (by rw [hs1regs]; exact hfall)
            apply ih_fall <;> assumption

lemma sem_rule_load {prog : Program} {pc : ℕ}
    {sz : Size} {dst src_reg : Reg} {off : BitVec 16} {R Q : Assert}
    (hprog : prog[pc]? = some (Instr.load sz dst src_reg off))
    (ih : SemTriple prog (pc + 1) R Q) :
    SemTriple prog pc (wp_load sz dst src_reg off R) Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.load sz dst src_reg off) := by rw [hpc]; exact hprog
      cases step_load_inv hprog' hstep with
      | intro hregs rest =>
        cases rest with
        | intro hmem hpc1 =>
          simp only [wp_load] at hP
          cases hP with
          | intro v rest =>
            cases rest with
            | intro hread hR =>
              have hc1 := consistent_union_left hcons
              have hreadmem := consistent_readHeap hc1 hread
              have hs1pc : s1.pc = pc + 1 := by omega
              have hs1mem : s1.mem = s.mem := hmem
              have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by rw [hs1mem]; exact hcons
              have hs1regs : s1.regs = s.regs.set dst v := by rw [hregs, hreadmem]
              rw [← hs1regs] at hR
              have htail := heapSafe_tail hsafe
              apply ih <;> assumption

lemma sem_rule_store {prog : Program} {pc : ℕ}
    {sz : Size} {dst : Reg} {off : BitVec 16} {src : Src} {R Q : Assert}
    (hprog : prog[pc]? = some (Instr.store sz dst off src))
    (ih : SemTriple prog (pc + 1) R Q) :
    SemTriple prog pc (wp_store sz dst off src R) Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.store sz dst off src) := by rw [hpc]; exact hprog
      cases step_store_inv hprog' hstep with
      | intro hregs rest =>
        cases rest with
        | intro hmem hpc1 =>
          simp only [wp_store] at hP
          cases hP with
          | intro hown hR =>
            let addr := s.regs dst + BitVec.signExtend 64 off
            let val  := evalSrc s.regs src
            have hs1pc : s1.pc = pc + 1 := by omega
            have hs1mem : s1.mem = writeMem s.mem addr val sz := hmem
            have hs1regs : s1.regs = s.regs := hregs
            let h1' := writeHeap h1 addr sz val
            have hcons1 : Heap.Consistent (Heap.union h1' h2) s1.mem := by
              rw [hs1mem]; exact consistent_union_writeHeap hdisj hcons hown
            have hdisj1 : Heap.Disjoint h1' h2 := disjoint_writeHeap hdisj hown
            have hRh1' : R s1.regs h1' := by rw [hs1regs]; exact hR
            have htail : HeapSafe prog (Heap.union h1' h2) hsteps' :=
              heapSafe_writeHeap hown (heapSafe_tail hsafe)
            apply ih <;> assumption

lemma sem_rule_atomic {prog : Program} {pc : ℕ}
    {sz : Size} {op : AtomicOp} {fetch : Bool} {dst src : Reg} {off : BitVec 16}
    {R Q : Assert}
    (hprog : prog[pc]? = some (Instr.atomic sz op fetch dst src off))
    (ih : SemTriple prog (pc + 1) R Q) :
    SemTriple prog pc (wp_atomic sz op fetch dst src off R) Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.atomic sz op fetch dst src off) :=
        by rw [hpc]; exact hprog
      cases step_atomic_inv hprog' hstep with
      | intro hmem rest =>
        cases rest with
        | intro hregs hpc1 =>
          simp only [wp_atomic] at hP
          cases hP with
          | intro old_val rest =>
            cases rest with
            | intro hread hR =>
              -- Connect heap read to memory read
              have hc1 := consistent_union_left hcons
              have holdval : readMem s.mem (s.regs dst + BitVec.signExtend 64 off) sz = old_val :=
                consistent_readHeap hc1 hread
              -- The heap owns the chunk (readHeap ≠ none)
              have hown : readHeap h1 (s.regs dst + BitVec.signExtend 64 off) sz ≠ none := by
                simp [hread]
              -- Successor state bookkeeping
              have hs1pc : s1.pc = pc + 1 := by omega
              -- Rewrite readMem occurrences in hmem/hregs to old_val
              simp only [atomicNewVal, atomicNewRegs, holdval] at hmem hregs
              -- h1' is the updated heap after the atomic write
              let h1' := writeHeap h1 (s.regs dst + BitVec.signExtend 64 off) sz
                           (atomicNewVal op old_val (s.regs src) (s.regs Reg.r0))
              have hcons1 : Heap.Consistent (Heap.union h1' h2) s1.mem := by
                rw [hmem]; exact consistent_union_writeHeap hdisj hcons hown
              have hdisj1 : Heap.Disjoint h1' h2 := disjoint_writeHeap hdisj hown
              -- hR has type R (atomicNewRegs ... old_val) h1', and hregs says s1.regs equals that
              have hR1 : R s1.regs h1' := by rw [hregs]; exact hR
              have htail : HeapSafe prog (Heap.union h1' h2) hsteps' :=
                heapSafe_writeHeap hown (heapSafe_tail hsafe)
              apply ih <;> assumption

lemma sem_rule_call {prog : Program} {pc : ℕ}
    {fid : BitVec 32} {R Q : Assert}
    (hprog : prog[pc]? = some (Instr.call fid))
    (ih : SemTriple prog (pc + 1) R Q) :
    SemTriple prog pc (wp_call R) Q := by
  intro s h1 h2 hpc hP hcons hdisj sf hsteps hexit hsafe
  cases hsteps with
  | refl =>
      simp [hpc, hprog] at hexit
  | step s s1 sf' hstep hsteps' =>
      have hprog' : prog[s.pc]? = some (Instr.call fid) := by rw [hpc]; exact hprog
      cases step_call_inv hprog' hstep with
      | intro hcallee rest =>
        cases rest with
        | intro hfp_exists hpc1 =>
          cases hfp_exists with
          | intro fp hfp =>
            have hs1pc : s1.pc = pc + 1 := by omega
            -- Decompose HeapSafe to get hhead (call-safety) and htail (rest)
            have hhead := heapSafe_head hsafe
            have htail := heapSafe_tail hsafe
            -- HeapSafe gives: call step only touches addresses outside h1 ∪ h2
            have hmod : ∀ a, s1.mem a ≠ s.mem a → (Heap.union h1 h2) a = none :=
              hhead ⟨fid, hprog'⟩
            -- Therefore h1 is still consistent with the post-call memory
            have hcons_h1 : Heap.Consistent h1 s1.mem := by
              intro a b ha
              by_contra hne
              have hneq : s1.mem a ≠ s.mem a := by
                intro heq
                exact hne (heq.trans (consistent_union_left hcons a b (by simp [ha])))
              have := hmod a hneq
              simp [Heap.union, ha] at this
            -- Apply wp_call with the post-call register file and memory
            have hR : R s1.regs h1 := hP s1.regs s1.mem hcons_h1 hcallee
            -- Full consistency is preserved by the same argument
            have hcons1 : Heap.Consistent (Heap.union h1 h2) s1.mem := by
              intro a b ha
              by_contra hne
              have hneq : s1.mem a ≠ s.mem a := by
                intro heq
                exact hne (heq.trans (hcons a b ha))
              have := hmod a hneq
              simp [ha] at this
            apply ih <;> assumption

/- Main soundness theorem -/

theorem htriple_sound {prog : Program} {pc : ℕ} {P Q : Assert}
    (ht : HTriple prog pc P Q) :
    SemTriple prog pc P Q := by
  induction ht <;> first
  | apply sem_rule_exit        <;> assumption
  | apply sem_rule_alu64       <;> assumption
  | apply sem_rule_alu32       <;> assumption
  | apply sem_rule_neg64       <;> assumption
  | apply sem_rule_neg32       <;> assumption
  | apply sem_rule_endian      <;> assumption
  | apply sem_rule_lddw        <;> assumption
  | apply sem_rule_ja          <;> assumption
  | apply sem_rule_jmp64       <;> assumption
  | apply sem_rule_jmp32       <;> assumption
  | apply sem_rule_load        <;> assumption
  | apply sem_rule_store       <;> assumption
  | apply sem_rule_atomic      <;> assumption
  | apply sem_rule_call        <;> assumption
  | apply sem_rule_frame       <;> assumption
  | apply sem_rule_disj        <;> assumption
  | apply sem_rule_exists      <;> assumption
  | apply sem_rule_consequence <;> assumption

theorem wf_sem_sound (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
    (Q : Assert) (hwf : WellFormed prog mapSize callTypes) :
    SemTriple prog 0 (vcgWP prog Q (prog.size + 1) 0) Q :=
  htriple_sound (wf_vcg prog mapSize callTypes Q hwf)

def OracleHeapSafe (oracle : CallOracle) (h : Heap) : Prop :=
  ∀ (fid : BitVec 32) (regs : RegFile) (mem : Memory) (a : BitVec 64),
    (oracle fid regs mem).2 a ≠ mem a → h a = none

lemma memPreserving_heapSafe (oracle : CallOracle)
    (hm : ∀ fid regs mem, (oracle fid regs mem).2 = mem) (h : Heap) :
    OracleHeapSafe oracle h := by
  intro fid regs mem a ha
  exact absurd (congrFun (hm fid regs mem) a) ha

theorem interp_heapSafe
    (prog : Program) (oracle : CallOracle) (h : Heap)
    (hok : OracleOk oracle)
    (hhs : OracleHeapSafe oracle h)
    (fuel : ℕ) (s₀ sf : State)
    (hint : interp prog oracle s₀ fuel = some sf) :
    ∃ hsteps : Steps prog s₀ sf,
      prog[sf.pc]? = some Instr.exit ∧ HeapSafe prog h hsteps := by
  induction fuel generalizing s₀ with
  | zero => simp [interp] at hint
  | succ n ih =>
    simp only [interp] at hint
    match hpc : prog[s₀.pc]? with
    | none => simp [hpc] at hint
    | some Instr.exit =>
        simp only [hpc] at hint
        have heq : sf = s₀ := (Option.some.inj hint).symm
        subst heq
        exists Steps.refl _
        constructor
        · assumption
        · exact HeapSafe.refl _
    | some (Instr.alu64 op dst src) =>
        simp only [hpc] at hint
        let s₁ := { s₀ with
          regs := s₀.regs.set dst (evalAlu64 op (s₀.regs dst) (evalSrc s₀.regs src)),
          pc := s₀.pc + 1 }
        cases ih s₁ hint with
        | intro hsteps' rest =>
          cases rest with
          | intro hexit hsafe' =>
            have hstep : Step prog s₀ s₁ := Step.alu64 s₀.regs s₀.mem s₀.pc op dst src _ hpc rfl
            exists Steps.step _ _ _ hstep hsteps'
            constructor
            · assumption
            · apply HeapSafe.step
              · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
              · assumption
    | some (Instr.alu32 op dst src) =>
        simp only [hpc] at hint
        let s₁ := { s₀ with
          regs := s₀.regs.set dst (evalAlu32 op (s₀.regs dst) (evalSrc s₀.regs src)),
          pc := s₀.pc + 1 }
        cases ih s₁ hint with
        | intro hsteps' rest =>
          cases rest with
          | intro hexit hsafe' =>
            have hstep : Step prog s₀ s₁ := Step.alu32 s₀.regs s₀.mem s₀.pc op dst src _ hpc rfl
            exists Steps.step _ _ _ hstep hsteps'
            constructor
            · assumption
            · apply HeapSafe.step
              · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
              · assumption
    | some (Instr.neg64 dst) =>
        simp only [hpc] at hint
        let s₁ := { s₀ with regs := s₀.regs.set dst (- s₀.regs dst), pc := s₀.pc + 1 }
        cases ih s₁ hint with
        | intro hsteps' rest =>
          cases rest with
          | intro hexit hsafe' =>
            have hstep : Step prog s₀ s₁ := Step.neg64 s₀.regs s₀.mem s₀.pc dst hpc
            exists Steps.step _ _ _ hstep hsteps'
            constructor
            · assumption
            · apply HeapSafe.step
              · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
              · assumption
    | some (Instr.neg32 dst) =>
        simp only [hpc] at hint
        let s₁ := { s₀ with regs := s₀.regs.set dst (zext32 (- s₀.regs dst)), pc := s₀.pc + 1 }
        cases ih s₁ hint with
        | intro hsteps' rest =>
          cases rest with
          | intro hexit hsafe' =>
            have hstep : Step prog s₀ s₁ := Step.neg32 s₀.regs s₀.mem s₀.pc dst hpc
            exists Steps.step _ _ _ hstep hsteps'
            constructor
            · assumption
            · apply HeapSafe.step
              · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
              · assumption
    | some (Instr.endian e sz dst) =>
        simp only [hpc] at hint
        let s₁ := { s₀ with
          regs := s₀.regs.set dst (evalEndian e sz (s₀.regs dst)), pc := s₀.pc + 1 }
        cases ih s₁ hint with
        | intro hsteps' rest =>
          cases rest with
          | intro hexit hsafe' =>
            have hstep : Step prog s₀ s₁ := Step.endian s₀.regs s₀.mem s₀.pc e sz dst _ hpc rfl
            exists Steps.step _ _ _ hstep hsteps'
            constructor
            · assumption
            · apply HeapSafe.step
              · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
              · assumption
    | some (Instr.ja off) =>
        simp only [hpc] at hint
        split_ifs at hint with hnn
        · let s₁ := { s₀ with pc := ((s₀.pc : Int) + 1 + offset16ToInt off).toNat }
          cases ih s₁ hint with
          | intro hsteps' rest =>
            cases rest with
            | intro hexit hsafe' =>
              have hstep : Step prog s₀ s₁ := Step.ja s₀.regs s₀.mem s₀.pc off _ hpc rfl hnn
              exists Steps.step _ _ _ hstep hsteps'
              constructor
              · assumption
              · apply HeapSafe.step
                · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
                · assumption
    | some (Instr.jmp64 op dst src off) =>
        simp only [hpc] at hint
        by_cases hcond : evalJmp64 op (s₀.regs dst) (evalSrc s₀.regs src) = true
        · simp only [hcond, ite_true] at hint
          split_ifs at hint with hnn
          · let s₁ := { s₀ with pc := ((s₀.pc : Int) + 1 + offset16ToInt off).toNat }
            cases ih s₁ hint with
            | intro hsteps' rest =>
              cases rest with
              | intro hexit hsafe' =>
                have hstep : Step prog s₀ s₁ :=
                  Step.jmp64_taken s₀.regs s₀.mem s₀.pc op dst src off _ hpc hcond rfl hnn
                exists Steps.step _ _ _ hstep hsteps'
                constructor
                · assumption
                · apply HeapSafe.step
                  · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
                  · assumption
        · simp only [Bool.not_eq_true] at hcond
          simp only [hcond] at hint
          let s₁ := { s₀ with pc := s₀.pc + 1 }
          cases ih s₁ hint with
          | intro hsteps' rest =>
            cases rest with
            | intro hexit hsafe' =>
              have hstep : Step prog s₀ s₁ :=
                Step.jmp64_fallthrough s₀.regs s₀.mem s₀.pc op dst src off hpc hcond
              exists Steps.step _ _ _ hstep hsteps'
              constructor
              · assumption
              · apply HeapSafe.step
                · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
                · assumption
    | some (Instr.jmp32 op dst src off) =>
        simp only [hpc] at hint
        by_cases hcond : evalJmp32 op (s₀.regs dst) (evalSrc s₀.regs src) = true
        · simp only [hcond, ite_true] at hint
          split_ifs at hint with hnn
          · let s₁ := { s₀ with pc := ((s₀.pc : Int) + 1 + offset16ToInt off).toNat }
            cases ih s₁ hint with
            | intro hsteps' rest =>
              cases rest with
              | intro hexit hsafe' =>
                have hstep : Step prog s₀ s₁ :=
                  Step.jmp32_taken s₀.regs s₀.mem s₀.pc op dst src off _ hpc hcond rfl hnn
                exists Steps.step _ _ _ hstep hsteps'
                constructor
                · assumption
                · apply HeapSafe.step
                  · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
                  · assumption
        · simp only [Bool.not_eq_true] at hcond
          simp only [hcond] at hint
          let s₁ := { s₀ with pc := s₀.pc + 1 }
          cases ih s₁ hint with
          | intro hsteps' rest =>
            cases rest with
            | intro hexit hsafe' =>
              have hstep : Step prog s₀ s₁ :=
                Step.jmp32_fallthrough s₀.regs s₀.mem s₀.pc op dst src off hpc hcond
              exists Steps.step _ _ _ hstep hsteps'
              constructor
              · assumption
              · apply HeapSafe.step
                · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
                · assumption
    | some (Instr.store sz dst off src) =>
        simp only [hpc] at hint
        let addr := s₀.regs dst + BitVec.signExtend 64 off
        let mem' := writeMem s₀.mem addr (evalSrc s₀.regs src) sz
        let s₁ := { s₀ with mem := mem', pc := s₀.pc + 1 }
        cases ih s₁ hint with
        | intro hsteps' rest =>
          cases rest with
          | intro hexit hsafe' =>
            have hstep : Step prog s₀ s₁ :=
              Step.store s₀.regs s₀.mem s₀.pc sz dst off src addr mem' hpc rfl rfl
            exists Steps.step _ _ _ hstep hsteps'
            constructor
            · assumption
            · apply HeapSafe.step
              · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
              · assumption
    | some (Instr.load sz dst src off) =>
        simp only [hpc] at hint
        let addr := s₀.regs src + BitVec.signExtend 64 off
        let v    := readMem s₀.mem addr sz
        let s₁ := { s₀ with regs := s₀.regs.set dst v, pc := s₀.pc + 1 }
        cases ih s₁ hint with
        | intro hsteps' rest =>
          cases rest with
          | intro hexit hsafe' =>
            have hstep : Step prog s₀ s₁ :=
              Step.load s₀.regs s₀.mem s₀.pc sz dst src off addr v hpc rfl rfl
            exists Steps.step _ _ _ hstep hsteps'
            constructor
            · assumption
            · apply HeapSafe.step
              · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
              · assumption
    | some (Instr.lddw dst imm) =>
        simp only [hpc] at hint
        let s₁ := { s₀ with regs := s₀.regs.set dst imm, pc := s₀.pc + 2 }
        cases ih s₁ hint with
        | intro hsteps' rest =>
          cases rest with
          | intro hexit hsafe' =>
            have hstep : Step prog s₀ s₁ := Step.lddw s₀.regs s₀.mem s₀.pc dst imm hpc
            exists Steps.step _ _ _ hstep hsteps'
            constructor
            · assumption
            · apply HeapSafe.step
              · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
              · assumption
    | some (Instr.atomic sz op fetch dst src off) =>
        simp only [hpc] at hint
        let addr   := s₀.regs dst + BitVec.signExtend 64 off
        let oldVal := readMem s₀.mem addr sz
        let newVal := match op with
          | AtomicOp.add     => oldVal + s₀.regs src
          | AtomicOp.or      => oldVal ||| s₀.regs src
          | AtomicOp.and     => oldVal &&& s₀.regs src
          | AtomicOp.xor     => oldVal ^^^ s₀.regs src
          | AtomicOp.xchg    => s₀.regs src
          | AtomicOp.cmpxchg => if s₀.regs Reg.r0 = oldVal then s₀.regs src else oldVal
        let mem'  := writeMem s₀.mem addr newVal sz
        let regs' := match op with
          | AtomicOp.cmpxchg => s₀.regs.set Reg.r0 oldVal
          | _                => if fetch then s₀.regs.set src oldVal else s₀.regs
        let s₁ := ({ regs := regs', mem := mem', pc := s₀.pc + 1 } : State)
        cases ih s₁ hint with
        | intro hsteps' rest =>
          cases rest with
          | intro hexit hsafe' =>
            have hstep : Step prog s₀ s₁ :=
              Step.atomic_op s₀.regs s₀.mem s₀.pc sz op fetch dst src off
                addr oldVal newVal mem' regs' hpc rfl rfl rfl rfl rfl
            exists Steps.step _ _ _ hstep hsteps'
            constructor
            · assumption
            · apply HeapSafe.step
              · intro ⟨_, hc⟩ _ _; simp [hpc] at hc
              · assumption
    | some (Instr.call fid) =>
        simp only [hpc] at hint
        set regs' := (oracle fid s₀.regs s₀.mem).1 with hregs'_def
        set mem'  := (oracle fid s₀.regs s₀.mem).2 with hmem'_def
        let s₁ := ({ regs := regs', mem := mem', pc := s₀.pc + 1 } : State)
        cases ih s₁ hint with
        | intro hsteps' rest =>
          cases rest with
          | intro hexit hsafe' =>
            have hcallee : ∀ r, r ∈ ([Reg.r6, Reg.r7, Reg.r8, Reg.r9, Reg.r10] : List Reg) →
                regs' r = s₀.regs r :=
              fun r hr => hok fid s₀.regs s₀.mem r hr
            let fp : BitVec 64 → Option (BitVec 8) :=
              fun a => if mem' a = s₀.mem a then none else some (mem' a)
            have hfp : ∀ a, fp a = none → mem' a = s₀.mem a := by
              intro a ha; simp only [fp] at ha
              by_cases heq : mem' a = s₀.mem a
              · exact heq
              · simp only [if_neg heq] at ha; exact absurd ha (by simp)
            have hstep : Step prog s₀ s₁ :=
              Step.call s₀.regs regs' s₀.mem mem' s₀.pc fid fp hpc hcallee hfp
            have hcall_safe : isCallStep hstep → ∀ a, s₁.mem a ≠ s₀.mem a → h a = none :=
              fun _ a hmod => hhs fid s₀.regs s₀.mem a hmod
            exists Steps.step _ _ _ hstep hsteps'
            constructor
            · assumption
            · apply HeapSafe.step
              · exact hcall_safe
              · assumption

theorem sem_triple_interp_sound
    (prog : Program) (pc : ℕ) (P Q : Assert)
    (hst : SemTriple prog pc P Q)
    (oracle : CallOracle)
    (hok : OracleOk oracle)
    (h1 h2 : Heap)
    (s sf : State) (fuel : ℕ)
    (hpc : s.pc = pc)
    (hP : P s.regs h1)
    (hcons : Heap.Consistent (Heap.union h1 h2) s.mem)
    (hdisj : Heap.Disjoint h1 h2)
    (hhs : OracleHeapSafe oracle (Heap.union h1 h2))
    (hint : interp prog oracle s fuel = some sf) :
    ∃ hf1 : Heap,
      Q sf.regs hf1 ∧
      Heap.Consistent (Heap.union hf1 h2) sf.mem ∧
      Heap.Disjoint hf1 h2 := by
  cases interp_heapSafe prog oracle (Heap.union h1 h2) hok hhs fuel s sf hint with
  | intro hsteps rest =>
    cases rest with
    | intro hexit hsafe =>
      apply hst <;> assumption

theorem wf_interp_sound
    (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
    (Q : Assert)
    (hwf : WellFormed prog mapSize callTypes)
    (oracle : CallOracle) (hok : OracleOk oracle)
    (h1 h2 : Heap) (s sf : State) (fuel : ℕ)
    (hpc : s.pc = 0)
    (hP : vcgWP prog Q (prog.size + 1) 0 s.regs h1)
    (hcons : Heap.Consistent (Heap.union h1 h2) s.mem)
    (hdisj : Heap.Disjoint h1 h2)
    (hhs : OracleHeapSafe oracle (Heap.union h1 h2))
    (hint : interp prog oracle s fuel = some sf) :
    ∃ hf1 : Heap,
      Q sf.regs hf1 ∧
      Heap.Consistent (Heap.union hf1 h2) sf.mem ∧
      Heap.Disjoint hf1 h2 :=
  sem_triple_interp_sound prog 0 _ Q (wf_sem_sound prog mapSize callTypes Q hwf)
    oracle hok h1 h2 s sf fuel hpc hP hcons hdisj hhs hint

end Ebpf

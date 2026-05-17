import Ebpf.Semantics

set_option linter.style.emptyLine false

namespace Ebpf

/- Partial heaps -/

abbrev Heap := BitVec 64 → Option (BitVec 8)

def Heap.empty : Heap := fun _ => none

def Heap.Disjoint (h1 h2 : Heap) : Prop :=
  ∀ a, h1 a = none ∨ h2 a = none

def Heap.union (h1 h2 : Heap) : Heap :=
  fun a => (h1 a).orElse (fun _ => h2 a)

def Heap.Consistent (h : Heap) (mem : Memory) : Prop :=
  ∀ a b, h a = some b → mem a = b

def readHeap (h : Heap) (addr : BitVec 64) (sz : Size) : Option (BitVec 64) :=
  match sz with
  | Size.byte => do
      let b ← h addr
      some (BitVec.zeroExtend 64 b)
  | Size.half => do
      let b0 ← h addr
      let b1 ← h (addr + 1)
      some (BitVec.zeroExtend 64 b0 ||| (BitVec.zeroExtend 64 b1 <<< 8))
  | Size.word => do
      let b0 ← h addr
      let b1 ← h (addr + 1)
      let b2 ← h (addr + 2)
      let b3 ← h (addr + 3)
      some (BitVec.zeroExtend 64 b0 ||| (BitVec.zeroExtend 64 b1 <<< 8)  |||
            (BitVec.zeroExtend 64 b2 <<< 16) ||| (BitVec.zeroExtend 64 b3 <<< 24))
  | Size.dword => do
      let b0 ← h addr
      let b1 ← h (addr + 1)
      let b2 ← h (addr + 2)
      let b3 ← h (addr + 3)
      let b4 ← h (addr + 4)
      let b5 ← h (addr + 5)
      let b6 ← h (addr + 6)
      let b7 ← h (addr + 7)
      some (BitVec.zeroExtend 64 b0 ||| (BitVec.zeroExtend 64 b1 <<< 8)  |||
            (BitVec.zeroExtend 64 b2 <<< 16) ||| (BitVec.zeroExtend 64 b3 <<< 24) |||
            (BitVec.zeroExtend 64 b4 <<< 32) ||| (BitVec.zeroExtend 64 b5 <<< 40) |||
            (BitVec.zeroExtend 64 b6 <<< 48) ||| (BitVec.zeroExtend 64 b7 <<< 56))

def writeHeap (h : Heap) (addr : BitVec 64) (sz : Size) (val : BitVec 64) : Heap :=
  match sz with
  | Size.byte  => fun a =>
      if a = addr          then some (BitVec.truncate 8 val) else h a
  | Size.half  => fun a =>
      if a = addr          then some (BitVec.truncate 8 val)
      else if a = addr + 1 then some (BitVec.truncate 8 (val >>> 8))
      else h a
  | Size.word  => fun a =>
      if a = addr          then some (BitVec.truncate 8 val)
      else if a = addr + 1 then some (BitVec.truncate 8 (val >>> 8))
      else if a = addr + 2 then some (BitVec.truncate 8 (val >>> 16))
      else if a = addr + 3 then some (BitVec.truncate 8 (val >>> 24))
      else h a
  | Size.dword => fun a =>
      if a = addr          then some (BitVec.truncate 8 val)
      else if a = addr + 1 then some (BitVec.truncate 8 (val >>> 8))
      else if a = addr + 2 then some (BitVec.truncate 8 (val >>> 16))
      else if a = addr + 3 then some (BitVec.truncate 8 (val >>> 24))
      else if a = addr + 4 then some (BitVec.truncate 8 (val >>> 32))
      else if a = addr + 5 then some (BitVec.truncate 8 (val >>> 40))
      else if a = addr + 6 then some (BitVec.truncate 8 (val >>> 48))
      else if a = addr + 7 then some (BitVec.truncate 8 (val >>> 56))
      else h a

/- Assertions -/

abbrev Assert := RegFile → Heap → Prop

def Assert.HeapOnly (P : Assert) : Prop :=
  ∀ rf rf' h, P rf h → P rf' h

def emp : Assert :=
  fun _ h => h = Heap.empty

def heapPts (addr : BitVec 64) (sz : Size) (val : BitVec 64) : Assert :=
  fun _ h => readHeap h addr sz = some val ∧
    match sz with
    | Size.byte  => ∀ a, a ≠ addr                                           → h a = none
    | Size.half  => ∀ a, a ≠ addr ∧ a ≠ addr+1                             → h a = none
    | Size.word  => ∀ a, a ≠ addr ∧ a ≠ addr+1 ∧ a ≠ addr+2 ∧ a ≠ addr+3 → h a = none
    | Size.dword => ∀ a, a ≠ addr ∧ a ≠ addr+1 ∧ a ≠ addr+2 ∧ a ≠ addr+3 ∧
                         a ≠ addr+4 ∧ a ≠ addr+5 ∧ a ≠ addr+6 ∧ a ≠ addr+7 → h a = none

def regPts (r : Reg) (v : BitVec 64) : Assert :=
  fun rf _ => rf r = v

def Assert.pure (P : Prop) : Assert :=
  fun _ _ => P

def Assert.regs (P : RegFile → Prop) : Assert :=
  fun rf _ => P rf

def Assert.and (P Q : Assert) : Assert := fun rf h => P rf h ∧ Q rf h
def Assert.or (P Q : Assert) : Assert := fun rf h => P rf h ∨ Q rf h
def Assert.not (P : Assert) : Assert := fun rf h => ¬P rf h

def Assert.forall_ {α : Type} (P : α → Assert) : Assert :=
  fun rf h => ∀ x, P x rf h

def Assert.exists_ {α : Type} (P : α → Assert) : Assert :=
  fun rf h => ∃ x, P x rf h

def sepConj (P Q : Assert) : Assert :=
  fun rf h => ∃ h1 h2 : Heap,
    Heap.Disjoint h1 h2 ∧
    Heap.union h1 h2 = h ∧
    P rf h1 ∧ Q rf h2

def sepImp (P Q : Assert) : Assert :=
  fun rf h => ∀ h' : Heap,
    Heap.Disjoint h h' → P rf h' → Q rf (Heap.union h h')

infixr:35 " ⋆ "  => sepConj
infixr:25 " -⋆ " => sepImp

def Assert.Entails (P Q : Assert) : Prop := ∀ rf h, P rf h → Q rf h

notation:20 P " ⊢ₐ " Q => Assert.Entails P Q

/- Weakest-precondition transformers -/

def wp_alu64 (op : AluOp) (dst : Reg) (src : Src) (Q : Assert) : Assert :=
  fun rf h => Q (rf.set dst (evalAlu64 op (rf dst) (evalSrc rf src))) h

def wp_alu32 (op : AluOp) (dst : Reg) (src : Src) (Q : Assert) : Assert :=
  fun rf h => Q (rf.set dst (evalAlu32 op (rf dst) (evalSrc rf src))) h

def wp_neg64 (dst : Reg) (Q : Assert) : Assert :=
  fun rf h => Q (rf.set dst (- rf dst)) h

def wp_neg32 (dst : Reg) (Q : Assert) : Assert :=
  fun rf h => Q (rf.set dst (zext32 (- rf dst))) h

def wp_endian (e : Endian) (sz : Size) (dst : Reg) (Q : Assert) : Assert :=
  fun rf h => Q (rf.set dst (evalEndian e sz (rf dst))) h

def wp_lddw (dst : Reg) (imm : BitVec 64) (Q : Assert) : Assert :=
  fun rf h => Q (rf.set dst imm) h

def wp_load (sz : Size) (dst : Reg) (src_reg : Reg) (off : BitVec 16)
    (Q : Assert) : Assert :=
  fun rf h =>
    let addr := rf src_reg + BitVec.signExtend 64 off
    ∃ v : BitVec 64, readHeap h addr sz = some v ∧ Q (rf.set dst v) h

def wp_store (sz : Size) (dst : Reg) (off : BitVec 16) (src : Src)
    (Q : Assert) : Assert :=
  fun rf h =>
    let addr := rf dst + BitVec.signExtend 64 off
    let val  := evalSrc rf src
    readHeap h addr sz ≠ none ∧
    Q rf (writeHeap h addr sz val)

def wp_jmp64 (op : JmpOp) (dst : Reg) (src : Src)
    (Q_taken Q_fall : Assert) : Assert :=
  fun rf h =>
    (evalJmp64 op (rf dst) (evalSrc rf src) = true  → Q_taken rf h) ∧
    (evalJmp64 op (rf dst) (evalSrc rf src) = false → Q_fall  rf h)

def wp_jmp32 (op : JmpOp) (dst : Reg) (src : Src)
    (Q_taken Q_fall : Assert) : Assert :=
  fun rf h =>
    (evalJmp32 op (rf dst) (evalSrc rf src) = true  → Q_taken rf h) ∧
    (evalJmp32 op (rf dst) (evalSrc rf src) = false → Q_fall  rf h)

def wp_call (Q : Assert) : Assert :=
  fun rf h =>
    ∀ (rf' : RegFile) (mem' : Memory),
      Heap.Consistent h mem' →
      (∀ r, r ∈ ([Reg.r6, Reg.r7, Reg.r8, Reg.r9, Reg.r10] : List Reg) →
            rf' r = rf r) →
      Q rf' h

def wp_atomic (sz : Size) (op : AtomicOp) (fetch : Bool)
    (dst src : Reg) (off : BitVec 16) (Q : Assert) : Assert :=
  fun rf h =>
    let addr    := rf dst + BitVec.signExtend 64 off
    ∃ old_val : BitVec 64,
      readHeap h addr sz = some old_val ∧
      let new_val :=
        match op with
        | AtomicOp.add     => old_val + rf src
        | AtomicOp.or      => old_val ||| rf src
        | AtomicOp.and     => old_val &&& rf src
        | AtomicOp.xor     => old_val ^^^ rf src
        | AtomicOp.xchg    => rf src
        | AtomicOp.cmpxchg => if rf Reg.r0 = old_val then rf src else old_val
      let h'  := writeHeap h addr sz new_val
      let rf' :=
        match op with
        | AtomicOp.cmpxchg => rf.set Reg.r0 old_val
        | _                => if fetch then rf.set src old_val else rf
      Q rf' h'

/- Hoare triples -/

inductive HTriple (prog : Program) : ℕ → Assert → Assert → Prop where
  | consequence :
      ∀ (pc : ℕ) (P P' Q Q' : Assert),
      (P' ⊢ₐ P) →
      HTriple prog pc P Q →
      (Q ⊢ₐ Q') →
      HTriple prog pc P' Q'
  | frame :
      ∀ (pc : ℕ) (P Q R : Assert),
      Assert.HeapOnly R →
      HTriple prog pc P Q →

      HTriple prog pc (P ⋆ R) (Q ⋆ R)
  | disj :
      ∀ (pc : ℕ) (P1 P2 Q : Assert),
      HTriple prog pc P1 Q →
      HTriple prog pc P2 Q →
      HTriple prog pc (P1.or P2) Q
  | exists_ :
      ∀ {α : Type} (pc : ℕ) (P : α → Assert) (Q : Assert),
      (∀ x : α, HTriple prog pc (P x) Q) →
      HTriple prog pc (Assert.exists_ P) Q
  | exit :
      ∀ (pc : ℕ) (Q : Assert),
      prog[pc]? = some Instr.exit →
      HTriple prog pc Q Q
  | alu64 :
      ∀ (pc : ℕ) (op : AluOp) (dst : Reg) (src : Src) (R Q : Assert),
      prog[pc]? = some (Instr.alu64 op dst src) →
      HTriple prog (pc + 1) R Q →
      HTriple prog pc (wp_alu64 op dst src R) Q
  | alu32 :
      ∀ (pc : ℕ) (op : AluOp) (dst : Reg) (src : Src) (R Q : Assert),
      prog[pc]? = some (Instr.alu32 op dst src) →
      HTriple prog (pc + 1) R Q →
      HTriple prog pc (wp_alu32 op dst src R) Q
  | neg64 :
      ∀ (pc : ℕ) (dst : Reg) (R Q : Assert),
      prog[pc]? = some (Instr.neg64 dst) →
      HTriple prog (pc + 1) R Q →
      HTriple prog pc (wp_neg64 dst R) Q
  | neg32 :
      ∀ (pc : ℕ) (dst : Reg) (R Q : Assert),
      prog[pc]? = some (Instr.neg32 dst) →
      HTriple prog (pc + 1) R Q →
      HTriple prog pc (wp_neg32 dst R) Q
  | endian :
      ∀ (pc : ℕ) (e : Endian) (sz : Size) (dst : Reg) (R Q : Assert),
      prog[pc]? = some (Instr.endian e sz dst) →
      HTriple prog (pc + 1) R Q →
      HTriple prog pc (wp_endian e sz dst R) Q
  | ja :
      ∀ (pc : ℕ) (off : BitVec 16) (pc' : Int) (R Q : Assert),
      prog[pc]? = some (Instr.ja off) →
      pc' = (pc : Int) + 1 + offset16ToInt off →
      0 ≤ pc' →
      HTriple prog pc'.toNat R Q →
      HTriple prog pc R Q
  | jmp64 :
      ∀ (pc : ℕ) (op : JmpOp) (dst : Reg) (src : Src)
        (off : BitVec 16) (pc' : Int) (R_taken R_fall Q : Assert),
      prog[pc]? = some (Instr.jmp64 op dst src off) →
      pc' = (pc : Int) + 1 + offset16ToInt off →
      0 ≤ pc' →
      HTriple prog pc'.toNat R_taken Q →
      HTriple prog (pc + 1) R_fall Q →
      HTriple prog pc (wp_jmp64 op dst src R_taken R_fall) Q
  | jmp32 :
      ∀ (pc : ℕ) (op : JmpOp) (dst : Reg) (src : Src)
        (off : BitVec 16) (pc' : Int) (R_taken R_fall Q : Assert),
      prog[pc]? = some (Instr.jmp32 op dst src off) →
      pc' = (pc : Int) + 1 + offset16ToInt off →
      0 ≤ pc' →
      HTriple prog pc'.toNat R_taken Q →
      HTriple prog (pc + 1) R_fall Q →
      HTriple prog pc (wp_jmp32 op dst src R_taken R_fall) Q
  | load :
      ∀ (pc : ℕ) (sz : Size) (dst : Reg) (src_reg : Reg)
        (off : BitVec 16) (R Q : Assert),
      prog[pc]? = some (Instr.load sz dst src_reg off) →
      HTriple prog (pc + 1) R Q →
      HTriple prog pc (wp_load sz dst src_reg off R) Q
  | store :
      ∀ (pc : ℕ) (sz : Size) (dst : Reg) (off : BitVec 16)
        (src : Src) (R Q : Assert),
      prog[pc]? = some (Instr.store sz dst off src) →
      HTriple prog (pc + 1) R Q →
      HTriple prog pc (wp_store sz dst off src R) Q
  | lddw :
      ∀ (pc : ℕ) (dst : Reg) (imm : BitVec 64) (R Q : Assert),
      prog[pc]? = some (Instr.lddw dst imm) →
      HTriple prog (pc + 2) R Q →
      HTriple prog pc (wp_lddw dst imm R) Q
  | atomic :
      ∀ (pc : ℕ) (sz : Size) (op : AtomicOp) (fetch : Bool)
        (dst src : Reg) (off : BitVec 16) (R Q : Assert),
      prog[pc]? = some (Instr.atomic sz op fetch dst src off) →
      HTriple prog (pc + 1) R Q →
      HTriple prog pc (wp_atomic sz op fetch dst src off R) Q
  | call :
      ∀ (pc : ℕ) (fid : BitVec 32) (R Q : Assert),
      prog[pc]? = some (Instr.call fid) →
      HTriple prog (pc + 1) R Q →
      HTriple prog pc (wp_call R) Q

end Ebpf

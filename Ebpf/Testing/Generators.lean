import Ebpf.Semantics
import Plausible.Testable

namespace Ebpf.Testing

open Ebpf Plausible Gen

structure RegFileRec where
  r0  : BitVec 64
  r1  : BitVec 64
  r2  : BitVec 64
  r3  : BitVec 64
  r4  : BitVec 64
  r5  : BitVec 64
  r6  : BitVec 64
  r7  : BitVec 64
  r8  : BitVec 64
  r9  : BitVec 64
  r10 : BitVec 64
  deriving Repr

def RegFileRec.toRegFile (r : RegFileRec) : RegFile := fun reg =>
  match reg with
  | Reg.r0  => r.r0  | Reg.r1  => r.r1  | Reg.r2  => r.r2
  | Reg.r3  => r.r3  | Reg.r4  => r.r4  | Reg.r5  => r.r5
  | Reg.r6  => r.r6  | Reg.r7  => r.r7  | Reg.r8  => r.r8
  | Reg.r9  => r.r9  | Reg.r10 => r.r10

structure MemPatch where
  entries : List (BitVec 64 × BitVec 8)
  deriving Repr

def MemPatch.toMemory (p : MemPatch) : Memory :=
  fun addr =>
    match p.entries.find? (·.1 == addr) with
    | some (_, b) => b
    | none        => 0

def zeroMem : Memory := fun _ => 0

structure StraightLineProg where
  instrs : List Instr
  deriving Repr

def StraightLineProg.toProgram (p : StraightLineProg) : Program :=
  p.instrs.toArray.push Instr.exit

meta section


instance : Shrinkable Reg := ⟨fun _ => []⟩
instance : Arbitrary Reg where
  arbitrary := elements
    [Reg.r0, Reg.r1, Reg.r2, Reg.r3, Reg.r4, Reg.r5,
     Reg.r6, Reg.r7, Reg.r8, Reg.r9, Reg.r10] (by decide)

instance : Shrinkable Size := ⟨fun _ => []⟩
instance : Arbitrary Size where
  arbitrary := elements [Size.byte, Size.half, Size.word, Size.dword] (by decide)

instance : Shrinkable AluOp := ⟨fun _ => []⟩
instance : Arbitrary AluOp where
  arbitrary := elements
    [AluOp.add, AluOp.sub, AluOp.mul, AluOp.div, AluOp.mod,
     AluOp.or, AluOp.and, AluOp.xor, AluOp.mov] (by decide)

instance : Shrinkable JmpOp := ⟨fun _ => []⟩
instance : Arbitrary JmpOp where
  arbitrary := elements
    [JmpOp.jeq, JmpOp.jne, JmpOp.jgt, JmpOp.jge, JmpOp.jlt, JmpOp.jle,
     JmpOp.jsgt, JmpOp.jsge, JmpOp.jslt, JmpOp.jsle, JmpOp.jset] (by decide)

instance : Shrinkable AtomicOp := ⟨fun _ => []⟩
instance : Arbitrary AtomicOp where
  arbitrary := elements
    [AtomicOp.add, AtomicOp.or, AtomicOp.and, AtomicOp.xor,
     AtomicOp.xchg, AtomicOp.cmpxchg] (by decide)

instance : Shrinkable Endian := ⟨fun _ => []⟩
instance : Arbitrary Endian where
  arbitrary := elements [Endian.le, Endian.be] (by decide)

instance : Shrinkable Src := ⟨fun _ => []⟩
instance : Arbitrary Src where
  arbitrary := do
    match ← chooseAny Bool with
    | true  => pure (Src.reg (← Arbitrary.arbitrary))
    | false => pure (Src.imm (← Arbitrary.arbitrary))

instance : Shrinkable RegFileRec := ⟨fun _ => []⟩
instance : Arbitrary RegFileRec where
  arbitrary := do
    pure { r0  := ← Arbitrary.arbitrary, r1  := ← Arbitrary.arbitrary
         , r2  := ← Arbitrary.arbitrary, r3  := ← Arbitrary.arbitrary
         , r4  := ← Arbitrary.arbitrary, r5  := ← Arbitrary.arbitrary
         , r6  := ← Arbitrary.arbitrary, r7  := ← Arbitrary.arbitrary
         , r8  := ← Arbitrary.arbitrary, r9  := ← Arbitrary.arbitrary
         , r10 := ← Arbitrary.arbitrary }

instance : Shrinkable MemPatch where
  shrink p := match p.entries with
    | []     => []
    | _ :: t => [⟨t⟩]

instance : Arbitrary MemPatch where
  arbitrary := do
    let entries ← listOf (prodOf Arbitrary.arbitrary Arbitrary.arbitrary)
    pure ⟨entries⟩

def genStraightLineInstr : Gen Instr :=
  backtrack
    [ (2, do pure (Instr.alu64 (← Arbitrary.arbitrary) (← Arbitrary.arbitrary) (← Arbitrary.arbitrary)))
    , (2, do pure (Instr.alu32 (← Arbitrary.arbitrary) (← Arbitrary.arbitrary) (← Arbitrary.arbitrary)))
    , (1, do pure (Instr.neg64 (← Arbitrary.arbitrary)))
    , (1, do pure (Instr.neg32 (← Arbitrary.arbitrary)))
    , (1, do pure (Instr.endian (← Arbitrary.arbitrary) (← Arbitrary.arbitrary) (← Arbitrary.arbitrary)))
    , (1, do pure (Instr.load  (← Arbitrary.arbitrary) (← Arbitrary.arbitrary) (← Arbitrary.arbitrary) (← Arbitrary.arbitrary)))
    , (1, do pure (Instr.lddw  (← Arbitrary.arbitrary) (← Arbitrary.arbitrary)))
    ]

instance : Shrinkable StraightLineProg where
  shrink p := match p.instrs with
    | []     => []
    | _ :: t => [⟨t⟩]

instance : Arbitrary StraightLineProg where
  arbitrary := do
    let instrs ← listOf genStraightLineInstr
    pure ⟨instrs⟩

end  -- meta section

end Ebpf.Testing

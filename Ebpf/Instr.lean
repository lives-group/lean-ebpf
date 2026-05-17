import Mathlib.Data.BitVec

namespace Ebpf

/-- eBPF registers -/
inductive Reg : Type where
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10
  deriving DecidableEq, Repr

/-- Memory access sizes -/
inductive Size : Type where
  | byte    -- 1 byte  (BPF_B)
  | half    -- 2 bytes (BPF_H)
  | word    -- 4 bytes (BPF_W)
  | dword   -- 8 bytes (BPF_DW)
  deriving DecidableEq, Repr

/-- Binary ALU operations -/
inductive AluOp : Type where
  | add | sub | mul | div | mod
  | or  | and | xor
  | lsh | rsh | arsh
  | mov
  deriving DecidableEq, Repr

/-- Source operand -/
inductive Src : Type where
  | reg (r : Reg)
  | imm (i : BitVec 32)
  deriving DecidableEq, Repr

/-- Byte-swap endianness -/
inductive Endian : Type where
  | le | be
  deriving DecidableEq, Repr

/-- Jump condition -/
inductive JmpOp : Type where
  | jeq | jne
  | jgt | jge | jlt | jle          -- unsigned
  | jsgt | jsge | jslt | jsle       -- signed
  | jset                             -- bitwise AND test
  deriving DecidableEq, Repr

/-- Atomic fetch-and-modify operations -/
inductive AtomicOp : Type where
  | add | or | and | xor
  | xchg                             -- exchange
  | cmpxchg                          -- compare-and-swap (uses R0)
  deriving DecidableEq, Repr

/-- eBPF instructions. -/
inductive Instr : Type where
  | alu64 (op : AluOp) (dst : Reg) (src : Src)
  | alu32 (op : AluOp) (dst : Reg) (src : Src)
  | neg64 (dst : Reg)
  | neg32 (dst : Reg)
  | endian (e : Endian) (width : Size) (dst : Reg)
  | ja (offset : BitVec 16)
  | jmp64 (op : JmpOp) (dst : Reg) (src : Src) (offset : BitVec 16)
  | jmp32 (op : JmpOp) (dst : Reg) (src : Src) (offset : BitVec 16)
  | call (imm : BitVec 32)
  | exit
  | store (sz : Size) (dst : Reg) (offset : BitVec 16) (src : Src)
  | load (sz : Size) (dst : Reg) (src : Reg) (offset : BitVec 16)
  | lddw (dst : Reg) (imm : BitVec 64)
  | atomic (sz : Size) (op : AtomicOp) (fetch : Bool) (dst : Reg) (src : Reg) (offset : BitVec 16)
  deriving DecidableEq, Repr

abbrev Program := Array Instr

end Ebpf

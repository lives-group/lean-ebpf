import Ebpf.Testing.Oracle

namespace Ebpf.Testing

open Ebpf Plausible


def run (prog : Program) (s : State) : Option State :=
  interp prog trivialOracle s (prog.size * 3 + 10)


def prop_alu64_correct (op : AluOp) (dst : Reg) (src : Src) (rf : RegFileRec) : Bool :=
  let regs := rf.toRegFile
  let prog : Program := #[Instr.alu64 op dst src, Instr.exit]
  let s₀ : State := { regs, mem := zeroMem, pc := 0 }
  match run prog s₀ with
  | none    => false
  | some sf => sf.regs dst == evalAlu64 op (regs dst) (evalSrc regs src)

#test ∀ (op : AluOp) (dst : Reg) (src : Src) (rf : RegFileRec), prop_alu64_correct op dst src rf = true


def prop_alu32_correct (op : AluOp) (dst : Reg) (src : Src) (rf : RegFileRec) : Bool :=
  let regs := rf.toRegFile
  let prog : Program := #[Instr.alu32 op dst src, Instr.exit]
  let s₀ : State := { regs, mem := zeroMem, pc := 0 }
  match run prog s₀ with
  | none    => false
  | some sf => sf.regs dst == evalAlu32 op (regs dst) (evalSrc regs src)

#test ∀ (op : AluOp) (dst : Reg) (src : Src) (rf : RegFileRec), prop_alu32_correct op dst src rf = true


def prop_lddw_correct (dst : Reg) (imm : BitVec 64) (rf : RegFileRec) : Bool :=
  let regs := rf.toRegFile
  let prog : Program := #[Instr.lddw dst imm, Instr.exit, Instr.exit]
  let s₀ : State := { regs, mem := zeroMem, pc := 0 }
  match run prog s₀ with
  | none    => false
  | some sf => sf.regs dst == imm

#test ∀ (dst : Reg) (imm : BitVec 64) (rf : RegFileRec), prop_lddw_correct dst imm rf = true

def prop_neg64_involution (dst : Reg) (rf : RegFileRec) : Bool :=
  let regs := rf.toRegFile
  let prog : Program := #[Instr.neg64 dst, Instr.neg64 dst, Instr.exit]
  let s₀ : State := { regs, mem := zeroMem, pc := 0 }
  match run prog s₀ with
  | none    => false
  | some sf => sf.regs dst == regs dst

#test ∀ (dst : Reg) (rf : RegFileRec), prop_neg64_involution dst rf = true

def prop_store_load_byte_roundtrip
    (addr : BitVec 64) (val : BitVec 64) (rf : RegFileRec) : Bool :=
  let regs := (rf.toRegFile.set Reg.r1 addr).set Reg.r2 val
  let prog : Program :=
    #[ Instr.store Size.byte Reg.r1 0 (Src.reg Reg.r2)
     , Instr.load  Size.byte Reg.r0 Reg.r1 0
     , Instr.exit ]
  let s₀ : State := { regs, mem := zeroMem, pc := 0 }
  match run prog s₀ with
  | none    => false
  | some sf => sf.regs Reg.r0 == BitVec.zeroExtend 64 (BitVec.truncate 8 val)

#test ∀ (addr val : BitVec 64) (rf : RegFileRec), prop_store_load_byte_roundtrip addr val rf = true

def prop_callee_saved (rf : RegFileRec) : Bool :=
  let regs := rf.toRegFile
  let prog : Program := #[Instr.call 0, Instr.exit]
  let s₀ : State := { regs, mem := zeroMem, pc := 0 }
  match run prog s₀ with
  | none    => false
  | some sf =>
    [Reg.r6, Reg.r7, Reg.r8, Reg.r9, Reg.r10].all (fun r => sf.regs r == regs r)

#test ∀ (rf : RegFileRec), prop_callee_saved rf = true

def prop_deterministic (prog : StraightLineProg) (rf : RegFileRec) (patch : MemPatch) : Bool :=
  let p := prog.toProgram
  let s₀ : State := { regs := rf.toRegFile, mem := patch.toMemory, pc := 0 }
  let fuel := p.size * 3 + 10
  let r1 := (interp p trivialOracle s₀ fuel).map (·.pc)
  let r2 := (interp p trivialOracle s₀ fuel).map (·.pc)
  r1 == r2

#test ∀ (prog : StraightLineProg) (rf : RegFileRec) (patch : MemPatch),
    prop_deterministic prog rf patch = true

def prop_alu64_other_regs_unchanged
    (op : AluOp) (dst r : Reg) (src : Src) (rf : RegFileRec) : Bool :=
  if dst == r then true
  else
    let regs := rf.toRegFile
    let prog : Program := #[Instr.alu64 op dst src, Instr.exit]
    let s₀ : State := { regs, mem := zeroMem, pc := 0 }
    match run prog s₀ with
    | none    => false
    | some sf => sf.regs r == regs r

#test ∀ (op : AluOp) (dst r : Reg) (src : Src) (rf : RegFileRec),
    prop_alu64_other_regs_unchanged op dst r src rf = true

def prop_alu_mem_preserved
    (op : AluOp) (dst : Reg) (src : Src)
    (rf : RegFileRec) (patch : MemPatch) (probe : BitVec 64) : Bool :=
  let mem₀ := patch.toMemory
  let prog : Program := #[Instr.alu64 op dst src, Instr.exit]
  let s₀ : State := { regs := rf.toRegFile, mem := mem₀, pc := 0 }
  match run prog s₀ with
  | none    => false
  | some sf => sf.mem probe == mem₀ probe

#test ∀ (op : AluOp) (dst : Reg) (src : Src)
    (rf : RegFileRec) (patch : MemPatch) (probe : BitVec 64),
    prop_alu_mem_preserved op dst src rf patch probe = true

def prop_interp_stops_at_exit (prog : StraightLineProg) (rf : RegFileRec) (patch : MemPatch) : Bool :=
  let p := prog.toProgram
  let s₀ : State := { regs := rf.toRegFile, mem := patch.toMemory, pc := 0 }
  match run p s₀ with
  | none    => true   -- divergence: not a counterexample
  | some sf => p[sf.pc]? == some Instr.exit

#test ∀ (prog : StraightLineProg) (rf : RegFileRec) (patch : MemPatch),
    prop_interp_stops_at_exit prog rf patch = true

end Ebpf.Testing

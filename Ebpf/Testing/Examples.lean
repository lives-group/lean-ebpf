import Ebpf.Testing.Oracle

namespace Ebpf.Testing.Examples

open Ebpf Ebpf.Testing

def run (prog : Program) (s : State) : Option State :=
  interp prog trivialOracle s (prog.size * 3 + 10)

def zeroRegs : RegFile := fun _ => 0

def addProg : Program :=
  #[ Instr.alu64 AluOp.add Reg.r0 (Src.reg Reg.r2), Instr.exit ]

def addState : State :=
  { regs := RegFile.set (RegFile.set zeroRegs Reg.r0 3) Reg.r2 7
  , mem  := zeroMem
  , pc   := 0 }

#eval do
  match run addProg addState with
  | none    => IO.println "Did not terminate"
  | some sf => IO.println s!"r0 = {sf.regs Reg.r0}"   -- expected: 10

def storeLoadProg : Program :=
  #[ Instr.store Size.byte Reg.r1 0 (Src.reg Reg.r2)
   , Instr.load  Size.byte Reg.r0 Reg.r1 0
   , Instr.exit ]

def storeLoadState : State :=
  { regs := RegFile.set (RegFile.set zeroRegs Reg.r1 0x1000) Reg.r2 0xAB
  , mem  := zeroMem
  , pc   := 0 }

#eval do
  match run storeLoadProg storeLoadState with
  | none    => IO.println "Did not terminate"
  | some sf => IO.println s!"r0 = {sf.regs Reg.r0}"   -- expected: 171 (0xAB)

def callProg : Program := #[ Instr.call 42, Instr.exit ]

def callRegs : RegFile :=
  zeroRegs
    |> (RegFile.set · Reg.r6 0x600)
    |> (RegFile.set · Reg.r7 0x700)
    |> (RegFile.set · Reg.r8 0x800)
    |> (RegFile.set · Reg.r9 0x900)
    |> (RegFile.set · Reg.r10 0xa00)

#eval do
  let s₀ : State := { regs := callRegs, mem := zeroMem, pc := 0 }
  match run callProg s₀ with
  | none    => IO.println "Did not terminate"
  | some sf =>
    let ok := [Reg.r6, Reg.r7, Reg.r8, Reg.r9, Reg.r10].all
                (fun r => sf.regs r == callRegs r)
    IO.println s!"callee-saved preserved: {ok}"   -- expected: true

def negProg : Program :=
  #[ Instr.neg64 Reg.r0, Instr.neg64 Reg.r0, Instr.exit ]

#eval do
  let v : BitVec 64 := 0xCAFE
  let s₀ : State := { regs := RegFile.set zeroRegs Reg.r0 v, mem := zeroMem, pc := 0 }
  match run negProg s₀ with
  | none    => IO.println "Did not terminate"
  | some sf => IO.println s!"involution ok: {sf.regs Reg.r0 == v}"   -- expected: true

def lddwProg : Program :=
  #[ Instr.lddw Reg.r0 0xDEADBEEFCAFEBABE, Instr.exit, Instr.exit ]

#eval do
  let s₀ : State := { regs := zeroRegs, mem := zeroMem, pc := 0 }
  match run lddwProg s₀ with
  | none    => IO.println "Did not terminate"
  | some sf => IO.println s!"r0 = {sf.regs Reg.r0}"

end Ebpf.Testing.Examples

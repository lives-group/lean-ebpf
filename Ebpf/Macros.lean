import Ebpf.Instr

set_option linter.style.longLine false

namespace Ebpf

scoped notation "r0"  => Reg.r0
scoped notation "r1"  => Reg.r1
scoped notation "r2"  => Reg.r2
scoped notation "r3"  => Reg.r3
scoped notation "r4"  => Reg.r4
scoped notation "r5"  => Reg.r5
scoped notation "r6"  => Reg.r6
scoped notation "r7"  => Reg.r7
scoped notation "r8"  => Reg.r8
scoped notation "r9"  => Reg.r9
scoped notation "r10" => Reg.r10

def bpfOff (n : Int) : BitVec 16 :=
  BitVec.ofNat 16 (((n % (2 ^ 16 : Int) + 2 ^ 16) % 2 ^ 16).toNat)


scoped macro "add64"  d:ident ", " s:ident : term => `(Instr.alu64 .add  $d (Src.reg $s))
scoped macro "add64"  d:ident ", " s:num   : term => `(Instr.alu64 .add  $d (Src.imm ($s : BitVec 32)))
scoped macro "sub64"  d:ident ", " s:ident : term => `(Instr.alu64 .sub  $d (Src.reg $s))
scoped macro "sub64"  d:ident ", " s:num   : term => `(Instr.alu64 .sub  $d (Src.imm ($s : BitVec 32)))
scoped macro "mul64"  d:ident ", " s:ident : term => `(Instr.alu64 .mul  $d (Src.reg $s))
scoped macro "mul64"  d:ident ", " s:num   : term => `(Instr.alu64 .mul  $d (Src.imm ($s : BitVec 32)))
scoped macro "div64"  d:ident ", " s:ident : term => `(Instr.alu64 .div  $d (Src.reg $s))
scoped macro "div64"  d:ident ", " s:num   : term => `(Instr.alu64 .div  $d (Src.imm ($s : BitVec 32)))
scoped macro "mod64"  d:ident ", " s:ident : term => `(Instr.alu64 .mod  $d (Src.reg $s))
scoped macro "mod64"  d:ident ", " s:num   : term => `(Instr.alu64 .mod  $d (Src.imm ($s : BitVec 32)))
scoped macro "or64"   d:ident ", " s:ident : term => `(Instr.alu64 .or   $d (Src.reg $s))
scoped macro "or64"   d:ident ", " s:num   : term => `(Instr.alu64 .or   $d (Src.imm ($s : BitVec 32)))
scoped macro "and64"  d:ident ", " s:ident : term => `(Instr.alu64 .and  $d (Src.reg $s))
scoped macro "and64"  d:ident ", " s:num   : term => `(Instr.alu64 .and  $d (Src.imm ($s : BitVec 32)))
scoped macro "xor64"  d:ident ", " s:ident : term => `(Instr.alu64 .xor  $d (Src.reg $s))
scoped macro "xor64"  d:ident ", " s:num   : term => `(Instr.alu64 .xor  $d (Src.imm ($s : BitVec 32)))
scoped macro "lsh64"  d:ident ", " s:ident : term => `(Instr.alu64 .lsh  $d (Src.reg $s))
scoped macro "lsh64"  d:ident ", " s:num   : term => `(Instr.alu64 .lsh  $d (Src.imm ($s : BitVec 32)))
scoped macro "rsh64"  d:ident ", " s:ident : term => `(Instr.alu64 .rsh  $d (Src.reg $s))
scoped macro "rsh64"  d:ident ", " s:num   : term => `(Instr.alu64 .rsh  $d (Src.imm ($s : BitVec 32)))
scoped macro "arsh64" d:ident ", " s:ident : term => `(Instr.alu64 .arsh $d (Src.reg $s))
scoped macro "arsh64" d:ident ", " s:num   : term => `(Instr.alu64 .arsh $d (Src.imm ($s : BitVec 32)))
scoped macro "mov64"  d:ident ", " s:ident : term => `(Instr.alu64 .mov  $d (Src.reg $s))
scoped macro "mov64"  d:ident ", " s:num   : term => `(Instr.alu64 .mov  $d (Src.imm ($s : BitVec 32)))

scoped macro "neg64" d:ident : term => `(Instr.neg64 $d)


scoped macro "add32"  d:ident ", " s:ident : term => `(Instr.alu32 .add  $d (Src.reg $s))
scoped macro "add32"  d:ident ", " s:num   : term => `(Instr.alu32 .add  $d (Src.imm ($s : BitVec 32)))
scoped macro "sub32"  d:ident ", " s:ident : term => `(Instr.alu32 .sub  $d (Src.reg $s))
scoped macro "sub32"  d:ident ", " s:num   : term => `(Instr.alu32 .sub  $d (Src.imm ($s : BitVec 32)))
scoped macro "mul32"  d:ident ", " s:ident : term => `(Instr.alu32 .mul  $d (Src.reg $s))
scoped macro "mul32"  d:ident ", " s:num   : term => `(Instr.alu32 .mul  $d (Src.imm ($s : BitVec 32)))
scoped macro "div32"  d:ident ", " s:ident : term => `(Instr.alu32 .div  $d (Src.reg $s))
scoped macro "div32"  d:ident ", " s:num   : term => `(Instr.alu32 .div  $d (Src.imm ($s : BitVec 32)))
scoped macro "mod32"  d:ident ", " s:ident : term => `(Instr.alu32 .mod  $d (Src.reg $s))
scoped macro "mod32"  d:ident ", " s:num   : term => `(Instr.alu32 .mod  $d (Src.imm ($s : BitVec 32)))
scoped macro "or32"   d:ident ", " s:ident : term => `(Instr.alu32 .or   $d (Src.reg $s))
scoped macro "or32"   d:ident ", " s:num   : term => `(Instr.alu32 .or   $d (Src.imm ($s : BitVec 32)))
scoped macro "and32"  d:ident ", " s:ident : term => `(Instr.alu32 .and  $d (Src.reg $s))
scoped macro "and32"  d:ident ", " s:num   : term => `(Instr.alu32 .and  $d (Src.imm ($s : BitVec 32)))
scoped macro "xor32"  d:ident ", " s:ident : term => `(Instr.alu32 .xor  $d (Src.reg $s))
scoped macro "xor32"  d:ident ", " s:num   : term => `(Instr.alu32 .xor  $d (Src.imm ($s : BitVec 32)))
scoped macro "lsh32"  d:ident ", " s:ident : term => `(Instr.alu32 .lsh  $d (Src.reg $s))
scoped macro "lsh32"  d:ident ", " s:num   : term => `(Instr.alu32 .lsh  $d (Src.imm ($s : BitVec 32)))
scoped macro "rsh32"  d:ident ", " s:ident : term => `(Instr.alu32 .rsh  $d (Src.reg $s))
scoped macro "rsh32"  d:ident ", " s:num   : term => `(Instr.alu32 .rsh  $d (Src.imm ($s : BitVec 32)))
scoped macro "arsh32" d:ident ", " s:ident : term => `(Instr.alu32 .arsh $d (Src.reg $s))
scoped macro "arsh32" d:ident ", " s:num   : term => `(Instr.alu32 .arsh $d (Src.imm ($s : BitVec 32)))
scoped macro "mov32"  d:ident ", " s:ident : term => `(Instr.alu32 .mov  $d (Src.reg $s))
scoped macro "mov32"  d:ident ", " s:num   : term => `(Instr.alu32 .mov  $d (Src.imm ($s : BitVec 32)))

scoped macro "neg32" d:ident : term => `(Instr.neg32 $d)

scoped macro "le32" d:ident : term => `(Instr.endian .le .word  $d)
scoped macro "le64" d:ident : term => `(Instr.endian .le .dword $d)
scoped macro "be16" d:ident : term => `(Instr.endian .be .half  $d)
scoped macro "be32" d:ident : term => `(Instr.endian .be .word  $d)
scoped macro "be64" d:ident : term => `(Instr.endian .be .dword $d)

scoped macro "ja " o:num : term => `(Instr.ja ($o : BitVec 16))

scoped macro "jeq64"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp64 .jeq  $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jeq64"  d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp64 .jeq  $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jne64"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp64 .jne  $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jne64"  d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp64 .jne  $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jgt64"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp64 .jgt  $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jgt64"  d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp64 .jgt  $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jge64"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp64 .jge  $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jge64"  d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp64 .jge  $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jlt64"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp64 .jlt  $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jlt64"  d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp64 .jlt  $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jle64"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp64 .jle  $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jle64"  d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp64 .jle  $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jsgt64" d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp64 .jsgt $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jsgt64" d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp64 .jsgt $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jsge64" d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp64 .jsge $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jsge64" d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp64 .jsge $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jslt64" d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp64 .jslt $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jslt64" d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp64 .jslt $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jsle64" d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp64 .jsle $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jsle64" d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp64 .jsle $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jset64" d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp64 .jset $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jset64" d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp64 .jset $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))

scoped macro "jeq32"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp32 .jeq  $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jeq32"  d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp32 .jeq  $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jne32"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp32 .jne  $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jne32"  d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp32 .jne  $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jgt32"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp32 .jgt  $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jgt32"  d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp32 .jgt  $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jge32"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp32 .jge  $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jge32"  d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp32 .jge  $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jlt32"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp32 .jlt  $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jlt32"  d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp32 .jlt  $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jle32"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp32 .jle  $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jle32"  d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp32 .jle  $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jsgt32" d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp32 .jsgt $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jsgt32" d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp32 .jsgt $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jsge32" d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp32 .jsge $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jsge32" d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp32 .jsge $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jslt32" d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp32 .jslt $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jslt32" d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp32 .jslt $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jsle32" d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp32 .jsle $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jsle32" d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp32 .jsle $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))
scoped macro "jset32" d:ident ", " s:ident ", " o:num : term =>
  `(Instr.jmp32 .jset $d (Src.reg $s) ($o : BitVec 16))
scoped macro "jset32" d:ident ", " s:num   ", " o:num : term =>
  `(Instr.jmp32 .jset $d (Src.imm ($s : BitVec 32)) ($o : BitVec 16))

scoped macro "ldxb"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.load .byte  $d $s ($o : BitVec 16))
scoped macro "ldxh"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.load .half  $d $s ($o : BitVec 16))
scoped macro "ldxw"  d:ident ", " s:ident ", " o:num : term =>
  `(Instr.load .word  $d $s ($o : BitVec 16))
scoped macro "ldxdw" d:ident ", " s:ident ", " o:num : term =>
  `(Instr.load .dword $d $s ($o : BitVec 16))

scoped macro "stxb"  d:ident ", " o:num ", " s:ident : term =>
  `(Instr.store .byte  $d ($o : BitVec 16) (Src.reg $s))
scoped macro "stxh"  d:ident ", " o:num ", " s:ident : term =>
  `(Instr.store .half  $d ($o : BitVec 16) (Src.reg $s))
scoped macro "stxw"  d:ident ", " o:num ", " s:ident : term =>
  `(Instr.store .word  $d ($o : BitVec 16) (Src.reg $s))
scoped macro "stxdw" d:ident ", " o:num ", " s:ident : term =>
  `(Instr.store .dword $d ($o : BitVec 16) (Src.reg $s))

scoped macro "stb"  d:ident ", " o:num ", " s:num : term =>
  `(Instr.store .byte  $d ($o : BitVec 16) (Src.imm ($s : BitVec 32)))
scoped macro "sth"  d:ident ", " o:num ", " s:num : term =>
  `(Instr.store .half  $d ($o : BitVec 16) (Src.imm ($s : BitVec 32)))
scoped macro "stw"  d:ident ", " o:num ", " s:num : term =>
  `(Instr.store .word  $d ($o : BitVec 16) (Src.imm ($s : BitVec 32)))
scoped macro "stdw" d:ident ", " o:num ", " s:num : term =>
  `(Instr.store .dword $d ($o : BitVec 16) (Src.imm ($s : BitVec 32)))

scoped macro "lddw" d:ident ", " i:num : term => `(Instr.lddw $d ($i : BitVec 64))

scoped macro "atomicadd"     d:ident ", " o:num ", " s:ident : term =>
  `(Instr.atomic .dword .add     false $d $s ($o : BitVec 16))
scoped macro "atomicaddf"    d:ident ", " o:num ", " s:ident : term =>
  `(Instr.atomic .dword .add     true  $d $s ($o : BitVec 16))
scoped macro "atomicor"      d:ident ", " o:num ", " s:ident : term =>
  `(Instr.atomic .dword .or      false $d $s ($o : BitVec 16))
scoped macro "atomicorf"     d:ident ", " o:num ", " s:ident : term =>
  `(Instr.atomic .dword .or      true  $d $s ($o : BitVec 16))
scoped macro "atomicand"     d:ident ", " o:num ", " s:ident : term =>
  `(Instr.atomic .dword .and     false $d $s ($o : BitVec 16))
scoped macro "atomicandf"    d:ident ", " o:num ", " s:ident : term =>
  `(Instr.atomic .dword .and     true  $d $s ($o : BitVec 16))
scoped macro "atomicxor"     d:ident ", " o:num ", " s:ident : term =>
  `(Instr.atomic .dword .xor     false $d $s ($o : BitVec 16))
scoped macro "atomicxorf"    d:ident ", " o:num ", " s:ident : term =>
  `(Instr.atomic .dword .xor     true  $d $s ($o : BitVec 16))
scoped macro "atomicxchg"    d:ident ", " o:num ", " s:ident : term =>
  `(Instr.atomic .dword .xchg    true  $d $s ($o : BitVec 16))
scoped macro "atomiccmpxchg" d:ident ", " o:num ", " s:ident : term =>
  `(Instr.atomic .dword .cmpxchg true  $d $s ($o : BitVec 16))

scoped macro "call " fid:num : term => `(Instr.call ($fid : BitVec 32))

scoped macro "exit" : term => `(Instr.exit)

scoped macro "bpf_prog" "[" instrs:term,* "]" : term => `(#[$instrs,*])

end Ebpf

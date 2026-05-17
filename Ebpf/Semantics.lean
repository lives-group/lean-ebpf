import Ebpf.Instr
import Mathlib.Data.BitVec

namespace Ebpf

/- Machine State -/

abbrev RegFile := Reg → BitVec 64

abbrev Memory := BitVec 64 → BitVec 8

structure State where
  regs : RegFile
  mem  : Memory
  pc   : ℕ

def RegFile.set (rf : RegFile) (r : Reg) (v : BitVec 64) : RegFile :=
  fun r' => if r' = r then v else rf r'


def readMem (m : Memory) (addr : BitVec 64) (sz : Size) : BitVec 64 :=
  match sz with
  | Size.byte  => BitVec.zeroExtend 64 (m addr)
  | Size.half  =>
      let b0 := BitVec.zeroExtend 64 (m addr)
      let b1 := BitVec.zeroExtend 64 (m (addr + 1))
      b0 ||| (b1 <<< 8)
  | Size.word  =>
      let b0 := BitVec.zeroExtend 64 (m addr)
      let b1 := BitVec.zeroExtend 64 (m (addr + 1))
      let b2 := BitVec.zeroExtend 64 (m (addr + 2))
      let b3 := BitVec.zeroExtend 64 (m (addr + 3))
      b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
  | Size.dword =>
      let b0 := BitVec.zeroExtend 64 (m addr)
      let b1 := BitVec.zeroExtend 64 (m (addr + 1))
      let b2 := BitVec.zeroExtend 64 (m (addr + 2))
      let b3 := BitVec.zeroExtend 64 (m (addr + 3))
      let b4 := BitVec.zeroExtend 64 (m (addr + 4))
      let b5 := BitVec.zeroExtend 64 (m (addr + 5))
      let b6 := BitVec.zeroExtend 64 (m (addr + 6))
      let b7 := BitVec.zeroExtend 64 (m (addr + 7))
      b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
      (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

def writeMem (m : Memory) (addr : BitVec 64) (val : BitVec 64) (sz : Size) : Memory :=
  match sz with
  | Size.byte  => fun a => if a = addr then BitVec.truncate 8 val else m a
  | Size.half  => fun a =>
      if a = addr     then BitVec.truncate 8 val
      else if a = addr + 1 then BitVec.truncate 8 (val >>> 8)
      else m a
  | Size.word  => fun a =>
      if a = addr      then BitVec.truncate 8 val
      else if a = addr + 1 then BitVec.truncate 8 (val >>> 8)
      else if a = addr + 2 then BitVec.truncate 8 (val >>> 16)
      else if a = addr + 3 then BitVec.truncate 8 (val >>> 24)
      else m a
  | Size.dword => fun a =>
      if a = addr      then BitVec.truncate 8 val
      else if a = addr + 1 then BitVec.truncate 8 (val >>> 8)
      else if a = addr + 2 then BitVec.truncate 8 (val >>> 16)
      else if a = addr + 3 then BitVec.truncate 8 (val >>> 24)
      else if a = addr + 4 then BitVec.truncate 8 (val >>> 32)
      else if a = addr + 5 then BitVec.truncate 8 (val >>> 40)
      else if a = addr + 6 then BitVec.truncate 8 (val >>> 48)
      else if a = addr + 7 then BitVec.truncate 8 (val >>> 56)
      else m a

def zext32 (v : BitVec 64) : BitVec 64 :=
  BitVec.zeroExtend 64 (BitVec.truncate 32 v)

def evalSrc (rf : RegFile) (s : Src) : BitVec 64 :=
  match s with
  | Src.reg r => rf r
  | Src.imm i => BitVec.signExtend 64 i

def evalAlu64 (op : AluOp) (dst src : BitVec 64) : BitVec 64 :=
  match op with
  | AluOp.add  => dst + src
  | AluOp.sub  => dst - src
  | AluOp.mul  => dst * src
  | AluOp.div  => if src = 0 then 0 else dst / src
  | AluOp.mod  => if src = 0 then dst else dst % src
  | AluOp.or   => dst ||| src
  | AluOp.and  => dst &&& src
  | AluOp.xor  => dst ^^^ src
  | AluOp.lsh  => dst <<< src.toNat
  | AluOp.rsh  => dst >>> src.toNat
  | AluOp.arsh => BitVec.sshiftRight dst src.toNat
  | AluOp.mov  => src

def evalAlu32 (op : AluOp) (dst src : BitVec 64) : BitVec 64 :=
  let d := BitVec.truncate 32 dst
  let s := BitVec.truncate 32 src
  let r : BitVec 32 :=
    match op with
    | AluOp.add  => d + s
    | AluOp.sub  => d - s
    | AluOp.mul  => d * s
    | AluOp.div  => if s = 0 then 0 else d / s
    | AluOp.mod  => if s = 0 then d else d % s
    | AluOp.or   => d ||| s
    | AluOp.and  => d &&& s
    | AluOp.xor  => d ^^^ s
    | AluOp.lsh  => d <<< s.toNat
    | AluOp.rsh  => d >>> s.toNat
    | AluOp.arsh => BitVec.sshiftRight d s.toNat
    | AluOp.mov  => s
  BitVec.zeroExtend 64 r

def evalJmp64 (op : JmpOp) (dst src : BitVec 64) : Bool :=
  match op with
  | JmpOp.jeq  => dst == src
  | JmpOp.jne  => dst != src
  | JmpOp.jgt  => dst > src
  | JmpOp.jge  => dst ≥ src
  | JmpOp.jlt  => dst < src
  | JmpOp.jle  => dst ≤ src
  | JmpOp.jsgt => dst.toInt > src.toInt
  | JmpOp.jsge => dst.toInt ≥ src.toInt
  | JmpOp.jslt => dst.toInt < src.toInt
  | JmpOp.jsle => dst.toInt ≤ src.toInt
  | JmpOp.jset => (dst &&& src) != 0

def evalJmp32 (op : JmpOp) (dst src : BitVec 64) : Bool :=
  evalJmp64 op
    (BitVec.zeroExtend 64 (BitVec.truncate 32 dst))
    (BitVec.zeroExtend 64 (BitVec.truncate 32 src))

def evalEndian (e : Endian) (sz : Size) (v : BitVec 64) : BitVec 64 :=
  let swap16 (x : BitVec 64) : BitVec 64 :=
    let lo := x &&& 0xff
    let hi := (x >>> 8) &&& 0xff
    (lo <<< 8) ||| hi
  let swap32 (x : BitVec 64) : BitVec 64 :=
    let b0 := x &&& 0xff
    let b1 := (x >>> 8)  &&& 0xff
    let b2 := (x >>> 16) &&& 0xff
    let b3 := (x >>> 24) &&& 0xff
    (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3
  let swap64 (x : BitVec 64) : BitVec 64 :=
    let b0 := x &&& 0xff
    let b1 := (x >>> 8)  &&& 0xff
    let b2 := (x >>> 16) &&& 0xff
    let b3 := (x >>> 24) &&& 0xff
    let b4 := (x >>> 32) &&& 0xff
    let b5 := (x >>> 40) &&& 0xff
    let b6 := (x >>> 48) &&& 0xff
    let b7 := (x >>> 56) &&& 0xff
    (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32) |||
    (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8)  ||| b7
  match e with
  | Endian.le => v
  | Endian.be =>
    match sz with
    | Size.byte  => v
    | Size.half  => swap16 v
    | Size.word  => swap32 v
    | Size.dword => swap64 v

def offset16ToInt (off : BitVec 16) : Int := off.toInt

set_option linter.style.emptyLine false

inductive Step (prog : Program) : State → State → Prop where
  | alu64 :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ)
        (op : AluOp) (dst : Reg) (src : Src) (v : BitVec 64),
      prog[pc]? = some (Instr.alu64 op dst src) →
      v = evalAlu64 op (regs dst) (evalSrc regs src) →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs.set dst v, mem := mem, pc := pc + 1 }
  | alu32 :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ)
        (op : AluOp) (dst : Reg) (src : Src) (v : BitVec 64),
      prog[pc]? = some (Instr.alu32 op dst src) →
      v = evalAlu32 op (regs dst) (evalSrc regs src) →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs.set dst v, mem := mem, pc := pc + 1 }
  | neg64 :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ) (dst : Reg),
      prog[pc]? = some (Instr.neg64 dst) →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs.set dst (- regs dst), mem := mem, pc := pc + 1 }
  | neg32 :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ) (dst : Reg),
      prog[pc]? = some (Instr.neg32 dst) →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs.set dst (zext32 (- regs dst)), mem := mem, pc := pc + 1 }
  | endian :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ)
        (e : Endian) (sz : Size) (dst : Reg) (v : BitVec 64),
      prog[pc]? = some (Instr.endian e sz dst) →
      v = evalEndian e sz (regs dst) →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs.set dst v, mem := mem, pc := pc + 1 }
  | ja :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ) (off : BitVec 16) (pc' : Int),
      prog[pc]? = some (Instr.ja off) →
      pc' = (pc : Int) + 1 + offset16ToInt off →
      0 ≤ pc' →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs, mem := mem, pc := pc'.toNat }
  | jmp64_taken :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ)
        (op : JmpOp) (dst : Reg) (src : Src) (off : BitVec 16) (pc' : Int),
      prog[pc]? = some (Instr.jmp64 op dst src off) →
      evalJmp64 op (regs dst) (evalSrc regs src) = true →
      pc' = (pc : Int) + 1 + offset16ToInt off →
      0 ≤ pc' →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs, mem := mem, pc := pc'.toNat }
  | jmp64_fallthrough :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ)
        (op : JmpOp) (dst : Reg) (src : Src) (off : BitVec 16),
      prog[pc]? = some (Instr.jmp64 op dst src off) →
      evalJmp64 op (regs dst) (evalSrc regs src) = false →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs, mem := mem, pc := pc + 1 }
  | jmp32_taken :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ)
        (op : JmpOp) (dst : Reg) (src : Src) (off : BitVec 16) (pc' : Int),
      prog[pc]? = some (Instr.jmp32 op dst src off) →
      evalJmp32 op (regs dst) (evalSrc regs src) = true →
      pc' = (pc : Int) + 1 + offset16ToInt off →
      0 ≤ pc' →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs, mem := mem, pc := pc'.toNat }
  | jmp32_fallthrough :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ)
        (op : JmpOp) (dst : Reg) (src : Src) (off : BitVec 16),
      prog[pc]? = some (Instr.jmp32 op dst src off) →
      evalJmp32 op (regs dst) (evalSrc regs src) = false →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs, mem := mem, pc := pc + 1 }
  | store :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ)
        (sz : Size) (dst : Reg) (off : BitVec 16) (src : Src)
        (addr : BitVec 64) (mem' : Memory),
      prog[pc]? = some (Instr.store sz dst off src) →
      addr = regs dst + BitVec.signExtend 64 off →
      mem' = writeMem mem addr (evalSrc regs src) sz →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs, mem := mem', pc := pc + 1 }
  | load :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ)
        (sz : Size) (dst : Reg) (src : Reg) (off : BitVec 16)
        (addr : BitVec 64) (v : BitVec 64),
      prog[pc]? = some (Instr.load sz dst src off) →
      addr = regs src + BitVec.signExtend 64 off →
      v = readMem mem addr sz →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs.set dst v, mem := mem, pc := pc + 1 }
  | lddw :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ)
        (dst : Reg) (imm : BitVec 64),
      prog[pc]? = some (Instr.lddw dst imm) →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs.set dst imm, mem := mem, pc := pc + 2 }
  | atomic_op :
      ∀ (regs : RegFile) (mem : Memory) (pc : ℕ)
        (sz : Size) (op : AtomicOp) (fetch : Bool)
        (dst : Reg) (src : Reg) (off : BitVec 16)
        (addr : BitVec 64) (oldVal newVal : BitVec 64)
        (mem' : Memory) (regs' : RegFile),
      prog[pc]? = some (Instr.atomic sz op fetch dst src off) →
      addr    = regs dst + BitVec.signExtend 64 off →
      oldVal  = readMem mem addr sz →
      newVal  = (match op with
                 | AtomicOp.add    => oldVal + regs src
                 | AtomicOp.or     => oldVal ||| regs src
                 | AtomicOp.and    => oldVal &&& regs src
                 | AtomicOp.xor    => oldVal ^^^ regs src
                 | AtomicOp.xchg   => regs src
                 | AtomicOp.cmpxchg =>
                     if regs Reg.r0 = oldVal then regs src else oldVal) →
      mem'    = writeMem mem addr newVal sz →
      regs'   = (match op with
                 | AtomicOp.cmpxchg => (regs.set Reg.r0 oldVal)
                 | _ => if fetch then regs.set src oldVal else regs) →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs', mem := mem', pc := pc + 1 }
  | call :
      ∀ (regs regs' : RegFile) (mem mem' : Memory) (pc : ℕ) (fid : BitVec 32)
        (fp : BitVec 64 → Option (BitVec 8)),
      prog[pc]? = some (Instr.call fid) →
      (∀ r, r ∈ ([Reg.r6, Reg.r7, Reg.r8, Reg.r9, Reg.r10] : List Reg) →
            regs' r = regs r) →
      (∀ a, fp a = none → mem' a = mem a) →
      Step prog
        { regs := regs, mem := mem, pc := pc }
        { regs := regs', mem := mem', pc := pc + 1 }

/- Multi-step (reflexive-transitive closure) -/

inductive Steps (prog : Program) : State → State → Type where
  | refl : ∀ (s : State), Steps prog s s
  | step : ∀ (s s'' s' : State),
      Step prog s s'' → Steps prog s'' s' → Steps prog s s'

/- Termination -/

def Terminates (prog : Program) (s₀ : State) : Prop :=
  ∃ s : State, Nonempty (Steps prog s₀ s) ∧ prog[s.pc]? = some Instr.exit

end Ebpf

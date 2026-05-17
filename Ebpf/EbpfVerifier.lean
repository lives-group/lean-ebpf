import Ebpf.Semantics
set_option linter.style.emptyLine false
namespace Ebpf

inductive RegType where
  | not_init | scalar | ptr_ctx | ptr_map_const
  | ptr_map_value (off : Int) | ptr_map_value_or_null
  | ptr_stack (off : Int)
  | ptr_packet (off : Int) (range : ℕ)
  | ptr_packet_end | ptr_socket | ptr_socket_or_null
  deriving DecidableEq, Repr

def RegType.isNullable : RegType → Bool
| .ptr_map_value_or_null => true
| .ptr_socket_or_null => true
| _ => false

def RegType.isPointer : RegType → Bool
| .not_init
| .scalar => false
| _ => true

def RegType.isReadable : RegType → Bool
| .not_init => false
| _ => true

def RegType.noArith : RegType → Bool
| .ptr_map_const => true
| .ptr_packet_end => true
| .ptr_map_value_or_null => true
| .ptr_socket_or_null => true
| _ => false

def sizeBytes : Size → ℕ
| .byte => 1
| .half => 2
| .word => 4
| .dword => 8

structure AState where
  regs : Reg → RegType
  stack : Fin 512 → Bool
  refcount : ℕ

def AState.setReg (s : AState) (r : Reg) (t : RegType) : AState :=
  { s with regs := fun r' => if r' = r then t else s.regs r' }
def AState.markStack (s : AState) (lo n : ℕ) : AState :=
  { s with stack := fun i => if lo ≤ i.val ∧ i.val < lo + n then true else s.stack i }
def stackIdx (off : Int) : Option (Fin 512) :=
  if _ : -512 ≤ off ∧ off < 0 then
    let i := (512 + off).toNat
    if hi : i < 512 then some ⟨i, hi⟩ else none
  else none
def AState.stackRangeInit (s : AState) (off : Int) (sz : ℕ) : Prop :=
  ∀ k : Fin sz, let i := (512 + off + k.val).toNat
    ∃ hi : i < 512, s.stack ⟨i, hi⟩ = true

-- ALU results
def aluResult64 (op : AluOp) (dst src : RegType) : Option RegType :=
  match op with
  | AluOp.mov => if src.isReadable then some src else none
  | _ =>
    if dst.noArith || src.noArith then none
    else match dst, src with
    | .scalar, .scalar => some .scalar
    | .ptr_map_value _off, .scalar =>
        match op with
        | AluOp.add
        | AluOp.sub => some (.ptr_map_value 0)
        | _ => none
    | .ptr_stack _off, .scalar =>
        match op with
        | AluOp.add
        | AluOp.sub => some (.ptr_stack 0)
        | _ => none
    | .ptr_packet _off _r, .scalar =>
        match op with
        | AluOp.add => some (.ptr_packet 0 0)
        | _ => none
    | .scalar, .ptr_map_value _off =>
        match op with
        | AluOp.add => some (.ptr_map_value 0)
        | _ => none
    | .scalar, .ptr_stack _off =>
        match op with
        | AluOp.add => some (.ptr_stack 0)
        | _ => none
    | t1, t2 =>
        if t1.isPointer && t2.isPointer
        then some .scalar
        else none

def aluResult32 (op : AluOp) (dst src : RegType) : Option RegType :=
  match aluResult64 op dst src with
  | some _ => some .scalar
  | none => none

-- Memory safety predicates
def stackLoadSafe (s : AState) (off : Int) (sz : Size) : Prop :=
  s.stackRangeInit off (sizeBytes sz)

def mapValueAccessSafe (off : Int) (sz : Size) (mapSize : ℕ) : Prop :=
  0 ≤ off ∧ (off + sizeBytes sz : Int) ≤ mapSize

def packetAccessSafe (off : Int) (range : ℕ) (sz : Size) : Prop :=
  0 ≤ off ∧ (off.toNat + sizeBytes sz) ≤ range

def stackOffsetValid (off : Int) (sz : Size) : Prop :=
  -512 ≤ off ∧ (off + sizeBytes sz : Int) ≤ 0

def loadSafe (ty : RegType) (sz : Size) (s : AState) (mapSize : ℕ) : Prop :=
  match ty with
  | .ptr_ctx => True
  | .ptr_map_value off => mapValueAccessSafe off sz mapSize
  | .ptr_stack off => stackOffsetValid off sz ∧ stackLoadSafe s off sz
  | .ptr_packet off range => packetAccessSafe off range sz
  | _ => False

def storeSafe (ty : RegType) (sz : Size) (mapSize : ℕ) : Prop :=
  match ty with
  | .ptr_ctx => True
  | .ptr_map_value off => mapValueAccessSafe off sz mapSize
  | .ptr_stack off => stackOffsetValid off sz
  | _ => False

-- NULL-check refinement
def refineEqZero : RegType → RegType
| .ptr_map_value_or_null => .scalar
| .ptr_socket_or_null => .scalar
| t => t

def refineNeZero : RegType → RegType
| .ptr_map_value_or_null => .ptr_map_value 0
| .ptr_socket_or_null => .ptr_socket
| t => t

def nullCheckTaken (dst : Reg) (src : Src) (s : AState) : AState :=
  match src with
  | Src.imm i => if i = 0
                 then s.setReg dst (refineEqZero (s.regs dst))
                 else s
  | _ => s

def nullCheckFall (dst : Reg) (src : Src) (s : AState) : AState :=
  match src with
  | Src.imm i => if i = 0
                 then s.setReg dst (refineNeZero (s.regs dst))
                 else s
  | _ => s

def srcReadable (s : AState) : Src → Prop
| Src.imm _ => True
| Src.reg r => s.regs r ≠ .not_init

def srcType (s : AState) : Src → RegType
| Src.imm _ => .scalar
| Src.reg r => s.regs r

def afterCall (s : AState) (ret : RegType) : AState :=
  { s with regs :=
      fun r => match r with
      | .r0 => ret
      | .r1 => .not_init
      | .r2 => .not_init
      | .r3 => .not_init
      | .r4 => .not_init
      | .r5 => .not_init
      | _ => s.regs r }

-- Phase 1 predicates
def isForwardJump (pc : ℕ) (target : ℕ) : Prop :=
  pc < target

def NoBackEdges (prog : Program) : Prop :=
  ∀ pc : ℕ, pc < prog.size → match prog[pc]? with
    | some (Instr.ja off) =>
      isForwardJump pc ((pc : Int) + 1 + offset16ToInt off).toNat
    | some (Instr.jmp64 _ _ _ off) =>
      isForwardJump pc ((pc : Int) + 1 + offset16ToInt off).toNat
    | some (Instr.jmp32 _ _ _ off) =>
      isForwardJump pc ((pc : Int) + 1 + offset16ToInt off).toNat
    | _ => True

def NoDeadCode (prog : Program) : Prop :=
  ∀ target : ℕ, target < prog.size → ∃ pc : ℕ, pc < prog.size ∧
    match prog[pc]? with
    | some (Instr.ja off) =>
      ((pc : Int) + 1 + offset16ToInt off).toNat = target
    | some (Instr.jmp64 _ _ _ off) =>
      ((pc : Int) + 1 + offset16ToInt off).toNat = target ∨ target = pc + 1
    | some (Instr.jmp32 _ _ _ off) =>
      ((pc : Int) + 1 + offset16ToInt off).toNat = target ∨ target = pc + 1
    | _ => target = pc + 1

-- Successor-state helpers
def storeSuccState (s : AState) (dst : Reg) (off : BitVec 16) (sz : Size) : AState :=
  match s.regs dst with
  | RegType.ptr_stack poff =>
    s.markStack ((512 : Int) + poff + off.toInt).toNat (sizeBytes sz)
  | _ => s

def atomicSuccState (s : AState) (op : AtomicOp) (fetch : Bool) (src : Reg) : AState :=
  let s' := if fetch then s.setReg src RegType.scalar else s
  if op = AtomicOp.cmpxchg then s'.setReg Reg.r0 RegType.scalar else s'

/- The verifier -/

inductive Verifies (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
                   : ℕ → AState → Prop where
  | exit : ∀ (pc : ℕ) (s : AState),
      prog[pc]? = some Instr.exit → 
      s.regs Reg.r0 ≠ RegType.not_init → 
      s.refcount = 0 →
      Verifies prog mapSize callTypes pc s
  | alu64 : ∀ (pc : ℕ) (s : AState) 
              (op : AluOp) (dst : Reg) 
              (src : Src) (t : RegType),
      prog[pc]? = some (Instr.alu64 op dst src) →
      s.regs dst ≠ RegType.not_init → srcReadable s src →
      aluResult64 op (s.regs dst) (srcType s src) = some t →
      Verifies prog mapSize callTypes (pc + 1) (s.setReg dst t) →
      Verifies prog mapSize callTypes pc s
  | alu32 : ∀ (pc : ℕ) (s : AState) 
              (op : AluOp) (dst : Reg) 
              (src : Src) (t : RegType),
      prog[pc]? = some (Instr.alu32 op dst src) →
      s.regs dst ≠ RegType.not_init → 
      srcReadable s src →
      aluResult32 op (s.regs dst) (srcType s src) = some t →
      Verifies prog mapSize callTypes (pc + 1) (s.setReg dst t) →
      Verifies prog mapSize callTypes pc s
  | neg64 : ∀ (pc : ℕ) (s : AState) (dst : Reg),
      prog[pc]? = some (Instr.neg64 dst) → 
      s.regs dst = RegType.scalar →
      Verifies prog mapSize callTypes (pc + 1) s →
      Verifies prog mapSize callTypes pc s
  | neg32 : ∀ (pc : ℕ) (s : AState) 
              (dst : Reg),
      prog[pc]? = some (Instr.neg32 dst) → 
      s.regs dst = RegType.scalar →
      Verifies prog mapSize callTypes (pc + 1) s →
      Verifies prog mapSize callTypes pc s
  | endian : ∀ (pc : ℕ) (s : AState) 
               (e : Endian) (sz : Size) 
               (dst : Reg),
      prog[pc]? = some (Instr.endian e sz dst) → s.regs dst = RegType.scalar →
      Verifies prog mapSize callTypes (pc + 1) s →
      Verifies prog mapSize callTypes pc s
  | ja : ∀ (pc : ℕ) (s : AState) (off : BitVec 16) (pc' : Int),
      prog[pc]? = some (Instr.ja off) →
      pc' = (pc : Int) + 1 + offset16ToInt off → 0 ≤ pc' →
      Verifies prog mapSize callTypes pc'.toNat s →
      Verifies prog mapSize callTypes pc s
  | jmp64 : ∀ (pc : ℕ) (s : AState) (op : JmpOp) (dst : Reg) (src : Src)
        (off : BitVec 16) (pc' : Int),
      prog[pc]? = some (Instr.jmp64 op dst src off) →
      s.regs dst ≠ RegType.not_init → srcReadable s src →
      pc' = (pc : Int) + 1 + offset16ToInt off → 0 ≤ pc' →
      Verifies prog mapSize callTypes pc'.toNat
        (match op with
          | JmpOp.jeq => nullCheckTaken dst src s
          | JmpOp.jne => nullCheckFall dst src s
          | _ => s) →
      Verifies prog mapSize callTypes (pc + 1)
        (match op with
          | JmpOp.jeq => nullCheckFall dst src s
          | JmpOp.jne => nullCheckTaken dst src s
          | _ => s) →
      Verifies prog mapSize callTypes pc s
  | jmp32 : ∀ (pc : ℕ) (s : AState) (op : JmpOp) (dst : Reg) (src : Src)
        (off : BitVec 16) (pc' : Int),
      prog[pc]? = some (Instr.jmp32 op dst src off) →
      s.regs dst ≠ RegType.not_init → srcReadable s src →
      pc' = (pc : Int) + 1 + offset16ToInt off → 0 ≤ pc' →
      Verifies prog mapSize callTypes pc'.toNat
        (match op with
          | JmpOp.jeq => nullCheckTaken dst src s
          | JmpOp.jne => nullCheckFall dst src s
          | _ => s) →
      Verifies prog mapSize callTypes (pc + 1)
        (match op with
          | JmpOp.jeq => nullCheckFall dst src s
          | JmpOp.jne => nullCheckTaken dst src s
          | _ => s) →
      Verifies prog mapSize callTypes pc s
  | load : ∀ (pc : ℕ) (s : AState) (sz : Size) (dst : Reg) (src : Reg) (off : BitVec 16),
      prog[pc]? = some (Instr.load sz dst src off) →
      loadSafe (s.regs src) sz s mapSize →
      Verifies prog mapSize callTypes (pc + 1) (s.setReg dst RegType.scalar) →
      Verifies prog mapSize callTypes pc s
  | store : ∀ (pc : ℕ) (s : AState) (sz : Size) (dst : Reg) (off : BitVec 16) (src : Src),
      prog[pc]? = some (Instr.store sz dst off src) →
      srcReadable s src → storeSafe (s.regs dst) sz mapSize →
      Verifies prog mapSize callTypes (pc + 1) (storeSuccState s dst off sz) →
      Verifies prog mapSize callTypes pc s
  | lddw : ∀ (pc : ℕ) (s : AState) (dst : Reg) (imm : BitVec 64),
      prog[pc]? = some (Instr.lddw dst imm) →
      Verifies prog mapSize callTypes (pc + 2) (s.setReg dst RegType.scalar) →
      Verifies prog mapSize callTypes pc s
  | atomic : ∀ (pc : ℕ) (s : AState) (sz : Size) (op : AtomicOp) (fetch : Bool)
        (dst src : Reg) (off : BitVec 16),
      prog[pc]? = some (Instr.atomic sz op fetch dst src off) →
      (match s.regs dst with
        | RegType.ptr_map_value _ => True
        | RegType.ptr_stack _ => True
        | _ => False) →
      s.regs src = RegType.scalar →
      (op = AtomicOp.cmpxchg → s.regs Reg.r0 = RegType.scalar) →
      Verifies prog mapSize callTypes (pc + 1) (atomicSuccState s op fetch src) →
      Verifies prog mapSize callTypes pc s
  | call : ∀ (pc : ℕ) (s : AState) (fid : BitVec 32),
      prog[pc]? = some (Instr.call fid) →
      s.regs Reg.r1 ≠ RegType.not_init → s.regs Reg.r2 ≠ RegType.not_init →
      s.regs Reg.r3 ≠ RegType.not_init → s.regs Reg.r4 ≠ RegType.not_init →
      s.regs Reg.r5 ≠ RegType.not_init →
      callTypes fid ≠ RegType.not_init →
      Verifies prog mapSize callTypes (pc + 1)
        (if callTypes fid = RegType.ptr_socket
         then { afterCall s (callTypes fid) with refcount := s.refcount + 1 }
         else afterCall s (callTypes fid)) →
      Verifies prog mapSize callTypes pc s

/- Top-level well-formedness predicate -/

def initialAState : AState where
  regs := fun r => match r with
                  | Reg.r1 => RegType.ptr_ctx
                  | Reg.r10 => RegType.ptr_stack 0
                  | _ => RegType.not_init
  stack := fun _ => false
  refcount := 0

def WellFormed (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType) : Prop :=
  NoBackEdges prog ∧
  NoDeadCode prog  ∧
  Verifies prog mapSize callTypes 0 initialAState

/-Decidability -/

def srcReadableB (s : AState) : Src → Bool
  | Src.imm _ => true
  | Src.reg r => s.regs r != .not_init

def checkStackRangeB (s : AState) (off : Int) (sz : ℕ) : Bool :=
  (List.finRange sz).all fun k =>
    let i := (512 + off + k.val).toNat
    if hi : i < 512 then s.stack ⟨i, hi⟩ else false

def mapValueAccessSafeB (off : Int) (sz : Size) (mapSize : ℕ) : Bool :=
  decide (0 ≤ off) && decide ((off + sizeBytes sz : Int) ≤ mapSize)

def packetAccessSafeB (off : Int) (range : ℕ) (sz : Size) : Bool :=
  decide (0 ≤ off) && decide ((off.toNat + sizeBytes sz) ≤ range)

def stackOffsetValidB (off : Int) (sz : Size) : Bool :=
  decide (-512 ≤ off) && decide ((off + sizeBytes sz : Int) ≤ 0)

def loadSafeB (ty : RegType) (sz : Size) (s : AState) (mapSize : ℕ) : Bool :=
  match ty with
  | .ptr_ctx => true
  | .ptr_map_value off => mapValueAccessSafeB off sz mapSize
  | .ptr_stack off => stackOffsetValidB off sz && checkStackRangeB s off (sizeBytes sz)
  | .ptr_packet off range => packetAccessSafeB off range sz
  | _ => false

def storeSafeB (ty : RegType) (sz : Size) (mapSize : ℕ) : Bool :=
  match ty with
  | .ptr_ctx => true
  | .ptr_map_value off => mapValueAccessSafeB off sz mapSize
  | .ptr_stack off => stackOffsetValidB off sz
  | _ => false

def atomicDstOkB (s : AState) (dst : Reg) : Bool :=
  match s.regs dst with
  | RegType.ptr_map_value _ => true
  | RegType.ptr_stack _ => true
  | _ => false

-- Fuel-based boolean verifier

def verifyCheck (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType) :
    ℕ → ℕ → AState → Bool
  | 0, _, _ => false
  | fuel + 1, pc, s =>
    match prog[pc]? with
    | some Instr.exit =>
        (s.regs Reg.r0 != RegType.not_init) && decide (s.refcount = 0)
    | some (Instr.alu64 op dst src) =>
        (s.regs dst != RegType.not_init) && srcReadableB s src &&
        match aluResult64 op (s.regs dst) (srcType s src) with
        | some t => verifyCheck prog mapSize callTypes fuel (pc + 1) (s.setReg dst t)
        | none => false
    | some (Instr.alu32 op dst src) =>
        (s.regs dst != RegType.not_init) && srcReadableB s src &&
        match aluResult32 op (s.regs dst) (srcType s src) with
        | some t => verifyCheck prog mapSize callTypes fuel (pc + 1) (s.setReg dst t)
        | none => false
    | some (Instr.neg64 dst) =>
        decide (s.regs dst = RegType.scalar) &&
        verifyCheck prog mapSize callTypes fuel (pc + 1) s
    | some (Instr.neg32 dst) =>
        decide (s.regs dst = RegType.scalar) &&
        verifyCheck prog mapSize callTypes fuel (pc + 1) s
    | some (Instr.endian _e _sz dst) =>
        decide (s.regs dst = RegType.scalar) &&
        verifyCheck prog mapSize callTypes fuel (pc + 1) s
    | some (Instr.ja off) =>
        let pc' : Int := (pc : Int) + 1 + offset16ToInt off
        if _ : 0 ≤ pc' then
          verifyCheck prog mapSize callTypes fuel pc'.toNat s
        else false
    | some (Instr.jmp64 op dst src off) =>
        let pc' : Int := (pc : Int) + 1 + offset16ToInt off
        (s.regs dst != RegType.not_init) && srcReadableB s src &&
        if _ : 0 ≤ pc' then
          verifyCheck prog mapSize callTypes fuel pc'.toNat
            (match op with
              | JmpOp.jeq => nullCheckTaken dst src s
              | JmpOp.jne => nullCheckFall dst src s
              | _ => s) &&
          verifyCheck prog mapSize callTypes fuel (pc + 1)
            (match op with
              | JmpOp.jeq => nullCheckFall dst src s
              | JmpOp.jne => nullCheckTaken dst src s
              | _ => s)
        else false
    | some (Instr.jmp32 op dst src off) =>
        let pc' : Int := (pc : Int) + 1 + offset16ToInt off
        (s.regs dst != RegType.not_init) && srcReadableB s src &&
        if _ : 0 ≤ pc' then
          verifyCheck prog mapSize callTypes fuel pc'.toNat
            (match op with
              | JmpOp.jeq => nullCheckTaken dst src s
              | JmpOp.jne => nullCheckFall dst src s
              | _ => s) &&
          verifyCheck prog mapSize callTypes fuel (pc + 1)
            (match op with
              | JmpOp.jeq => nullCheckFall dst src s
              | JmpOp.jne => nullCheckTaken dst src s
              | _ => s)
        else false
    | some (Instr.load sz dst src _off) =>
        loadSafeB (s.regs src) sz s mapSize &&
        verifyCheck prog mapSize callTypes fuel (pc + 1) (s.setReg dst RegType.scalar)
    | some (Instr.store sz dst off src) =>
        srcReadableB s src && storeSafeB (s.regs dst) sz mapSize &&
        verifyCheck prog mapSize callTypes fuel (pc + 1) (storeSuccState s dst off sz)
    | some (Instr.lddw dst _imm) =>
        verifyCheck prog mapSize callTypes fuel (pc + 2) (s.setReg dst RegType.scalar)
    | some (Instr.atomic _sz op fetch dst src _off) =>
        atomicDstOkB s dst && decide (s.regs src = RegType.scalar) &&
        (if op = AtomicOp.cmpxchg then decide (s.regs Reg.r0 = RegType.scalar) else true) &&
        verifyCheck prog mapSize callTypes fuel (pc + 1) (atomicSuccState s op fetch src)
    | some (Instr.call fid) =>
        (s.regs Reg.r1 != RegType.not_init) && (s.regs Reg.r2 != RegType.not_init) &&
        (s.regs Reg.r3 != RegType.not_init) && (s.regs Reg.r4 != RegType.not_init) &&
        (s.regs Reg.r5 != RegType.not_init) &&
        (callTypes fid != RegType.not_init) &&
        verifyCheck prog mapSize callTypes fuel (pc + 1)
          (if callTypes fid = RegType.ptr_socket
           then { afterCall s (callTypes fid) with refcount := s.refcount + 1 }
           else afterCall s (callTypes fid))
    | none => false

-- Boolean equivalences

lemma srcReadableB_iff (s : AState) (src : Src) :
    srcReadable s src ↔ srcReadableB s src = true := by
  cases src with
  | imm _ => simp [srcReadable, srcReadableB]
  | reg r => simp [srcReadable, srcReadableB, bne_iff_ne]

lemma checkStackRangeB_iff (s : AState) (off : Int) (sz : ℕ) :
    s.stackRangeInit off sz ↔ checkStackRangeB s off sz = true := by
  simp only [AState.stackRangeInit, checkStackRangeB, List.all_eq_true]
  constructor
  · intro h k _hk
    have := h k
    simp only at this ⊢
    cases this with
    | intro hi hstack =>
      simp [hi, hstack]
  · intro h k
    have hk : k ∈ List.finRange sz := List.mem_finRange k
    have := h k hk
    simp only at this
    split_ifs at this with hi
    constructor <;> assumption

lemma storeSafeB_iff (ty : RegType) (sz : Size) (mapSize : ℕ) :
    storeSafe ty sz mapSize ↔ storeSafeB ty sz mapSize = true := by
  cases ty with
  | ptr_ctx => simp [storeSafe, storeSafeB]
  | ptr_map_value off =>
    simp only [storeSafe, storeSafeB, mapValueAccessSafeB, mapValueAccessSafe,
               Bool.and_eq_true, decide_eq_true_eq]
  | ptr_stack off =>
    simp only [storeSafe, storeSafeB, stackOffsetValidB, stackOffsetValid,
               Bool.and_eq_true, decide_eq_true_eq]
  | not_init => simp [storeSafe, storeSafeB]
  | scalar => simp [storeSafe, storeSafeB]
  | ptr_map_const => simp [storeSafe, storeSafeB]
  | ptr_map_value_or_null => simp [storeSafe, storeSafeB]
  | ptr_packet off range => simp [storeSafe, storeSafeB]
  | ptr_packet_end => simp [storeSafe, storeSafeB]
  | ptr_socket => simp [storeSafe, storeSafeB]
  | ptr_socket_or_null => simp [storeSafe, storeSafeB]

lemma loadSafeB_iff (ty : RegType) (sz : Size) (s : AState) (mapSize : ℕ) :
    loadSafe ty sz s mapSize ↔ loadSafeB ty sz s mapSize = true := by
  cases ty with
  | ptr_ctx => simp [loadSafe, loadSafeB]
  | ptr_map_value off =>
    simp only [loadSafe, loadSafeB, mapValueAccessSafeB, mapValueAccessSafe,
               Bool.and_eq_true, decide_eq_true_eq]
  | ptr_stack off =>
    simp only [loadSafe, loadSafeB, stackLoadSafe, stackOffsetValidB, stackOffsetValid,
               Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro ⟨⟨h1, h2⟩, h3⟩
      constructor
      · constructor <;> assumption
      · exact (checkStackRangeB_iff s off (sizeBytes sz)).mp h3
    · intro ⟨⟨h1, h2⟩, h3⟩
      constructor
      · constructor <;> assumption
      · exact (checkStackRangeB_iff s off (sizeBytes sz)).mpr h3
  | ptr_packet off range =>
    simp only [loadSafe, loadSafeB, packetAccessSafeB, packetAccessSafe,
               Bool.and_eq_true, decide_eq_true_eq]
  | not_init => simp [loadSafe, loadSafeB]
  | scalar => simp [loadSafe, loadSafeB]
  | ptr_map_const => simp [loadSafe, loadSafeB]
  | ptr_map_value_or_null => simp [loadSafe, loadSafeB]
  | ptr_packet_end => simp [loadSafe, loadSafeB]
  | ptr_socket => simp [loadSafe, loadSafeB]
  | ptr_socket_or_null => simp [loadSafe, loadSafeB]

-- Monotonicity lemma

lemma verifyCheck_mono (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType) :
    ∀ fuel fuel' pc s,
    fuel ≤ fuel' →
    verifyCheck prog mapSize callTypes fuel pc s = true →
    verifyCheck prog mapSize callTypes fuel' pc s = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro fuel' pc s _ h
    simp [verifyCheck] at h
  | succ n ih =>
    intro fuel' pc s hle h
    match fuel' with
    | 0 => omega
    | m + 1 =>
      have hn : n ≤ m := Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hle)
      match hpc : prog[pc]? with
      | none =>
        simp [verifyCheck, hpc] at h
      | some instr =>
        cases instr with
        | exit =>
          simp only [verifyCheck, hpc] at h ⊢
          exact h
        | alu64 op dst src =>
          simp only [verifyCheck, hpc, Bool.and_eq_true] at h ⊢
          cases h with
          | intro hdst_hsrc hrest =>
            cases hdst_hsrc with
            | intro hdst hsrc =>
              refine ⟨⟨hdst, hsrc⟩, ?_⟩
              cases h_alu : aluResult64 op (s.regs dst) (srcType s src) with
              | some t => simp only [h_alu] at hrest ⊢; exact ih m _ _ hn hrest
              | none => simp [h_alu] at hrest
        | alu32 op dst src =>
          simp only [verifyCheck, hpc, Bool.and_eq_true] at h ⊢
          cases h with
          | intro hdst_hsrc hrest =>
            cases hdst_hsrc with
            | intro hdst hsrc =>
              refine ⟨⟨hdst, hsrc⟩, ?_⟩
              cases h_alu : aluResult32 op (s.regs dst) (srcType s src) with
              | some t => simp only [h_alu] at hrest ⊢; exact ih m _ _ hn hrest
              | none => simp [h_alu] at hrest
        | neg64 dst =>
          simp only [verifyCheck, hpc, Bool.and_eq_true] at h ⊢
          exact ⟨h.1, ih m _ _ hn h.2⟩
        | neg32 dst =>
          simp only [verifyCheck, hpc, Bool.and_eq_true] at h ⊢
          exact ⟨h.1, ih m _ _ hn h.2⟩
        | endian e sz dst =>
          simp only [verifyCheck, hpc, Bool.and_eq_true] at h ⊢
          exact ⟨h.1, ih m _ _ hn h.2⟩
        | ja off =>
          simp only [verifyCheck, hpc] at h ⊢
          split_ifs at h with hpc'
          · simp only [dif_pos hpc']
            exact ih m _ _ hn h
        | jmp64 op dst src off =>
          simp only [verifyCheck, hpc, Bool.and_eq_true] at h ⊢
          cases h with
          | intro hdst_hsrc hrest =>
            cases hdst_hsrc with
            | intro hdst hsrc =>
              refine ⟨⟨hdst, hsrc⟩, ?_⟩
              split_ifs at hrest with hpc'
              · simp only [dif_pos hpc', Bool.and_eq_true] at hrest ⊢
                exact ⟨ih m _ _ hn hrest.1, ih m _ _ hn hrest.2⟩
        | jmp32 op dst src off =>
          simp only [verifyCheck, hpc, Bool.and_eq_true] at h ⊢
          cases h with
          | intro hdst_hsrc hrest =>
            cases hdst_hsrc with
            | intro hdst hsrc =>
              refine ⟨⟨hdst, hsrc⟩, ?_⟩
              split_ifs at hrest with hpc'
              · simp only [dif_pos hpc', Bool.and_eq_true] at hrest ⊢
                exact ⟨ih m _ _ hn hrest.1, ih m _ _ hn hrest.2⟩
        | load sz dst src off =>
          simp only [verifyCheck, hpc, Bool.and_eq_true] at h ⊢
          exact ⟨h.1, ih m _ _ hn h.2⟩
        | store sz dst off src =>
          simp only [verifyCheck, hpc, Bool.and_eq_true] at h ⊢
          cases h with
          | intro hsrc_hdst hrest =>
            cases hsrc_hdst with
            | intro hsrc hdst =>
              constructor
              · constructor <;> assumption
              · exact ih m _ _ hn hrest
        | lddw dst imm =>
          simp only [verifyCheck, hpc] at h ⊢
          exact ih m _ _ hn h
        | atomic sz op fetch dst src off =>
          simp only [verifyCheck, hpc, Bool.and_eq_true] at h ⊢
          cases h with
          | intro hdst_hsrc_hcmp hrest =>
            cases hdst_hsrc_hcmp with
            | intro hdst_hsrc hcmp =>
              cases hdst_hsrc with
              | intro hdst hsrc =>
                constructor
                · constructor
                  · constructor <;> assumption
                  · assumption
                · exact ih m _ _ hn hrest
        | call fid =>
          simp only [verifyCheck, hpc, Bool.and_eq_true] at h ⊢
          cases h with
          | intro h6 hrest =>
            cases h6 with
            | intro h5 hfid =>
              cases h5 with
              | intro h4 hr5 =>
                cases h4 with
                | intro h3 hr4 =>
                  cases h3 with
                  | intro h12 hr3 =>
                    cases h12 with
                    | intro hr1 hr2 =>
                      constructor
                      · constructor
                        · constructor
                          · constructor
                            · constructor
                              · constructor <;> assumption
                              · assumption
                            · assumption
                          · assumption
                        · assumption
                      · exact ih m _ _ hn hrest

-- Soundness theorem

theorem verifyCheck_sound (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType) :
    ∀ fuel pc s,
    verifyCheck prog mapSize callTypes fuel pc s = true →
    Verifies prog mapSize callTypes pc s := by
  intro fuel
  induction fuel with
  | zero =>
    intro pc s h
    simp [verifyCheck] at h
  | succ n ih =>
    intro pc s h
    match hpc : prog[pc]? with
    | none => simp [verifyCheck, hpc] at h
    | some instr =>
      cases instr with
      | exit =>
        simp only [verifyCheck, hpc, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
        exact Verifies.exit pc s hpc h.1 h.2
      | alu64 op dst src =>
        simp only [verifyCheck, hpc, Bool.and_eq_true, bne_iff_ne] at h
        cases h with
        | intro hdst_hsrc hrest =>
          cases hdst_hsrc with
          | intro hdst hsrc =>
            have hsrc' : srcReadable s src := (srcReadableB_iff s src).mpr hsrc
            split at hrest
            · next t ht =>
              exact Verifies.alu64 pc s op dst src t hpc hdst hsrc' ht (ih _ _ hrest)
            · simp at hrest
      | alu32 op dst src =>
        simp only [verifyCheck, hpc, Bool.and_eq_true, bne_iff_ne] at h
        cases h with
        | intro hdst_hsrc hrest =>
          cases hdst_hsrc with
          | intro hdst hsrc =>
            have hsrc' : srcReadable s src := (srcReadableB_iff s src).mpr hsrc
            split at hrest
            · next t ht =>
              exact Verifies.alu32 pc s op dst src t hpc hdst hsrc' ht (ih _ _ hrest)
            · simp at hrest
      | neg64 dst =>
        simp only [verifyCheck, hpc, Bool.and_eq_true, decide_eq_true_eq] at h
        exact Verifies.neg64 pc s dst hpc h.1 (ih _ _ h.2)
      | neg32 dst =>
        simp only [verifyCheck, hpc, Bool.and_eq_true, decide_eq_true_eq] at h
        exact Verifies.neg32 pc s dst hpc h.1 (ih _ _ h.2)
      | endian e sz dst =>
        simp only [verifyCheck, hpc, Bool.and_eq_true, decide_eq_true_eq] at h
        exact Verifies.endian pc s e sz dst hpc h.1 (ih _ _ h.2)
      | ja off =>
        simp only [verifyCheck, hpc] at h
        split_ifs at h with hpc'
        · exact Verifies.ja pc s off _ hpc rfl hpc' (ih _ _ h)
      | jmp64 op dst src off =>
        simp only [verifyCheck, hpc, Bool.and_eq_true, bne_iff_ne] at h
        cases h with
        | intro hdst_hsrc hrest =>
          cases hdst_hsrc with
          | intro hdst hsrc =>
            have hsrc' : srcReadable s src := (srcReadableB_iff s src).mpr hsrc
            split_ifs at hrest with hpc'
            · simp only [Bool.and_eq_true] at hrest
              exact Verifies.jmp64 pc s op dst src off _ hpc
                hdst hsrc' rfl hpc'
                (ih _ _ hrest.1) (ih _ _ hrest.2)
      | jmp32 op dst src off =>
        simp only [verifyCheck, hpc, Bool.and_eq_true, bne_iff_ne] at h
        cases h with
        | intro hdst_hsrc hrest =>
          cases hdst_hsrc with
          | intro hdst hsrc =>
            have hsrc' : srcReadable s src := (srcReadableB_iff s src).mpr hsrc
            split_ifs at hrest with hpc'
            · simp only [Bool.and_eq_true] at hrest
              exact Verifies.jmp32 pc s op dst src off _ hpc
                hdst hsrc' rfl hpc'
                (ih _ _ hrest.1) (ih _ _ hrest.2)
      | load sz dst src off =>
        simp only [verifyCheck, hpc, Bool.and_eq_true] at h
        have hload : loadSafe (s.regs src) sz s mapSize := (loadSafeB_iff _ _ _ _).mpr h.1
        exact Verifies.load pc s sz dst src off hpc hload (ih _ _ h.2)
      | store sz dst off src =>
        simp only [verifyCheck, hpc, Bool.and_eq_true] at h
        cases h with
        | intro hsrc_hdst hrest =>
          cases hsrc_hdst with
          | intro hsrc hdst =>
            have hsrc' : srcReadable s src := (srcReadableB_iff s src).mpr hsrc
            have hstore : storeSafe (s.regs dst) sz mapSize := (storeSafeB_iff _ _ _).mpr hdst
            exact Verifies.store pc s sz dst off src hpc hsrc' hstore (ih _ _ hrest)
      | lddw dst imm =>
        simp only [verifyCheck, hpc] at h
        exact Verifies.lddw pc s dst imm hpc (ih _ _ h)
      | atomic sz op fetch dst src off =>
        simp only [verifyCheck, hpc, Bool.and_eq_true, decide_eq_true_eq] at h
        cases h with
        | intro hdst_hsrc_hcmp hrest =>
          cases hdst_hsrc_hcmp with
          | intro hdst_hsrc hcmp =>
            cases hdst_hsrc with
            | intro hdst hsrc =>
              have hdst' : (match s.regs dst with
                  | RegType.ptr_map_value _ => True
                  | RegType.ptr_stack _ => True
                  | _ => False) := by
                simp only [atomicDstOkB] at hdst
                split at hdst <;> simp_all
              have hcmp' : op = AtomicOp.cmpxchg → s.regs Reg.r0 = RegType.scalar := by
                intro heq; simp only [heq, ↓reduceIte, decide_eq_true_iff] at hcmp; exact hcmp
              exact Verifies.atomic pc s sz op fetch dst src off hpc hdst' hsrc hcmp' (ih _ _ hrest)
      | call fid =>
        simp only [verifyCheck, hpc, Bool.and_eq_true, bne_iff_ne] at h
        cases h with
        | intro h6 hrest =>
          cases h6 with
          | intro h5 hfid =>
            cases h5 with
            | intro h4 hr5 =>
              cases h4 with
              | intro h3 hr4 =>
                cases h3 with
                | intro h12 hr3 =>
                  cases h12 with
                  | intro hr1 hr2 =>
                    exact Verifies.call pc s fid hpc
                      hr1 hr2 hr3 hr4 hr5 hfid (ih _ _ hrest)

-- Helper: pc < prog.size from Verifies
private lemma getElem?_some_lt {α : Type*} (a : Array α) {i : ℕ} {v : α}
    (h : a[i]? = some v) : i < a.size :=
  (Array.getElem?_eq_some_iff.mp h).elim fun hlt _ => hlt

private lemma verifies_pc_lt_size {prog : Program} {mapSize : ℕ} {callTypes : BitVec 32 → RegType}
    {pc : ℕ} {s : AState} (hv : Verifies prog mapSize callTypes pc s) : pc < prog.size := by
  cases hv with
  | exit pc s hprog _ _ => exact getElem?_some_lt prog hprog
  | alu64 pc s op dst src t hprog _ _ _ _ => exact getElem?_some_lt prog hprog
  | alu32 pc s op dst src t hprog _ _ _ _ => exact getElem?_some_lt prog hprog
  | neg64 pc s dst hprog _ _ => exact getElem?_some_lt prog hprog
  | neg32 pc s dst hprog _ _ => exact getElem?_some_lt prog hprog
  | endian pc s e sz dst hprog _ _ => exact getElem?_some_lt prog hprog
  | ja pc s off pc' hprog _ _ _ => exact getElem?_some_lt prog hprog
  | jmp64 pc s op dst src off pc' hprog _ _ _ _ _ _ => exact getElem?_some_lt prog hprog
  | jmp32 pc s op dst src off pc' hprog _ _ _ _ _ _ => exact getElem?_some_lt prog hprog
  | load pc s sz dst src off hprog _ _ => exact getElem?_some_lt prog hprog
  | store pc s sz dst off src hprog _ _ _ => exact getElem?_some_lt prog hprog
  | lddw pc s dst imm hprog _ => exact getElem?_some_lt prog hprog
  | atomic pc s sz op fetch dst src off hprog _ _ _ _ => exact getElem?_some_lt prog hprog
  | call pc s fid hprog _ _ _ _ _ _ _ => exact getElem?_some_lt prog hprog

-- Completeness theorem

theorem verifyCheck_complete (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType) :
    ∀ pc s,
    NoBackEdges prog →
    Verifies prog mapSize callTypes pc s →
    pc < prog.size →
    verifyCheck prog mapSize callTypes (prog.size + 1 - pc) pc s = true := by
  intro pc s hnb hv
  induction hv with
  | exit pc s hprog hr0 hrc =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
      constructor <;> assumption
  | alu64 pc s op dst src t hprog hdst hsrc halu hrec ih =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog, Bool.and_eq_true, bne_iff_ne]
      refine ⟨⟨hdst, (srcReadableB_iff s src).mp hsrc⟩, ?_⟩
      rw [halu]
      have hlt1 : pc + 1 < prog.size := by
        have := verifies_pc_lt_size hrec; omega
      have ih1 := ih hlt1
      have hfuel1 : prog.size + 1 - (pc + 1) = fuel := by omega
      rw [hfuel1] at ih1
      exact ih1
  | alu32 pc s op dst src t hprog hdst hsrc halu hrec ih =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog, Bool.and_eq_true, bne_iff_ne]
      refine ⟨⟨hdst, (srcReadableB_iff s src).mp hsrc⟩, ?_⟩
      rw [halu]
      have hlt1 : pc + 1 < prog.size := by
        have := verifies_pc_lt_size hrec; omega
      have ih1 := ih hlt1
      have hfuel1 : prog.size + 1 - (pc + 1) = fuel := by omega
      rw [hfuel1] at ih1
      exact ih1
  | neg64 pc s dst hprog heq hrec ih =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨heq, ?_⟩
      have hlt1 : pc + 1 < prog.size := by
        have := verifies_pc_lt_size hrec; omega
      have ih1 := ih hlt1
      have hfuel1 : prog.size + 1 - (pc + 1) = fuel := by omega
      rw [hfuel1] at ih1
      exact ih1
  | neg32 pc s dst hprog heq hrec ih =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨heq, ?_⟩
      have hlt1 : pc + 1 < prog.size := by
        have := verifies_pc_lt_size hrec; omega
      have ih1 := ih hlt1
      have hfuel1 : prog.size + 1 - (pc + 1) = fuel := by omega
      rw [hfuel1] at ih1
      exact ih1
  | endian pc s e sz dst hprog heq hrec ih =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨heq, ?_⟩
      have hlt1 : pc + 1 < prog.size := by
        have := verifies_pc_lt_size hrec; omega
      have ih1 := ih hlt1
      have hfuel1 : prog.size + 1 - (pc + 1) = fuel := by omega
      rw [hfuel1] at ih1
      exact ih1
  | ja pc s off pc' hprog hpc' hnn hrec ih =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog]
      have hnn' : 0 ≤ pc' := hnn
      rw [show (pc : Int) + 1 + offset16ToInt off = pc' from hpc'.symm]
      simp only [dif_pos hnn']
      have hfwd : isForwardJump pc pc'.toNat := by
        have h0 := hnb pc hlt
        simp only [hprog] at h0
        rw [hpc']; exact h0
      have hlt' : pc'.toNat < prog.size := verifies_pc_lt_size hrec
      have hfuel' : prog.size + 1 - pc'.toNat ≤ fuel := by
        unfold isForwardJump at hfwd; omega
      have ih1 := ih hlt'
      exact verifyCheck_mono prog mapSize callTypes _ _ _ _ hfuel' ih1
  | jmp64 pc s op dst src off pc' hprog hdst hsrc hpc' hnn hrec_taken hrec_fall ih_taken ih_fall =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog, Bool.and_eq_true, bne_iff_ne]
      refine ⟨⟨hdst, (srcReadableB_iff s src).mp hsrc⟩, ?_⟩
      have hnn' : 0 ≤ pc' := hnn
      rw [show (pc : Int) + 1 + offset16ToInt off = pc' from hpc'.symm]
      simp only [dif_pos hnn']
      simp only [Bool.and_eq_true]
      have hfwd : isForwardJump pc pc'.toNat := by
        have h0 := hnb pc hlt
        simp only [hprog] at h0
        rw [hpc']; exact h0
      have hlt_taken : pc'.toNat < prog.size := verifies_pc_lt_size hrec_taken
      have hlt_fall : pc + 1 < prog.size := verifies_pc_lt_size hrec_fall
      have hfuel_taken : prog.size + 1 - pc'.toNat ≤ fuel := by
        unfold isForwardJump at hfwd; omega
      have hfuel_fall : prog.size + 1 - (pc + 1) = fuel := by omega
      have ih_t := ih_taken hlt_taken
      have ih_f := ih_fall hlt_fall
      rw [hfuel_fall] at ih_f
      constructor
      · exact verifyCheck_mono prog mapSize callTypes _ _ _ _ hfuel_taken ih_t
      · exact ih_f
  | jmp32 pc s op dst src off pc' hprog hdst hsrc hpc' hnn hrec_taken hrec_fall ih_taken ih_fall =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog, Bool.and_eq_true, bne_iff_ne]
      refine ⟨⟨hdst, (srcReadableB_iff s src).mp hsrc⟩, ?_⟩
      have hnn' : 0 ≤ pc' := hnn
      rw [show (pc : Int) + 1 + offset16ToInt off = pc' from hpc'.symm]
      simp only [dif_pos hnn']
      simp only [Bool.and_eq_true]
      have hfwd : isForwardJump pc pc'.toNat := by
        have h0 := hnb pc hlt
        simp only [hprog] at h0
        rw [hpc']; exact h0
      have hlt_taken : pc'.toNat < prog.size := verifies_pc_lt_size hrec_taken
      have hlt_fall : pc + 1 < prog.size := verifies_pc_lt_size hrec_fall
      have hfuel_taken : prog.size + 1 - pc'.toNat ≤ fuel := by
        unfold isForwardJump at hfwd; omega
      have hfuel_fall : prog.size + 1 - (pc + 1) = fuel := by omega
      have ih_t := ih_taken hlt_taken
      have ih_f := ih_fall hlt_fall
      rw [hfuel_fall] at ih_f
      constructor
      · exact verifyCheck_mono prog mapSize callTypes _ _ _ _ hfuel_taken ih_t
      · exact ih_f
  | load pc s sz dst src off hprog hload hrec ih =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog, Bool.and_eq_true]
      refine ⟨(loadSafeB_iff _ _ _ _).mp hload, ?_⟩
      have hlt1 : pc + 1 < prog.size := by
        have := verifies_pc_lt_size hrec; omega
      have ih1 := ih hlt1
      have hfuel1 : prog.size + 1 - (pc + 1) = fuel := by omega
      rw [hfuel1] at ih1
      exact ih1
  | store pc s sz dst off src hprog hsrc hstore hrec ih =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog, Bool.and_eq_true]
      refine ⟨⟨(srcReadableB_iff s src).mp hsrc, (storeSafeB_iff _ _ _).mp hstore⟩, ?_⟩
      have hlt1 : pc + 1 < prog.size := by
        have := verifies_pc_lt_size hrec; omega
      have ih1 := ih hlt1
      have hfuel1 : prog.size + 1 - (pc + 1) = fuel := by omega
      rw [hfuel1] at ih1
      exact ih1
  | lddw pc s dst imm hprog hrec ih =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog]
      have hlt2 : pc + 2 < prog.size := by
        have := verifies_pc_lt_size hrec; omega
      have ih1 := ih hlt2
      have hfuel2 : prog.size + 1 - (pc + 2) ≤ fuel := by omega
      exact verifyCheck_mono prog mapSize callTypes _ _ _ _ hfuel2 ih1
  | atomic pc s sz op fetch dst src off hprog hdst hsrc hcmp hrec ih =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog, Bool.and_eq_true, decide_eq_true_eq]
      have hdst_b : atomicDstOkB s dst = true := by
        simp only [atomicDstOkB]
        cases h : s.regs dst with
        | ptr_map_value _ => simp
        | ptr_stack _ => simp
        | _ => exfalso; revert hdst; simp [h]
      refine ⟨⟨⟨hdst_b, hsrc⟩, ?_⟩, ?_⟩
      · split_ifs with heq
        · exact decide_eq_true_eq.mpr (hcmp heq)
        · rfl
      · have hlt1 : pc + 1 < prog.size := by
          have := verifies_pc_lt_size hrec; omega
        have ih1 := ih hlt1
        have hfuel1 : prog.size + 1 - (pc + 1) = fuel := by omega
        rw [hfuel1] at ih1
        exact ih1
  | call pc s fid hprog hr1 hr2 hr3 hr4 hr5 hfid hrec ih =>
    intro hlt
    have hfuel : prog.size + 1 - pc ≥ 1 := by omega
    match hfuel_eq : prog.size + 1 - pc with
    | 0 => omega
    | fuel + 1 =>
      simp only [verifyCheck, hprog, Bool.and_eq_true, bne_iff_ne]
      refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact hr1
      · exact hr2
      · exact hr3
      · exact hr4
      · exact hr5
      · exact hfid
      have hlt1 : pc + 1 < prog.size := by
        have := verifies_pc_lt_size hrec; omega
      have ih1 := ih hlt1
      have hfuel1 : prog.size + 1 - (pc + 1) = fuel := by omega
      rw [hfuel1] at ih1
      exact ih1

-- Boolean check for NoBackEdges

def noBackEdgesB (prog : Program) : Bool :=
  (List.range prog.size).all fun pc =>
    match prog[pc]? with
    | some (Instr.ja off) => decide (pc < ((pc : Int) + 1 + offset16ToInt off).toNat)
    | some (Instr.jmp64 _ _ _ off) => decide (pc < ((pc : Int) + 1 + offset16ToInt off).toNat)
    | some (Instr.jmp32 _ _ _ off) => decide (pc < ((pc : Int) + 1 + offset16ToInt off).toNat)
    | _ => true

lemma noBackEdgesB_iff (prog : Program) :
    NoBackEdges prog ↔ noBackEdgesB prog = true := by
  unfold NoBackEdges noBackEdgesB isForwardJump
  constructor
  · intro h
    apply List.all_eq_true.mpr
    intro pc hpc
    rw [List.mem_range] at hpc
    have hh := h pc hpc
    match hpinstr : prog[pc]? with
    | none => trivial
    | some (Instr.ja off) =>
      simp only [hpinstr] at hh ⊢
      exact decide_eq_true_eq.mpr hh
    | some (Instr.jmp64 op dst src off) =>
      simp only [hpinstr] at hh ⊢
      exact decide_eq_true_eq.mpr hh
    | some (Instr.jmp32 op dst src off) =>
      simp only [hpinstr] at hh ⊢
      exact decide_eq_true_eq.mpr hh
    | some (Instr.exit) => rfl
    | some (Instr.alu64 ..) => rfl
    | some (Instr.alu32 ..) => rfl
    | some (Instr.neg64 ..) => rfl
    | some (Instr.neg32 ..) => rfl
    | some (Instr.endian ..) => rfl
    | some (Instr.load ..) => rfl
    | some (Instr.store ..) => rfl
    | some (Instr.lddw ..) => rfl
    | some (Instr.atomic ..) => rfl
    | some (Instr.call ..) => rfl
  · intro h pc hpc
    have hh := List.all_eq_true.mp h pc (List.mem_range.mpr hpc)
    match hpinstr : prog[pc]? with
    | none => exact True.intro
    | some (Instr.ja off) =>
      simp only [hpinstr] at hh ⊢
      exact decide_eq_true_eq.mp hh
    | some (Instr.jmp64 op dst src off) =>
      simp only [hpinstr] at hh ⊢
      exact decide_eq_true_eq.mp hh
    | some (Instr.jmp32 op dst src off) =>
      simp only [hpinstr] at hh ⊢
      exact decide_eq_true_eq.mp hh
    | some (Instr.exit) => exact True.intro
    | some (Instr.alu64 ..) => exact True.intro
    | some (Instr.alu32 ..) => exact True.intro
    | some (Instr.neg64 ..) => exact True.intro
    | some (Instr.neg32 ..) => exact True.intro
    | some (Instr.endian ..) => exact True.intro
    | some (Instr.load ..) => exact True.intro
    | some (Instr.store ..) => exact True.intro
    | some (Instr.lddw ..) => exact True.intro
    | some (Instr.atomic ..) => exact True.intro
    | some (Instr.call ..) => exact True.intro

instance decNoBackEdges (prog : Program) : Decidable (NoBackEdges prog) :=
  decidable_of_iff _ (noBackEdgesB_iff prog).symm

-- Boolean check for NoDeadCode

def noDeadCodeB (prog : Program) : Bool :=
  (List.range prog.size).all fun target =>
    (List.range prog.size).any fun pc =>
      match prog[pc]? with
      | some (Instr.ja off) => decide (((pc : Int) + 1 + offset16ToInt off).toNat = target)
      | some (Instr.jmp64 _ _ _ off) =>
          decide (((pc : Int) + 1 + offset16ToInt off).toNat = target) ||
          decide (target = pc + 1)
      | some (Instr.jmp32 _ _ _ off) =>
          decide (((pc : Int) + 1 + offset16ToInt off).toNat = target) ||
          decide (target = pc + 1)
      | _ => decide (target = pc + 1)

lemma noDeadCodeB_iff (prog : Program) :
    NoDeadCode prog ↔ noDeadCodeB prog = true := by
  unfold NoDeadCode noDeadCodeB
  constructor
  · intro h
    apply List.all_eq_true.mpr
    intro target htarget
    rw [List.mem_range] at htarget
    cases h target htarget with
    | intro pc rest =>
      cases rest with
      | intro hpc hmatch =>
        apply List.any_eq_true.mpr
        refine ⟨pc, List.mem_range.mpr hpc, ?_⟩
        match hpinstr : prog[pc]? with
        | none =>
          simp only [hpinstr] at hmatch
          exact decide_eq_true_eq.mpr hmatch
        | some (Instr.ja off) =>
          simp only [hpinstr] at hmatch
          exact decide_eq_true_eq.mpr hmatch
        | some (Instr.jmp64 op dst src off) =>
          simp only [hpinstr] at hmatch
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact hmatch
        | some (Instr.jmp32 op dst src off) =>
          simp only [hpinstr] at hmatch
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact hmatch
        | some (Instr.exit) =>
          simp only [hpinstr] at hmatch; exact decide_eq_true_eq.mpr hmatch
        | some (Instr.alu64 op dst src) =>
          simp only [hpinstr] at hmatch; exact decide_eq_true_eq.mpr hmatch
        | some (Instr.alu32 op dst src) =>
          simp only [hpinstr] at hmatch; exact decide_eq_true_eq.mpr hmatch
        | some (Instr.neg64 dst) =>
          simp only [hpinstr] at hmatch; exact decide_eq_true_eq.mpr hmatch
        | some (Instr.neg32 dst) =>
          simp only [hpinstr] at hmatch; exact decide_eq_true_eq.mpr hmatch
        | some (Instr.endian e sz dst) =>
          simp only [hpinstr] at hmatch; exact decide_eq_true_eq.mpr hmatch
        | some (Instr.load sz dst src off) =>
          simp only [hpinstr] at hmatch; exact decide_eq_true_eq.mpr hmatch
        | some (Instr.store sz dst off src) =>
          simp only [hpinstr] at hmatch; exact decide_eq_true_eq.mpr hmatch
        | some (Instr.lddw dst imm) =>
          simp only [hpinstr] at hmatch; exact decide_eq_true_eq.mpr hmatch
        | some (Instr.atomic sz op fetch dst src off) =>
          simp only [hpinstr] at hmatch; exact decide_eq_true_eq.mpr hmatch
        | some (Instr.call fid) =>
          simp only [hpinstr] at hmatch; exact decide_eq_true_eq.mpr hmatch
  · intro h target htarget
    have hall := List.all_eq_true.mp h target (List.mem_range.mpr htarget)
    rw [List.any_eq_true] at hall
    cases hall with
    | intro pc rest =>
      cases rest with
      | intro hpc_mem hmatch =>
        rw [List.mem_range] at hpc_mem
        refine ⟨pc, hpc_mem, ?_⟩
        match hpinstr : prog[pc]? with
        | none => simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch
        | some (Instr.ja off) => simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch
        | some (Instr.jmp64 op dst src off) =>
          simp only [hpinstr] at hmatch ⊢
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hmatch
          exact hmatch
        | some (Instr.jmp32 op dst src off) =>
          simp only [hpinstr] at hmatch ⊢
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hmatch
          exact hmatch
        | some (Instr.exit) =>
          simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch
        | some (Instr.alu64 op dst src) =>
          simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch
        | some (Instr.alu32 op dst src) =>
          simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch
        | some (Instr.neg64 dst) =>
          simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch
        | some (Instr.neg32 dst) =>
          simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch
        | some (Instr.endian e sz dst) =>
          simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch
        | some (Instr.load sz dst src off) =>
          simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch
        | some (Instr.store sz dst off src) =>
          simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch
        | some (Instr.lddw dst imm) =>
          simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch
        | some (Instr.atomic sz op fetch dst src off) =>
          simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch
        | some (Instr.call fid) =>
          simp only [hpinstr] at hmatch ⊢; exact decide_eq_true_eq.mp hmatch

instance decNoDeadCode (prog : Program) : Decidable (NoDeadCode prog) :=
  decidable_of_iff _ (noDeadCodeB_iff prog).symm

def verifiesB (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
    (pc : ℕ) (s : AState) : Bool :=
  verifyCheck prog mapSize callTypes (prog.size + 1) pc s

theorem verifiesB_sound (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
    (pc : ℕ) (s : AState) :
    verifiesB prog mapSize callTypes pc s = true →
    Verifies prog mapSize callTypes pc s :=
  fun h => verifyCheck_sound prog mapSize callTypes (prog.size + 1) pc s h

-- WellFormed boolean check

def wellFormedB (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType) : Bool :=
  noBackEdgesB prog && noDeadCodeB prog &&
  verifiesB prog mapSize callTypes 0 initialAState

theorem wellFormedB_sound (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType) :
    wellFormedB prog mapSize callTypes = true →
    WellFormed prog mapSize callTypes := by
  intro h
  simp only [wellFormedB, Bool.and_eq_true] at h
  cases h with
  | intro h12 h3 =>
    cases h12 with
    | intro h1 h2 =>
      exact ⟨(noBackEdgesB_iff prog).mpr h1,
             (noDeadCodeB_iff prog).mpr h2,
             verifiesB_sound prog mapSize callTypes 0 initialAState h3⟩

-- Main decidability instance

instance (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType) :
    Decidable (WellFormed prog mapSize callTypes) := by
  by_cases h : wellFormedB prog mapSize callTypes = true
  · exact isTrue (wellFormedB_sound prog mapSize callTypes h)
  · apply isFalse
    intro hwf
    apply h
    simp only [wellFormedB, Bool.and_eq_true]
    cases hwf with
    | intro h1 rest =>
      cases rest with
      | intro h2 h3 =>
        refine ⟨⟨(noBackEdgesB_iff prog).mp h1, (noDeadCodeB_iff prog).mp h2⟩, ?_⟩
        simp only [verifiesB]
        have hlt : 0 < prog.size := by
          have := verifies_pc_lt_size h3
          omega
        have hcomplete := verifyCheck_complete prog mapSize callTypes 0 initialAState h1 h3 hlt
        simp only [Nat.sub_zero] at hcomplete
        exact hcomplete

/- Verifier Soundness -/

def SafeAt (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
    (pc : ℕ) (abs : AState) : Prop :=
  match prog[pc]? with
  | none => False
  | some Instr.exit =>
      abs.regs Reg.r0 ≠ .not_init ∧ abs.refcount = 0
  | some (Instr.alu64 op dst src) =>
      abs.regs dst ≠ .not_init ∧ srcReadable abs src ∧
      (aluResult64 op (abs.regs dst) (srcType abs src)).isSome
  | some (Instr.alu32 op dst src) =>
      abs.regs dst ≠ .not_init ∧ srcReadable abs src ∧
      (aluResult32 op (abs.regs dst) (srcType abs src)).isSome
  | some (Instr.neg64 dst) => abs.regs dst = .scalar
  | some (Instr.neg32 dst) => abs.regs dst = .scalar
  | some (Instr.endian _ _ dst) => abs.regs dst = .scalar
  | some (Instr.ja off) =>
      0 ≤ (pc : Int) + 1 + offset16ToInt off
  | some (Instr.jmp64 _ dst src off) =>
      abs.regs dst ≠ .not_init ∧ srcReadable abs src ∧
      0 ≤ (pc : Int) + 1 + offset16ToInt off
  | some (Instr.jmp32 _ dst src off) =>
      abs.regs dst ≠ .not_init ∧ srcReadable abs src ∧
      0 ≤ (pc : Int) + 1 + offset16ToInt off
  | some (Instr.load sz _ src _) =>
      loadSafe (abs.regs src) sz abs mapSize
  | some (Instr.store sz dst _ src) =>
      srcReadable abs src ∧ storeSafe (abs.regs dst) sz mapSize
  | some (Instr.lddw _ _) => True
  | some (Instr.atomic _ op _ dst src _) =>
      (match abs.regs dst with
       | .ptr_map_value _ => True | .ptr_stack _ => True | _ => False) ∧
      abs.regs src = .scalar ∧
      (op = .cmpxchg → abs.regs Reg.r0 = .scalar)
  | some (Instr.call fid) =>
      abs.regs Reg.r1 ≠ .not_init ∧ abs.regs Reg.r2 ≠ .not_init ∧
      abs.regs Reg.r3 ≠ .not_init ∧ abs.regs Reg.r4 ≠ .not_init ∧
      abs.regs Reg.r5 ≠ .not_init ∧ callTypes fid ≠ .not_init

theorem verifier_progress (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
    (pc : ℕ) (abs : AState) :
    Verifies prog mapSize callTypes pc abs → ∃ instr, prog[pc]? = some instr := by
  intro hv
  cases hv with
  | exit pc s hprog _ _                           => exists Instr.exit
  | alu64 pc s op dst src t hprog _ _ _ _         => exists Instr.alu64 op dst src
  | alu32 pc s op dst src t hprog _ _ _ _         => exists Instr.alu32 op dst src
  | neg64 pc s dst hprog _ _                      => exists Instr.neg64 dst
  | neg32 pc s dst hprog _ _                      => exists Instr.neg32 dst
  | endian pc s e sz dst hprog _ _                => exists Instr.endian e sz dst
  | ja pc s off pc' hprog _ _ _                   => exists Instr.ja off
  | jmp64 pc s op dst src off pc' hprog _ _ _ _ _ _ => exists Instr.jmp64 op dst src off
  | jmp32 pc s op dst src off pc' hprog _ _ _ _ _ _ => exists Instr.jmp32 op dst src off
  | load pc s sz dst src off hprog _ _            => exists Instr.load sz dst src off
  | store pc s sz dst off src hprog _ _ _         => exists Instr.store sz dst off src
  | lddw pc s dst imm hprog _                     => exists Instr.lddw dst imm
  | atomic pc s sz op fetch dst src off hprog _ _ _ _ => exists Instr.atomic sz op fetch dst src off
  | call pc s fid hprog _ _ _ _ _ _ _            => exists Instr.call fid

theorem verifier_soundness (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType)
    (pc : ℕ) (abs : AState) :
    Verifies prog mapSize callTypes pc abs →
    SafeAt prog mapSize callTypes pc abs := by
  intro hv
  cases hv with
  | exit pc s hprog hr0 hrc =>
      simp only [SafeAt, hprog]; constructor <;> assumption
  | alu64 pc s op dst src t hprog hdst hsrc halu _ =>
      simp only [SafeAt, hprog]
      exact ⟨hdst, hsrc, Option.isSome_iff_exists.mpr ⟨t, halu⟩⟩
  | alu32 pc s op dst src t hprog hdst hsrc halu _ =>
      simp only [SafeAt, hprog]
      exact ⟨hdst, hsrc, Option.isSome_iff_exists.mpr ⟨t, halu⟩⟩
  | neg64 pc s dst hprog heq _ =>
      simp only [SafeAt, hprog]; exact heq
  | neg32 pc s dst hprog heq _ =>
      simp only [SafeAt, hprog]; exact heq
  | endian pc s e sz dst hprog heq _ =>
      simp only [SafeAt, hprog]; exact heq
  | ja pc s off pc' hprog hpc' hnn _ =>
      simp only [SafeAt, hprog]; rw [← hpc']; exact hnn
  | jmp64 pc s op dst src off pc' hprog hdst hsrc hpc' hnn _ _ =>
      simp only [SafeAt, hprog]; rw [← hpc']; exact ⟨hdst, hsrc, hnn⟩
  | jmp32 pc s op dst src off pc' hprog hdst hsrc hpc' hnn _ _ =>
      simp only [SafeAt, hprog]; rw [← hpc']; exact ⟨hdst, hsrc, hnn⟩
  | load pc s sz dst src off hprog hload _ =>
      simp only [SafeAt, hprog]; exact hload
  | store pc s sz dst off src hprog hsrc hstore _ =>
      simp only [SafeAt, hprog]; constructor <;> assumption
  | lddw pc s dst imm hprog _ =>
      simp only [SafeAt, hprog]
  | atomic pc s sz op fetch dst src off hprog hdst hsrc hcmp _ =>
      simp only [SafeAt, hprog]
      exact ⟨hdst, hsrc, hcmp⟩
  | call pc s fid hprog hr1 hr2 hr3 hr4 hr5 hfid _ =>
      simp only [SafeAt, hprog]
      exact ⟨hr1, hr2, hr3, hr4, hr5, hfid⟩

theorem wf_initial_safe (prog : Program) (mapSize : ℕ) (callTypes : BitVec 32 → RegType) :
    WellFormed prog mapSize callTypes →
    SafeAt prog mapSize callTypes 0 initialAState :=
  fun ⟨_, _, hv⟩ => verifier_soundness prog mapSize callTypes 0 initialAState hv

theorem verifier_abstract_preservation (prog : Program) (mapSize : ℕ)
    (callTypes : BitVec 32 → RegType) (pc : ℕ) (abs : AState)
    (regs : RegFile) (mem : Memory) (s' : State) :
    Verifies prog mapSize callTypes pc abs →
    Step prog { regs := regs, mem := mem, pc := pc } s' →
    ∃ abs', Verifies prog mapSize callTypes s'.pc abs' := by
  intro hv hstep
  cases hv with
  | exit pc₁ _ hprog _ _ =>
      cases hstep <;> simp_all
  | alu64 pc₁ _ op₁ dst₁ src₁ t₁ hprog _ _ _ hrec =>
      cases hstep with
      | alu64 => exists abs.setReg dst₁ t₁
      | alu32 => simp_all | neg64 => simp_all | neg32 => simp_all
      | endian => simp_all | ja => simp_all
      | jmp64_taken => simp_all | jmp64_fallthrough => simp_all
      | jmp32_taken => simp_all | jmp32_fallthrough => simp_all
      | store => simp_all | load => simp_all | lddw => simp_all
      | atomic_op => simp_all | call => simp_all
  | alu32 pc₁ _ op₁ dst₁ src₁ t₁ hprog _ _ _ hrec =>
      cases hstep with
      | alu32 => exists abs.setReg dst₁ t₁
      | alu64 => simp_all | neg64 => simp_all | neg32 => simp_all
      | endian => simp_all | ja => simp_all
      | jmp64_taken => simp_all | jmp64_fallthrough => simp_all
      | jmp32_taken => simp_all | jmp32_fallthrough => simp_all
      | store => simp_all | load => simp_all | lddw => simp_all
      | atomic_op => simp_all | call => simp_all
  | neg64 pc₁ _ dst₁ hprog _ hrec =>
      cases hstep with
      | neg64 => exists abs
      | alu64 => simp_all | alu32 => simp_all | neg32 => simp_all
      | endian => simp_all | ja => simp_all
      | jmp64_taken => simp_all | jmp64_fallthrough => simp_all
      | jmp32_taken => simp_all | jmp32_fallthrough => simp_all
      | store => simp_all | load => simp_all | lddw => simp_all
      | atomic_op => simp_all | call => simp_all
  | neg32 pc₁ _ dst₁ hprog _ hrec =>
      cases hstep with
      | neg32 => exists abs
      | alu64 => simp_all | alu32 => simp_all | neg64 => simp_all
      | endian => simp_all | ja => simp_all
      | jmp64_taken => simp_all | jmp64_fallthrough => simp_all
      | jmp32_taken => simp_all | jmp32_fallthrough => simp_all
      | store => simp_all | load => simp_all | lddw => simp_all
      | atomic_op => simp_all | call => simp_all
  | endian pc₁ _ e₁ sz₁ dst₁ hprog _ hrec =>
      cases hstep with
      | endian => exists abs
      | alu64 => simp_all | alu32 => simp_all | neg64 => simp_all
      | neg32 => simp_all | ja => simp_all
      | jmp64_taken => simp_all | jmp64_fallthrough => simp_all
      | jmp32_taken => simp_all | jmp32_fallthrough => simp_all
      | store => simp_all | load => simp_all | lddw => simp_all
      | atomic_op => simp_all | call => simp_all
  | ja pc₁ _ off₁ pc'₁ hprog hpc'₁ hnn hrec =>
      cases hstep with
      | ja r m p off_s pc_s h hpc_s hnn_s =>
          simp only [hprog, Option.some.injEq] at h
          have hoff : off₁ = off_s := by simp only [Instr.ja.injEq] at h; exact h
          have hpc_eq : pc_s.toNat = pc'₁.toNat :=
            congrArg Int.toNat (hpc_s.trans (by rw [← hoff]; exact hpc'₁.symm))
          exists abs
          rw [hpc_eq]; exact hrec
      | alu64 => simp_all | alu32 => simp_all | neg64 => simp_all
      | neg32 => simp_all | endian => simp_all
      | jmp64_taken => simp_all | jmp64_fallthrough => simp_all
      | jmp32_taken => simp_all | jmp32_fallthrough => simp_all
      | store => simp_all | load => simp_all | lddw => simp_all
      | atomic_op => simp_all | call => simp_all
  | jmp64 pc₁ _ op₁ dst₁ src₁ off₁ pc'₁ hprog _ _ hpc'₁ _ hrec_t hrec_f =>
      -- jmp64_taken uses hrec_t; jmp64_fallthrough uses hrec_f
      cases hstep with
      | jmp64_taken r m p op_s dst_s src_s off_s pc_s h _ hpc_s _ =>
          simp only [hprog, Option.some.injEq] at h
          have hoff : off₁ = off_s := by simp only [Instr.jmp64.injEq] at h; exact h.2.2.2
          have hpc_eq : pc_s.toNat = pc'₁.toNat :=
            congrArg Int.toNat (hpc_s.trans (by rw [← hoff]; exact hpc'₁.symm))
          exact ⟨_, by rw [hpc_eq]; exact hrec_t⟩
      | jmp64_fallthrough _ _ _ _ _ _ _ h _ =>
          simp only [hprog, Option.some.injEq] at h; exact ⟨_, hrec_f⟩
      | alu64 => simp_all | alu32 => simp_all | neg64 => simp_all
      | neg32 => simp_all | endian => simp_all | ja => simp_all
      | jmp32_taken => simp_all | jmp32_fallthrough => simp_all
      | store => simp_all | load => simp_all | lddw => simp_all
      | atomic_op => simp_all | call => simp_all
  | jmp32 pc₁ _ op₁ dst₁ src₁ off₁ pc'₁ hprog _ _ hpc'₁ _ hrec_t hrec_f =>
      cases hstep with
      | jmp32_taken r m p op_s dst_s src_s off_s pc_s h _ hpc_s _ =>
          simp only [hprog, Option.some.injEq] at h
          have hoff : off₁ = off_s := by simp only [Instr.jmp32.injEq] at h; exact h.2.2.2
          have hpc_eq : pc_s.toNat = pc'₁.toNat :=
            congrArg Int.toNat (hpc_s.trans (by rw [← hoff]; exact hpc'₁.symm))
          exact ⟨_, by rw [hpc_eq]; exact hrec_t⟩
      | jmp32_fallthrough _ _ _ _ _ _ _ h _ =>
          simp only [hprog, Option.some.injEq] at h; exact ⟨_, hrec_f⟩
      | alu64 => simp_all | alu32 => simp_all | neg64 => simp_all
      | neg32 => simp_all | endian => simp_all | ja => simp_all
      | jmp64_taken => simp_all | jmp64_fallthrough => simp_all
      | store => simp_all | load => simp_all | lddw => simp_all
      | atomic_op => simp_all | call => simp_all
  | load pc₁ _ sz₁ dst₁ src₁ off₁ hprog _ hrec =>
      cases hstep with
      | load => exists abs.setReg dst₁ .scalar
      | alu64 => simp_all | alu32 => simp_all | neg64 => simp_all
      | neg32 => simp_all | endian => simp_all | ja => simp_all
      | jmp64_taken => simp_all | jmp64_fallthrough => simp_all
      | jmp32_taken => simp_all | jmp32_fallthrough => simp_all
      | store => simp_all | lddw => simp_all
      | atomic_op => simp_all | call => simp_all
  | store pc₁ _ sz₁ dst₁ off₁ src₁ hprog _ _ hrec =>
      cases hstep with
      | store => exists storeSuccState abs dst₁ off₁ sz₁
      | alu64 => simp_all | alu32 => simp_all | neg64 => simp_all
      | neg32 => simp_all | endian => simp_all | ja => simp_all
      | jmp64_taken => simp_all | jmp64_fallthrough => simp_all
      | jmp32_taken => simp_all | jmp32_fallthrough => simp_all
      | load => simp_all | lddw => simp_all
      | atomic_op => simp_all | call => simp_all
  | lddw pc₁ _ dst₁ imm₁ hprog hrec =>
      cases hstep with
      | lddw => exists abs.setReg dst₁ .scalar
      | alu64 => simp_all | alu32 => simp_all | neg64 => simp_all
      | neg32 => simp_all | endian => simp_all | ja => simp_all
      | jmp64_taken => simp_all | jmp64_fallthrough => simp_all
      | jmp32_taken => simp_all | jmp32_fallthrough => simp_all
      | store => simp_all | load => simp_all
      | atomic_op => simp_all | call => simp_all
  | atomic pc₁ _ sz₁ op₁ fetch₁ dst₁ src₁ off₁ hprog _ _ _ hrec =>
      cases hstep with
      | atomic_op => exists atomicSuccState abs op₁ fetch₁ src₁
      | alu64 => simp_all | alu32 => simp_all | neg64 => simp_all
      | neg32 => simp_all | endian => simp_all | ja => simp_all
      | jmp64_taken => simp_all | jmp64_fallthrough => simp_all
      | jmp32_taken => simp_all | jmp32_fallthrough => simp_all
      | store => simp_all | load => simp_all | lddw => simp_all
      | call => simp_all
  | call pc₁ _ fid₁ hprog _ _ _ _ _ _ hrec =>
      cases hstep with
      | call =>
          exists if callTypes fid₁ = .ptr_socket
                 then { afterCall abs (callTypes fid₁) with refcount := abs.refcount + 1 }
                 else afterCall abs (callTypes fid₁)
      | alu64 => simp_all | alu32 => simp_all | neg64 => simp_all
      | neg32 => simp_all | endian => simp_all | ja => simp_all
      | jmp64_taken => simp_all | jmp64_fallthrough => simp_all
      | jmp32_taken => simp_all | jmp32_fallthrough => simp_all
      | store => simp_all | load => simp_all | lddw => simp_all
      | atomic_op => simp_all

end Ebpf

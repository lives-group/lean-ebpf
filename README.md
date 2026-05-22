# eBPF Formalization in Lean 4

A mechanized formalization of the eBPF instruction set in Lean 4, including a
separation-logic-based program logic.

## Architecture

The formalization is organized in four layers that build on each other:

### 1. Instruction Set (`Instr.lean`, `Macros.lean`)

Defines the eBPF ISA following RFC 9669:

- **Registers**: `r0`–`r10` (`Reg`)
- **Instructions**: ALU 64/32, negation, byte-swap, loads/stores, jumps (`ja`,
  `jmp64`, `jmp32`), `call`, `exit`, `lddw`, and atomic operations
- **Program**: `Array Instr`
- `Macros.lean` provides assembly-style notation (`add64 r0, r1`, etc.) for
  writing programs inline

### 2. Concrete Semantics (`Semantics.lean`, `Interp.lean`, `InterpNF.lean`)

- **`State`**: register file (`Reg → BitVec 64`), flat byte-addressed memory
  (`BitVec 64 → BitVec 8`), and a program counter
- **`Semantics.lean`**: small-step `Step` relation (one constructor per
  instruction class), plus helpers `readMem`/`writeMem` for multi-byte access in
  little-endian order
- **`Interp.lean`**: fuel-based interpreter `interp` that returns `Option State`
- **`InterpNF.lean`**: fuel-free interpreter `interpNF`, defined by well-founded
  recursion under the `NoBackEdges` condition (all jump targets are strictly
  forward)
- **`InterpSoundness.lean`**: proves both interpreters agree when sufficient
  fuel is provided

### 3. Separation Logic (`EbpfLogic.lean`, `LogicSoundness.lean`)

**`EbpfLogic.lean`** defines:

- **`Heap`**: partial byte-addressed memory (`BitVec 64 → Option (BitVec 8)`)
- `Heap.Disjoint`, `Heap.union`, `Heap.Consistent` (heap agrees with physical
  memory)
- `readHeap`/`writeHeap`: heap reads/writes returning `Option`
- **Assertions** (`Assert = RegFile → Heap → Prop`): separating conjunction `⋆`,
  points-to `p ↦ v`, `emp`, existential lifting, and `HeapOnly`
- **WP combinators** `wp_alu64`, `wp_load`, `wp_store`, etc.: one per
  instruction

**`LogicSoundness.lean`** proves:

- `sem_rule_*`: each WP combinator is sound w.r.t. the small-step semantics
- `sem_rule_frame`: the frame rule (locality of heap operations)
- `htriple_sound`: the Hoare triple judgment `HTriple` is sound w.r.t.
  `SemTriple`
- `wf_sem_sound`: well-formed programs satisfy the VCG-generated precondition
- `interp_heapSafe`: the concrete interpreter preserves heap safety
- `wf_interp_sound`: end-to-end soundness connecting verification to interpreter
  termination and postcondition satisfaction

### 4. Abstract Interpreter / Verifier (`EbpfVerifier.lean`, `VCG.lean`)

**`EbpfVerifier.lean`** defines:

- **`RegType`**: abstract register type lattice — `scalar`, `ptr_ctx`,
  `ptr_map_value`, `ptr_stack`, `ptr_packet`, `ptr_socket`, and null variants
- **`AState`**: abstract machine state (register types + stack initialization
  bitmap + reference count)
- **`Verifies`**: inductive predicate encoding the verifier's type rules for
  each instruction
- **`WellFormed`**: a program is well-formed if `Verifies` holds from PC 0 with
  the standard initial abstract state
- **`NoBackEdges`**: structural condition required for termination (all jumps
  are forward)

**`VCG.lean`** defines:

- `vcgWP`: weakest-precondition VCG that unfolds the program from a given PC and
  computes the precondition for a given postcondition `Q`
- `vcg_soundness`: the VCG produces a valid `HTriple` whenever `Verifies` holds
- `wf_vcg`: for a well-formed program the VCG yields a complete Hoare triple

## Key Theorems

| Theorem                     | File              | Statement                                                                        |
| --------------------------- | ----------------- | -------------------------------------------------------------------------------- |
| `htriple_sound`             | `LogicSoundness`  | `HTriple prog pc P Q → SemTriple prog pc P Q`                                    |
| `vcg_soundness`             | `VCG`             | `Verifies ∧ NoBackEdges → HTriple prog pc (vcgWP Q) Q`                           |
| `wf_sem_sound`              | `LogicSoundness`  | `WellFormed prog → SemTriple prog 0 (vcgWP Q) Q`                                 |
| `wf_interp_sound`           | `LogicSoundness`  | End-to-end: verified program + safe oracle ⇒ interpreter satisfies postcondition |
| `interpNF_terminates`       | `InterpSoundness` | `NoBackEdges prog → interpNF prog oracle hnb` always halts                       |
| `sem_triple_interpNF_sound` | `InterpSoundness` | `SemTriple` implies correct interpreter output                                   |

## Example: Verified Packet Filters (`PacketFilters.lean`)

`PacketFilters.lean` contains a complete end-to-end verification of two packet
filters: one for ARP and other for TCP/IPv4.

## Building

```bash
lake build
```

Requires [Lean 4](https://leanprover.github.io/) and
[Mathlib4](https://leanprover-community.github.io/mathlib4_docs/). The project
is tested in CI via the
[`leanprover/lean-action`](https://github.com/leanprover/lean-action) workflow
and documentation is published via
[`leanprover-community/docgen-action`](https://github.com/leanprover-community/docgen-action).

## References

- RFC 9669: Dave Thaler, _BPF Instruction Set Architecture (ISA)_, IETF,
  October 2024.
- Reynolds, J.C., _Separation Logic: A Logic for Shared Mutable Data
  Structures_, LICS 2002.

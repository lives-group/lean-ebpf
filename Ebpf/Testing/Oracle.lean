import Ebpf.Interp
import Ebpf.LogicSoundness
import Ebpf.Testing.Generators

namespace Ebpf.Testing

open Ebpf

def trivialOracle : CallOracle :=
  fun _fid regs mem => (regs.set Reg.r0 0, mem)

theorem trivialOracle_ok : OracleOk trivialOracle := by
  intro fid regs mem r hr
  simp only [trivialOracle, RegFile.set]
  have : r ≠ Reg.r0 := by
    simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  simp [this]

theorem trivialOracle_heapSafe (h : Heap) : OracleHeapSafe trivialOracle h :=
  memPreserving_heapSafe trivialOracle (fun _ _ _ => rfl) h


def idOracle : CallOracle :=
  fun _fid regs mem => (regs, mem)

theorem idOracle_ok : OracleOk idOracle := by
  intro _fid _regs _mem _r _hr; rfl

theorem idOracle_heapSafe (h : Heap) : OracleHeapSafe idOracle h :=
  memPreserving_heapSafe idOracle (fun _ _ _ => rfl) h

end Ebpf.Testing

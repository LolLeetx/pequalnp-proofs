import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22302

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 20] }], output := 22 }

end PEqualNP.Outside.L_meta_22302

theorem PEqualNP.Outside.L_meta_22302 :
PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840637 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨PEqualNP.Outside.L_meta_22302.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_22302.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel

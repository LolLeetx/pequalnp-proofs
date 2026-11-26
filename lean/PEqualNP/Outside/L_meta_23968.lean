import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23968

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 10] }], output := 11 }

end PEqualNP.Outside.L_meta_23968

theorem PEqualNP.Outside.L_meta_23968 :
∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8653 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_23968.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_23968.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel

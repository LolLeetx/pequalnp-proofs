import Mathlib

namespace PEqualNP.Outside.L_lib_764

lemma sign_eq_prod (k : ℕ) (x z : Fin k → Bool) :
    (if (Finset.univ.filter (fun i => x i = true ∧ z i = true)).card % 2 = 0 then (1 : ℤ) else -1) =
      ∏ j, (if x j = true ∧ z j = true then (-1 : ℤ) else 1) := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  rcases Nat.even_or_odd (Finset.univ.filter (fun i => x i = true ∧ z i = true)).card with h | h
  · rw [h.neg_one_pow, if_pos (Nat.even_iff.mp h)]
  · rw [h.neg_one_pow, if_neg (by rw [Nat.odd_iff.mp h]; decide)]

lemma pair_sum (a b : Bool) (hab : a ≠ b) :
    (∑ c : Bool, (if a = true ∧ c = true then (-1 : ℤ) else 1) *
      (if b = true ∧ c = true then (-1 : ℤ) else 1)) = 0 := by
  cases a <;> cases b <;> simp_all

end PEqualNP.Outside.L_lib_764

open PEqualNP.Outside.L_lib_764 in
theorem PEqualNP.Outside.L_lib_764 : ∀ (k : ℕ) (x y : Fin k → Bool), x ≠ y →
  (∑ z : Fin k → Bool,
    (if (Finset.univ.filter (fun i => x i = true ∧ z i = true)).card % 2 = 0 then (1 : ℤ) else -1) *
    (if (Finset.univ.filter (fun i => y i = true ∧ z i = true)).card % 2 = 0 then (1 : ℤ) else -1)) = 0 := by
  intro k x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  simp_rw [sign_eq_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j c => (if x j = true ∧ c = true then (-1 : ℤ) else 1) *
      (if y j = true ∧ c = true then (-1 : ℤ) else 1))]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (pair_sum (x i) (y i) hi)

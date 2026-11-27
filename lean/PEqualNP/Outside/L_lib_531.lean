import Mathlib

open Finset

theorem PEqualNP.Outside.L_lib_531 : ∀ (m : ℕ) (p : Fin m → ℝ),
  (∀ i, 0 < p i) → (∑ i, p i) = 1 →
  (∀ i j, i ≤ j → p j ≤ p i) →
  let G := ∑ i, (i.val+1 : ℝ)*p i
  let H := ∑ i : Fin m, 1/(i.val+1 : ℝ)
  let S := ∑ i, Real.sqrt (p i)
  (∀ perm : Equiv.Perm (Fin m), G ≤ ∑ i, (i.val+1 : ℝ)*p (perm i)) ∧
    S^2 ≤ G*H ∧ G ≤ S^2 := by
  intro m p hpos _ hmono G H S
  refine ⟨?_, ?_, ?_⟩
  · intro perm
    have hav : Antivary (fun i : Fin m => (i.val + 1 : ℝ)) p := by
      intro i j hij
      have : ¬ (i ≤ j) := fun h => absurd (hmono i j h) (not_le.mpr hij)
      have hji : j < i := not_le.mp this
      have : (j.val : ℝ) < i.val := by exact_mod_cast hji
      linarith
    exact hav.sum_mul_le_sum_mul_comp_perm
  · have key := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun i => Real.sqrt ((i.val + 1 : ℝ) * p i)) (fun i => 1 / Real.sqrt (i.val + 1 : ℝ))
    have h1 : ∀ i : Fin m, Real.sqrt ((i.val + 1 : ℝ) * p i) * (1 / Real.sqrt (i.val + 1 : ℝ))
        = Real.sqrt (p i) := by
      intro i
      have hc : (0 : ℝ) < i.val + 1 := by positivity
      have hs : Real.sqrt (i.val + 1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
      rw [Real.sqrt_mul hc.le, mul_one_div, mul_comm (Real.sqrt _) (Real.sqrt (p i)), mul_div_assoc,
        div_self hs, mul_one]
    have h2 : ∀ i : Fin m, Real.sqrt ((i.val + 1 : ℝ) * p i) ^ 2 = (i.val + 1 : ℝ) * p i := by
      intro i
      exact Real.sq_sqrt (mul_nonneg (by positivity) (hpos i).le)
    have h3 : ∀ i : Fin m, (1 / Real.sqrt (i.val + 1 : ℝ)) ^ 2 = 1 / (i.val + 1 : ℝ) := by
      intro i
      rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
    simp only [h1, h2, h3] at key
    exact key
  · have hrow : ∀ i : Fin m, (i.val + 1 : ℝ) * p i ≤ ∑ j, Real.sqrt (p i) * Real.sqrt (p j) := by
      intro i
      have hcard : ((Finset.Iic i).card : ℝ) = i.val + 1 := by
        rw [Fin.card_Iic]; push_cast; ring
      calc (i.val + 1 : ℝ) * p i = ∑ _j ∈ Finset.Iic i, Real.sqrt (p i) * Real.sqrt (p i) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard, Real.mul_self_sqrt (hpos i).le]
        _ ≤ ∑ j ∈ Finset.Iic i, Real.sqrt (p i) * Real.sqrt (p j) := by
            apply Finset.sum_le_sum
            intro j hj
            apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
            exact Real.sqrt_le_sqrt (hmono j i (Finset.mem_Iic.mp hj))
        _ ≤ ∑ j, Real.sqrt (p i) * Real.sqrt (p j) :=
            Finset.sum_le_univ_sum_of_nonneg (fun j => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc G ≤ ∑ i, ∑ j, Real.sqrt (p i) * Real.sqrt (p j) := Finset.sum_le_sum (fun i _ => hrow i)
      _ = S ^ 2 := by rw [sq, Finset.sum_mul_sum]

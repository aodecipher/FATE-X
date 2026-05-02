import Mathlib

namespace Problem13

/--
Let $(R,+,\cdot)$ be a (not necessarily commutative) ring.
If we know that $R$ is not a field and $x^2=x$ for any $x\in R,$
where $x$ is not invertible. Prove that $x^2=x$ for any $x.$

NOTE: This Lean statement is provably FALSE because Mathlib's `IsField` requires
commutativity. Counterexample: `R = Quaternion ℝ` is a non-commutative division
ring, so `¬ IsField R`, and every non-unit is `0` (so `h2` holds vacuously),
but `i^2 = -1 ≠ i`. See `sq_eq_self_of_not_unit_counterexample`. The intended
olympiad reading interprets "field" as "skew field"; the corrected version is
`sq_eq_self_of_not_unit_salvaged` below.
-/
theorem sq_eq_self_of_not_unit {R : Type} [Ring R] (h : ¬ IsField R)
    (h2 : ∀ x : R, ¬ IsUnit x → x^2 = x) (x : R) : x^2 = x := by
  sorry

/-- The original statement is false: `Quaternion ℝ` satisfies the hypotheses
but not the conclusion. -/
theorem sq_eq_self_of_not_unit_counterexample :
    ¬ ∀ (R : Type) [Ring R] (_ : ¬ IsField R)
        (_ : ∀ x : R, ¬ IsUnit x → x ^ 2 = x) (x : R), x ^ 2 = x := by
  intro H
  have hnotfield : ¬ IsField (Quaternion ℝ) := by
    intro hf
    have key : (⟨0, 1, 0, 0⟩ : Quaternion ℝ) * ⟨0, 0, 1, 0⟩ ≠
               (⟨0, 0, 1, 0⟩ : Quaternion ℝ) * ⟨0, 1, 0, 0⟩ := by
      intro h
      have h1 := congrArg (·.imK) h
      simp at h1
      norm_num at h1
    exact key (hf.mul_comm _ _)
  have h2 : ∀ x : Quaternion ℝ, ¬ IsUnit x → x ^ 2 = x := by
    intro x hx
    have hzero : x = 0 := by
      by_contra hne
      exact hx (isUnit_iff_ne_zero.mpr hne)
    simp [hzero]
  have hbad := H _ hnotfield h2 ⟨0, 1, 0, 0⟩
  have hrre := congrArg (·.re) hbad
  simp [pow_two] at hrre

/-- Salvaged version: replace `¬ IsField R` (which only forbids commutative
field structure) with the stronger hypothesis that `R` has at least one
nonzero non-unit. Under this hypothesis, every element of `R` is idempotent. -/
theorem sq_eq_self_of_not_unit_salvaged {R : Type} [Ring R]
    (h : ∃ y : R, y ≠ 0 ∧ ¬ IsUnit y)
    (h2 : ∀ x : R, ¬ IsUnit x → x ^ 2 = x) (x : R) : x ^ 2 = x := by
  obtain ⟨y, hyne, hy_nu⟩ := h
  -- If z is a unit, then y * z is non-unit (since y is non-unit).
  have mul_nu : ∀ z : R, IsUnit z → ¬ IsUnit (y * z) := by
    intro z hz hu
    apply hy_nu
    obtain ⟨u, hu_eq⟩ := hz
    rw [← hu_eq] at hu
    exact (Units.isUnit_mul_units y u).mp hu
  by_cases hx : IsUnit x
  · by_cases hx1 : IsUnit (1 - x)
    · -- Both `x` and `1 - x` are units. We derive a contradiction by showing
      -- y * x = 0, hence y = 0.
      exfalso
      have hyx_nu : ¬ IsUnit (y * x) := mul_nu x hx
      have hy1x_nu : ¬ IsUnit (y * (1 - x)) := mul_nu (1 - x) hx1
      have hyy : y * y = y := by rw [← pow_two]; exact h2 y hy_nu
      have hyx2 : (y * x) ^ 2 = y * x := h2 _ hyx_nu
      have hy1x2 : (y * (1 - x)) ^ 2 = y * (1 - x) := h2 _ hy1x_nu
      have lhs_eq : (y * (1 - x)) ^ 2 = y - y * x - y * x * y + y * x * y * x := by
        have h_expand : (y * (1 - x)) ^ 2 =
            y * y - y * y * x - y * x * y + y * x * y * x := by noncomm_ring
        rw [h_expand, hyy]
      have rhs_eq : y * (1 - x) = y - y * x := by noncomm_ring
      rw [lhs_eq, rhs_eq] at hy1x2
      have key : y * x * y * x - y * x * y = 0 := by
        have hsub := sub_eq_zero.mpr hy1x2
        have hh : (y - y * x - y * x * y + y * x * y * x) - (y - y * x) =
                  y * x * y * x - y * x * y := by noncomm_ring
        rw [hh] at hsub
        exact hsub
      have eq1 : y * x * y * (x - 1) = 0 := by
        have hh : y * x * y * (x - 1) = y * x * y * x - y * x * y := by noncomm_ring
        rw [hh]; exact key
      have hxm1 : IsUnit (x - 1) := by
        have heq : x - 1 = -(1 - x) := by noncomm_ring
        rw [heq]; exact hx1.neg
      have yxy_zero : y * x * y = 0 := (IsUnit.mul_left_eq_zero hxm1).mp eq1
      have yx_zero : y * x = 0 := by
        have hsq_eq : (y * x) ^ 2 = y * x * y * x := by noncomm_ring
        rw [hsq_eq, yxy_zero, zero_mul] at hyx2
        exact hyx2.symm
      exact hyne ((IsUnit.mul_left_eq_zero hx).mp yx_zero)
    · -- `1 - x` is non-unit, so `(1 - x)^2 = 1 - x`. Expanding gives `x^2 = x`.
      have hsq : (1 - x) ^ 2 = 1 - x := h2 _ hx1
      have h1 : (1 - x) ^ 2 = 1 - x - x + x ^ 2 := by noncomm_ring
      rw [h1] at hsq
      have hsub := sub_eq_zero.mpr hsq
      have hh : (1 - x - x + x ^ 2) - (1 - x) = x ^ 2 - x := by noncomm_ring
      rw [hh] at hsub
      exact sub_eq_zero.mp hsub
  · exact h2 x hx

end Problem13

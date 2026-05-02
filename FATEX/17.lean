import Mathlib

namespace Problem17

/-- The square of `(√2 : ℂ)` is `2`. (Useful for arguments where one wants to
exhibit `√2 ∈ K` as a square root of `2`.) -/
private lemma sq_sqrt_two_complex : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  norm_cast
  rw [sq, Real.mul_self_sqrt (by norm_num)]

/-- Lower bound (rank ≥ ℵ₀): if `K` is maximal with `√2 ∉ K`, then `ℂ` is not finite-dimensional
over `K`. The argument uses that finrank = 1 forces `K = ⊤`, which contradicts `h_nmem`,
and finrank ≥ 2 case relies on Artin–Schreier (which is not yet in Mathlib here, so we leave
it as a focused sorry). -/
private lemma not_module_finite_of_maximal
    (K : Subfield ℂ) (h_nmem : (Real.sqrt 2 : ℂ) ∉ K)
    (h : ∀ (L : Subfield ℂ), K ≤ L → (Real.sqrt 2 : ℂ) ∉ L → K = L) :
    ¬ Module.Finite K ℂ := by
  intro hfin
  -- finrank K ℂ is a positive natural number.
  have halg : Algebra.IsAlgebraic K ℂ := Algebra.IsAlgebraic.of_finite K ℂ
  -- Case-split by finrank value.
  have hpos : 0 < Module.finrank K ℂ := Module.finrank_pos
  rcases (Nat.lt_or_ge (Module.finrank K ℂ) 2) with h1 | h2
  · -- finrank K ℂ ≤ 1, so finrank = 1 (since it's positive)
    have hfr : Module.finrank K ℂ = 1 := by omega
    -- finrank = 1: ⊥ = ⊤ as subalgebras of ℂ over K
    have hbt : (⊥ : Subalgebra K ℂ) = ⊤ := by
      rw [Subalgebra.bot_eq_top_iff_finrank_eq_one]
      exact hfr
    -- Then √2 belongs to K (i.e., is in the image of algebraMap K ℂ).
    apply h_nmem
    have h_in : ((Real.sqrt 2 : ℝ) : ℂ) ∈ (⊤ : Subalgebra K ℂ) := Algebra.mem_top
    rw [← hbt] at h_in
    rw [Algebra.mem_bot] at h_in
    obtain ⟨x, hx⟩ := h_in
    -- algebraMap K ℂ x = (Real.sqrt 2 : ℂ), so (Real.sqrt 2 : ℂ) ∈ K
    have hxsqrt : (x : ℂ) = (Real.sqrt 2 : ℂ) := hx
    rw [← hxsqrt]
    exact x.2
  · -- finrank K ℂ ≥ 2: requires Artin-Schreier (not yet in Mathlib in this form).
    -- Artin–Schreier: if a finite proper extension is algebraically closed, the degree is 2
    -- and the base is real closed. Real closed fields contain square roots of nonneg elements,
    -- so 2 = (√2)^2 with √2 ∈ K, contradiction.
    sorry

theorem countable_index_of_maximal_subfield_sqrt_2_nmem
    (K : Subfield ℂ) (h_nmem : (Real.sqrt 2 : ℂ) ∉ K)
    (h : ∀ (L : Subfield ℂ), K ≤ L → (Real.sqrt 2 : ℂ) ∉ L → K = L) :
    Module.rank K ℂ = Cardinal.aleph0 := by
  -- We prove the rank equals ℵ₀ by showing ℵ₀ ≤ rank ≤ ℵ₀.
  apply le_antisymm
  · -- Upper bound: rank K ℂ ≤ ℵ₀.
    -- This is the deep direction relying on a structural argument about algebraic
    -- extensions of K being countably generated. It is left as a focused sorry.
    sorry
  · -- Lower bound: ℵ₀ ≤ rank K ℂ.
    rw [← not_lt, Module.rank_lt_aleph0_iff]
    exact not_module_finite_of_maximal K h_nmem h

end Problem17

import Mathlib

namespace Problem14

/--
Show that if $R$ is a unique factorization domain such that the quotient field of $R$ is isomorphic
to $\mathbb{R}$, then R is isomorphic to $\mathbb{R}$.
-/
theorem isomorphic_real_of_fractionRing_isomorphic_real_of_UFD (R : Type) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h : Nonempty ((FractionRing R) ≃+* ℝ)) :
    Nonempty (R ≃+* ℝ) := by
  obtain ⟨φ⟩ := h
  -- Auxiliary: if `p` is prime in `R` and its image in `ℝ` is positive, then `p` is a square in `R`.
  have prime_pos_isSquare : ∀ p : R, Prime p →
      0 < φ (algebraMap R (FractionRing R) p) → IsSquare p := by
    intro p hp hpos
    set qK : FractionRing R := algebraMap R (FractionRing R) p with hqK
    set sR : ℝ := Real.sqrt (φ qK) with hsR
    have hsR_sq : sR ^ 2 = φ qK := Real.sq_sqrt hpos.le
    set s : FractionRing R := φ.symm sR with hs
    have hs_sq : s ^ 2 = qK := by
      apply φ.injective
      rw [map_pow, show φ s = sR from φ.apply_symm_apply sR, hsR_sq]
    -- s is integral over R via X^2 - C p
    have hs_int : IsIntegral R s := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.C p, Polynomial.monic_X_pow_sub_C p two_ne_zero, ?_⟩
      simp [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_C, hs_sq, hqK]
    -- UFD ⟹ integrally closed: s = algebraMap t for some t ∈ R
    obtain ⟨t, ht⟩ := UniqueFactorizationMonoid.integer_of_integral hs_int
    -- ht : algebraMap R (FractionRing R) t = s
    have htK : algebraMap R (FractionRing R) (t ^ 2) =
        algebraMap R (FractionRing R) p := by
      rw [map_pow, ht, hs_sq]
    have ht_eq : t ^ 2 = p := IsFractionRing.injective R (FractionRing R) htK
    exact ⟨t, by rw [← ht_eq, sq]⟩
  -- No prime in R: combine sign cases with `Prime.not_isSquare`.
  have noPrime : ∀ p : R, ¬Prime p := by
    intro p hp
    have hp_ne : p ≠ 0 := hp.ne_zero
    have hqK_ne : algebraMap R (FractionRing R) p ≠ 0 := by
      rwa [Ne, IsFractionRing.to_map_eq_zero_iff (R := R) (K := FractionRing R)]
    have hφq_ne : φ (algebraMap R (FractionRing R) p) ≠ 0 := by
      rw [Ne, ← map_zero φ]; exact fun h => hqK_ne (φ.injective h)
    rcases lt_or_gt_of_ne hφq_ne with hneg | hpos
    · have hp_neg_pos : 0 < φ (algebraMap R (FractionRing R) (-p)) := by
        rw [map_neg, map_neg]; linarith
      exact (Prime.not_isSquare hp.neg) (prime_pos_isSquare (-p) hp.neg hp_neg_pos)
    · exact (Prime.not_isSquare hp) (prime_pos_isSquare p hp hpos)
  -- R is a field: every nonzero element is a unit (else has a prime factor).
  have hRfield : IsField R := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro a ha
    by_contra hno_inv
    push_neg at hno_inv
    have ha_not_unit : ¬IsUnit a := by
      rintro ⟨u, rfl⟩
      exact hno_inv ↑u⁻¹ u.mul_inv
    obtain ⟨p, hp_irr, _⟩ := WfDvdMonoid.exists_irreducible_factor ha_not_unit ha
    exact noPrime p (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irr)
  -- Construct the isomorphism R ≃+* ℝ.
  letI : Field R := hRfield.toField
  refine ⟨RingEquiv.ofBijective ((φ : FractionRing R →+* ℝ).comp
    (algebraMap R (FractionRing R))) ⟨?_, ?_⟩⟩
  · exact φ.injective.comp (IsFractionRing.injective R (FractionRing R))
  · intro y
    obtain ⟨z, rfl⟩ := φ.surjective y
    obtain ⟨x, b, hb_mem, h_eq⟩ :=
      IsFractionRing.div_surjective (A := R) (K := FractionRing R) z
    have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero hb_mem
    refine ⟨x * b⁻¹, ?_⟩
    show φ (algebraMap R (FractionRing R) (x * b⁻¹)) = φ z
    congr 1
    rw [map_mul, map_inv₀, ← div_eq_mul_inv, h_eq]

end Problem14

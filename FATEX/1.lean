import Mathlib

namespace Problem1

/--
Let $R$ be a UFD with two nonassociate prime elements $p$ and $q$ such that every prime
element is an associate of either $p$ or $q$. Prove that $R$ is a PID.
-/
theorem isPrincipalIdealRing_of_associated_or_associated {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {p q : R} (hp : Prime p) (hq : Prime q) (hpq : ¬ Associated p q)
    (h : ∀ {x : R}, Prime x → Associated x p ∨ Associated x q) :
    IsPrincipalIdealRing R := by
  refine IsPrincipalIdealRing.of_prime_ne_bot ?_
  intro P hP hP_ne_bot
  -- Step 1: every element of P is divisible by p or by q.
  have hP_sub : (P : Set R) ⊆ (Ideal.span {p} : Set R) ∪ (Ideal.span {q} : Set R) := by
    intro x hx
    by_cases hx0 : x = 0
    · left
      simp [hx0, SetLike.mem_coe]
    have hx_nu : ¬ IsUnit x := fun hu => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
    obtain ⟨i, hi_irr, hi_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hx_nu hx0
    have hi_prime : Prime i := UniqueFactorizationMonoid.irreducible_iff_prime.mp hi_irr
    rcases h hi_prime with hip | hiq
    · left
      simp only [SetLike.mem_coe, Ideal.mem_span_singleton]
      exact (hip.symm.dvd).trans hi_dvd
    · right
      simp only [SetLike.mem_coe, Ideal.mem_span_singleton]
      exact (hiq.symm.dvd).trans hi_dvd
  -- Step 2: by Ideal.subset_union, P ≤ (p) or P ≤ (q).
  rcases (Ideal.subset_union (I := P) (J := Ideal.span {p}) (K := Ideal.span {q})).mp hP_sub
    with hPle | hPle
  all_goals
    obtain ⟨π, hπ_mem, hπ_prime⟩ := hP.exists_mem_prime_of_ne_bot hP_ne_bot
  · -- P ≤ (p). The prime element π ∈ P satisfies π ~ p (else q ∈ (p), contradiction).
    have hπp : Associated π p := by
      rcases h hπ_prime with hπp | hπq
      · exact hπp
      · exfalso
        have hq_dvd : p ∣ q := by
          have : q ∈ Ideal.span {p} := hPle (by
            obtain ⟨u, hu⟩ := hπq
            have : q = π * u := hu.symm
            rw [this]; exact P.mul_mem_right _ hπ_mem)
          exact Ideal.mem_span_singleton.mp this
        exact hpq (hp.associated_of_dvd hq hq_dvd)
    -- Show P = (p): both inclusions
    refine ⟨⟨p, ?_⟩⟩
    apply le_antisymm hPle
    rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨u, hu⟩ := hπp
    have hp_eq : p = π * u := hu.symm
    rw [hp_eq]; exact P.mul_mem_right _ hπ_mem
  · have hπq : Associated π q := by
      rcases h hπ_prime with hπp | hπq
      · exfalso
        have hp_dvd : q ∣ p := by
          have : p ∈ Ideal.span {q} := hPle (by
            obtain ⟨u, hu⟩ := hπp
            have : p = π * u := hu.symm
            rw [this]; exact P.mul_mem_right _ hπ_mem)
          exact Ideal.mem_span_singleton.mp this
        exact hpq ((hq.associated_of_dvd hp hp_dvd).symm)
      · exact hπq
    refine ⟨⟨q, ?_⟩⟩
    apply le_antisymm hPle
    rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨u, hu⟩ := hπq
    have hq_eq : q = π * u := hu.symm
    rw [hq_eq]; exact P.mul_mem_right _ hπ_mem

end Problem1

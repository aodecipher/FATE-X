import Mathlib

namespace Problem39

/--
Let \( R \) be a normal Noetherian domain, \( K \) its fraction field, \( L/K \) a finite
field extension, and \( \overline{R} \) the integral closure of \( R \) in \( L \).
Prove that only finitely many primes \( \mathfrak{P} \) of \( \overline{R} \) lie over a given
prime \( \mathfrak{p} \) of \( R \).
-/
theorem finite_primes_lies_over_of_finite_extension (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (L : Type) [Field L] [Algebra R L]
    [Algebra (FractionRing R) L] [IsScalarTower R (FractionRing R) L]
    [FiniteDimensional (FractionRing R) L] (p : Ideal R) [p.IsPrime] :
    (p.primesOver (integralClosure R L)).Finite := by
  -- Strategy: reduce to the separable case via the separable closure.
  -- Let K = FractionRing R, Ks = separableClosure K L. Then L/Ks is purely inseparable
  -- and Ks/K is finite separable.  Let Ss = integralClosure R Ks; by the separable case
  -- (`IsIntegralClosure.finite`) Ss is module-finite over R, hence quasi-finite, so
  -- (p.primesOver Ss).Finite. The inclusion Ss → integralClosure R L is injective and
  -- every element has a power in its range (by pure inseparability of L/Ks), so by
  -- `PrimeSpectrum.isHomeomorph_comap` the induced map on Spec is a bijection; in
  -- particular `P ↦ P ∩ Ss` is injective on `primesOver`, transporting finiteness.
  set K := FractionRing R
  set Ks := separableClosure K L
  haveI : IsScalarTower R Ks L :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R K L r,
          IsScalarTower.algebraMap_apply R K Ks r,
          IsScalarTower.algebraMap_apply K Ks L]
  haveI : Algebra.IsSeparable K Ks := separableClosure.isSeparable K L
  haveI : FiniteDimensional K Ks := inferInstance
  set Ss := integralClosure R Ks
  set S := integralClosure R L
  haveI : Module.Finite R Ss := IsIntegralClosure.finite R K Ks Ss
  have hSs_finite_primesOver : (p.primesOver Ss).Finite :=
    Algebra.QuasiFinite.finite_primesOver p
  -- The R-algebra hom Ss → S induced by Ks ↪ L.
  let f : Ss →ₐ[R] S := AlgHom.mapIntegralClosure
    ((IntermediateField.val Ks).restrictScalars R)
  let φ : Ss →+* S := f.toRingHom
  have hφ_inj : Function.Injective φ := by
    intro x y h
    have hL : (x.1 : L) = (y.1 : L) := congrArg (fun (z : S) => (z.1 : L)) h
    exact Subtype.ext ((IntermediateField.val Ks).injective hL)
  haveI : IsPurelyInseparable Ks L := separableClosure.isPurelyInseparable K L
  let q := ringExpChar Ks
  haveI : ExpChar Ks q := ringExpChar.expChar Ks
  have hq1 : 1 ≤ q := by
    show 1 ≤ ringExpChar (Ks : Type _)
    unfold ringExpChar; exact le_max_right _ _
  -- Every element of S has a positive power in the range of φ.
  have hφ_pow : ∀ x : S, ∃ n > 0, x ^ n ∈ φ.range := by
    intro x
    have ⟨n, hn⟩ := IsPurelyInseparable.pow_mem (F := Ks) (E := L) q (x : L)
    obtain ⟨y, hy⟩ := hn
    have hqpos : 0 < q ^ n := pow_pos (lt_of_lt_of_le Nat.zero_lt_one hq1) n
    refine ⟨q ^ n, hqpos, ?_⟩
    have hxn_int : IsIntegral R ((x : L) ^ q ^ n) := x.2.pow _
    rw [← hy] at hxn_int
    have hy_int : IsIntegral R y := IsIntegral.tower_bot_of_field hxn_int
    refine ⟨⟨y, hy_int⟩, ?_⟩
    apply Subtype.ext
    show ((IntermediateField.val Ks).restrictScalars R) y = (x : L) ^ q ^ n
    exact hy
  -- Spec φ is a homeomorphism, in particular injective.
  have h_homeo : IsHomeomorph (PrimeSpectrum.comap φ) := by
    apply PrimeSpectrum.isHomeomorph_comap φ hφ_pow
    rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ_inj]
    exact bot_le
  have hcomap_inj : Function.Injective (PrimeSpectrum.comap φ) := h_homeo.bijective.injective
  have hφ_commutes : φ.comp (algebraMap R Ss) = algebraMap R S := by
    ext r
    show (φ ((algebraMap R Ss) r) : L) = ((algebraMap R S) r : L)
    show (f ((algebraMap R Ss) r) : L) = ((algebraMap R S) r : L)
    rw [show f ((algebraMap R Ss) r) = (algebraMap R S) r from f.commutes r]
  -- Inject p.primesOver S into p.primesOver Ss via P ↦ P.comap φ.
  apply Set.Finite.of_finite_image (f := fun (P : Ideal S) => P.comap φ)
  · apply hSs_finite_primesOver.subset
    rintro J ⟨P, ⟨hPprime, hPover⟩, rfl⟩
    refine ⟨Ideal.comap_isPrime φ P, ⟨?_⟩⟩
    show p = (P.comap φ).comap (algebraMap R Ss)
    rw [Ideal.comap_comap, hφ_commutes]
    exact hPover.over
  · rintro P ⟨hP, _⟩ P' ⟨hP', _⟩ hh
    have : (PrimeSpectrum.comap φ ⟨P, hP⟩) = (PrimeSpectrum.comap φ ⟨P', hP'⟩) :=
      PrimeSpectrum.ext hh
    exact congrArg PrimeSpectrum.asIdeal (hcomap_inj this)

end Problem39

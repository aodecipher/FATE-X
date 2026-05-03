import Mathlib

namespace Problem32

open IsLocalRing

/--
Let \( A \) be a Noetherian local ring such that its completion \( \widehat{A} \) is a unique
factorization domain. Then \( A \) is a unique factorization domain.
-/
theorem UFD_of_adicCompletion_UFD (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain (AdicCompletion (maximalIdeal R) R)]
    [UniqueFactorizationMonoid (AdicCompletion (maximalIdeal R) R)] :
    ∃ (h : IsDomain R), UniqueFactorizationMonoid R := by
  -- Step 1: `IsDomain R`. Since `R` is Noetherian local, the canonical map
  -- `AdicCompletion.of : R →ₗ R̂` is injective by Hausdorff-ness (Krull intersection).
  -- Since `R̂` is a domain, `R` injects into a domain, hence is itself a domain.
  have hHaus : IsHausdorff (maximalIdeal R) R := inferInstance
  have hofinj : Function.Injective (AdicCompletion.of (maximalIdeal R) R) :=
    AdicCompletion.of_injective _ _
  -- The algebra map agrees with `AdicCompletion.of` on elements (both come from the
  -- same coherent family `n ↦ Submodule.Quotient.mk x`), hence is also injective.
  have halg : Function.Injective
      (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
    intro x y hxy
    apply hofinj
    apply Subtype.ext
    exact congrArg Subtype.val hxy
  have hdom : IsDomain R :=
    Function.Injective.isDomain (algebraMap R (AdicCompletion (maximalIdeal R) R)) halg
  refine ⟨hdom, ?_⟩
  -- Step 2: `UniqueFactorizationMonoid R` (Mori–Nagata UFD descent).
  -- OBSTRUCTION: this direction is the substantive content of Mori's theorem and
  -- is not available in Mathlib. A full proof needs:
  --   (a) faithful flatness of `R → R̂` (only flatness, `AdicCompletion.flat_of_isNoetherian`,
  --       is in Mathlib; faithful flatness for Noetherian local rings is missing);
  --   (b) descent of primality of elements along faithfully flat ring extensions
  --       (essentially, an irreducible `π` of `R` is prime in `R` iff `π` is prime in `R̂`,
  --       relying on `R/(π) → R̂/(π)` being faithfully flat);
  --   (c) `WfDvdMonoid R` from `IsNoetherianRing R` to get factorisation into irreducibles,
  --       then upgrade via `UniqueFactorizationMonoid.of_exists_prime_factors`.
  sorry

end Problem32

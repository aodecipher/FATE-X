import Mathlib

namespace Problem36

open Submodule LinearMap

/-- For an R-linear map `f : M →ₗ[R] N` and a generating family `s : ι → M`,
the annihilator of `f` (as element of `Hom`) equals the intersection of the
annihilators of the values `f (s i)` in `N`. -/
private lemma colon_singleton_linearMap_eq_iInf
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {ι : Type*} (s : ι → M) (hs : Submodule.span R (Set.range s) = ⊤)
    (f : M →ₗ[R] N) :
    (⊥ : Submodule R (M →ₗ[R] N)).colon {f} =
      ⨅ i, (⊥ : Submodule R N).colon {f (s i)} := by
  ext r
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Ideal.mem_iInf]
  constructor
  · intro hr i
    have : (r • f) (s i) = 0 := by rw [hr]; rfl
    simpa [LinearMap.smul_apply] using this
  · intro hr
    apply LinearMap.ext_on_range hs
    intro i
    have := hr i
    simpa [LinearMap.smul_apply] using this

/-- For nonzero `φ : M →ₗ[R] R⧸p` (with `p` prime), the annihilator equals `p`. -/
private lemma annihilator_linearMap_to_quotient
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {p : Ideal R} (hp : p.IsPrime) (φ : M →ₗ[R] R ⧸ p) (hφ : φ ≠ 0) :
    (⊥ : Submodule R (M →ₗ[R] R ⧸ p)).colon {φ} = p := by
  apply le_antisymm
  · -- r ∈ Ann φ ⟹ r ∈ p
    intro r hr
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
    by_contra hrp
    apply hφ
    ext m
    have key : (r • φ) m = 0 := by rw [hr]; rfl
    have hsm : r • φ m = (0 : R ⧸ p) := by
      have : (r • φ) m = r • φ m := rfl
      rw [this] at key; exact key
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (p : Submodule R R) (φ m)
    show φ m = (0 : R ⧸ p)
    rw [← ha] at hsm ⊢
    rw [← Submodule.Quotient.mk_smul] at hsm
    rw [Submodule.Quotient.mk_eq_zero] at hsm ⊢
    rcases hp.mem_or_mem (show r * a ∈ p from by simpa [smul_eq_mul] using hsm) with h | h
    · exact absurd h hrp
    · exact h
  · -- p ⊆ Ann φ
    intro r hr
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    ext m
    show (r • φ) m = 0
    rw [LinearMap.smul_apply]
    show r • φ m = (0 : R ⧸ p)
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (p : Submodule R R) (φ m)
    rw [← ha]
    rw [← Submodule.Quotient.mk_smul]
    rw [Submodule.Quotient.mk_eq_zero]
    show r • a ∈ p
    rw [smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr

/--
If \( R \) is Noetherian and \( M \) and \( N \) are finitely generated \( R \)-modules, show that
\[
\operatorname{Ass} \operatorname{Hom}_R(M, N) = \operatorname{Supp} M \cap \operatorname{Ass} N,
\]
where \( \operatorname{Supp} M \) is the set of all primes containing the annihilator of \( M \).
-/
theorem associatedPrimes_hom_eq_support_inter_associatedPrimes (R : Type) [CommRing R]
    [IsNoetherianRing R] (M N : Type) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.Finite R N] : associatedPrimes R (M →ₗ[R] N) =
    {p | p ∈ associatedPrimes R N ∧ Module.annihilator R M ≤ p} := by
  ext p
  constructor
  · -- (⊆) direction
    rintro ⟨hp, f, hf⟩
    -- Get a finite generating family for M
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
    refine ⟨?_, ?_⟩
    · -- Show p ∈ associatedPrimes R N
      -- We have Ann(f) = ⋂ᵢ Ann(f (s i))
      have hann : (⊥ : Submodule R (M →ₗ[R] N)).colon {f} =
          ⨅ i, (⊥ : Submodule R N).colon {f (s i)} :=
        colon_singleton_linearMap_eq_iInf s hs f
      have hp_eq : p = ⨅ i, (⊥ : Submodule R N).colon {f (s i)} := hf.trans hann
      -- Convert ⨅ over Fin n to a Finset.inf
      have hinf : (Finset.univ : Finset (Fin n)).inf
            (fun i => (⊥ : Submodule R N).colon {f (s i)}) =
          (⨅ i, (⊥ : Submodule R N).colon {f (s i)}) := by
        rw [Finset.inf_univ_eq_iInf]
      have hple : (Finset.univ : Finset (Fin n)).inf
          (fun i => (⊥ : Submodule R N).colon {f (s i)}) ≤ p := by
        rw [hinf, ← hp_eq]
      obtain ⟨i₀, _, hi₀⟩ := hp.inf_le'.mp hple
      -- p = ⨅ ≤ Ann(f (s i₀)) (any specific i)
      have hp_le : p ≤ (⊥ : Submodule R N).colon {f (s i₀)} := by
        rw [hp_eq]; exact iInf_le _ i₀
      exact ⟨hp, f (s i₀), le_antisymm hp_le hi₀⟩
    · -- Show Module.annihilator R M ≤ p
      intro r hrann
      rw [Module.mem_annihilator] at hrann
      rw [hf, Submodule.mem_colon_singleton, Submodule.mem_bot]
      ext m
      show (r • f) m = 0
      rw [LinearMap.smul_apply]
      have hkey : f (r • m) = r • f m := f.map_smul r m
      rw [hrann m, map_zero] at hkey
      exact hkey.symm
  · -- (⊇) direction
    sorry

end Problem36

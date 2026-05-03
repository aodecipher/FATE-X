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

/-- If `R` is Noetherian, `M` is finitely generated, and `p` is a prime with
`Module.annihilator R M ≤ p`, then there exists a nonzero `R`-linear map `M → R⧸p`.
Proved by Noetherian induction via `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`. -/
private theorem exists_nonzero_linearMap_to_quot_of_annihilator_le
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : p.IsPrime) (hMp : Module.annihilator R M ≤ p) :
    ∃ φ : M →ₗ[R] R ⧸ p, φ ≠ 0 := by
  revert hMp
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R (M := M) inferInstance
    (motive := fun N _ _ _ => Module.annihilator R N ≤ p →
      ∃ φ : N →ₗ[R] R ⧸ p, φ ≠ 0) ?_ ?_ ?_
  · -- Subsingleton case: Ann N = ⊤, so ⊤ ≤ p contradicts p.IsPrime
    intro N _ _ _ _ hN
    exfalso
    have hAnn : Module.annihilator R N = ⊤ := by
      rw [eq_top_iff]; intro r _
      rw [Module.mem_annihilator]; intro m
      exact Subsingleton.elim _ _
    rw [hAnn, top_le_iff] at hN
    exact hp.ne_top hN
  · -- Quotient case: N ≃ R⧸q for prime q. Build `factor ∘ e` using q ≤ p.
    intro N _ _ _ q e hN
    have hAnnRq : Module.annihilator R (R ⧸ q.asIdeal) = q.asIdeal :=
      Ideal.annihilator_quotient
    have hAnnN : Module.annihilator R N = q.asIdeal := by
      rw [LinearEquiv.annihilator_eq e, hAnnRq]
    rw [hAnnN] at hN
    refine ⟨(Submodule.factor hN) ∘ₗ (e : N →ₗ[R] R ⧸ q.asIdeal), ?_⟩
    intro h
    -- If the composition is zero, then `factor hN` is zero on the image of `e`,
    -- but `e` is surjective so `factor hN` is identically zero.
    have hsurj : Function.Surjective (Submodule.factor hN : R ⧸ q.asIdeal →ₗ[R] R ⧸ p) :=
      Submodule.factor_surjective hN
    have hfactor_zero : ∀ y : R ⧸ q.asIdeal, (Submodule.factor hN) y = 0 := by
      intro y
      obtain ⟨n, hn⟩ := e.surjective y
      have hh : ((Submodule.factor hN) ∘ₗ (e : N →ₗ[R] R ⧸ q.asIdeal)) n = 0 := by
        rw [h]; rfl
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hh
      rw [hn] at hh; exact hh
    -- Surjective + identically-zero ⟹ R⧸p subsingleton, contradicting `p ≠ ⊤`.
    have hsub : Subsingleton (R ⧸ p) := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨a, ha⟩ := hsurj x
      obtain ⟨b, hb⟩ := hsurj y
      rw [← ha, ← hb, hfactor_zero, hfactor_zero]
    haveI : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
    exact absurd hsub (not_subsingleton _)
  · -- SES case: 0 → N₁ →[f] N₂ →[g] N₃ → 0, with motive(N₁), motive(N₃).
    intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hexact ih₁ ih₃ hN₂
    by_cases hcase : Module.annihilator R N₃ ≤ p
    · -- Case A: pull back nonzero ψ : N₃ → R⧸p along the surjection g.
      obtain ⟨ψ, hψ⟩ := ih₃ hcase
      refine ⟨ψ ∘ₗ g, ?_⟩
      intro h
      apply hψ
      ext n₃
      obtain ⟨n₂, hn₂⟩ := hg n₃
      have : (ψ ∘ₗ g) n₂ = 0 := by rw [h]; rfl
      simp only [LinearMap.comp_apply, hn₂] at this
      exact this
    -- Case B: choose r ∈ Ann(N₃) \ p; show Ann(N₁) ≤ p, lift φ : N₁ → R⧸p
    -- to N₂ by ψ(n) := φ((ofInjective f hf).symm ⟨r • n, _⟩).
    obtain ⟨r, hr_ann, hr_p⟩ := Set.not_subset.mp hcase
    -- Ann(N₁) · Ann(N₃) ⊆ Ann(N₂): if s ∈ Ann(N₁), r' ∈ Ann(N₃), n ∈ N₂, then
    -- g(r'•n) = 0 so r'•n = f(n₁); then (s*r')•n = s•f(n₁) = f(s•n₁) = 0.
    have hAnnMul : Module.annihilator R N₁ * Module.annihilator R N₃ ≤
        Module.annihilator R N₂ := by
      rw [Ideal.mul_le]
      intro s hs r' hr'
      rw [Module.mem_annihilator]
      intro n
      have hgr : g (r' • n) = 0 := by
        rw [g.map_smul, Module.mem_annihilator.mp hr' (g n)]
      obtain ⟨n₁, hn₁⟩ := (hexact (r' • n)).mp hgr
      calc (s * r') • n = s • (r' • n) := by rw [mul_smul]
        _ = s • f n₁ := by rw [hn₁]
        _ = f (s • n₁) := by rw [f.map_smul]
        _ = f 0 := by rw [Module.mem_annihilator.mp hs n₁]
        _ = 0 := f.map_zero
    have hAnn1Mul3_le_p : Module.annihilator R N₁ * Module.annihilator R N₃ ≤ p :=
      hAnnMul.trans hN₂
    have hAnn1_le_p : Module.annihilator R N₁ ≤ p := by
      rcases (Ideal.IsPrime.mul_le hp).mp hAnn1Mul3_le_p with h | h
      · exact h
      · exact absurd h hcase
    obtain ⟨φ, hφ⟩ := ih₁ hAnn1_le_p
    -- The "multiply by r" map on N₂ has image in range f (= ker g, by exactness).
    have h_in_range : ∀ n : N₂, r • n ∈ LinearMap.range f := by
      intro n
      have hgr : g (r • n) = 0 := by
        rw [g.map_smul, Module.mem_annihilator.mp hr_ann (g n)]
      obtain ⟨n₁, hn₁⟩ := (hexact (r • n)).mp hgr
      exact ⟨n₁, hn₁⟩
    let mulr : N₂ →ₗ[R] N₂ := r • LinearMap.id
    let μ : N₂ →ₗ[R] LinearMap.range f := mulr.codRestrict (LinearMap.range f)
      (fun n => h_in_range n)
    let lift : N₂ →ₗ[R] N₁ := (LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ μ
    let ψ : N₂ →ₗ[R] R ⧸ p := φ ∘ₗ lift
    refine ⟨ψ, ?_⟩
    intro hψzero
    -- Show φ = 0, contradicting hφ.
    apply hφ
    ext n₁
    -- Compute ψ (f n₁) = r • φ n₁.
    have hμfn : (μ (f n₁) : N₂) = f (r • n₁) := by
      show r • f n₁ = f (r • n₁)
      rw [f.map_smul]
    have hlift : lift (f n₁) = r • n₁ := by
      show (LinearEquiv.ofInjective f hf).symm (μ (f n₁)) = r • n₁
      apply hf
      rw [LinearEquiv.ofInjective_symm_apply, hμfn]
    have hψfn : ψ (f n₁) = r • φ n₁ := by
      show φ (lift (f n₁)) = r • φ n₁
      rw [hlift, φ.map_smul]
    -- So ψ = 0 ⟹ r • φ n₁ = 0 in R⧸p, but r ∉ p and R⧸p is a domain ⟹ φ n₁ = 0.
    have hzero : r • φ n₁ = (0 : R ⧸ p) := by
      rw [← hψfn]
      show ψ (f n₁) = 0
      rw [hψzero]; rfl
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (p : Submodule R R) (φ n₁)
    show φ n₁ = 0
    rw [← ha] at hzero ⊢
    rw [← Submodule.Quotient.mk_smul] at hzero
    rw [Submodule.Quotient.mk_eq_zero] at hzero ⊢
    rcases hp.mem_or_mem (show r * a ∈ p from by simpa [smul_eq_mul] using hzero) with h | h
    · exact absurd h hr_p
    · exact h

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
    rintro ⟨⟨hp, y, hy⟩, hMle⟩
    -- Step 1: get a nonzero φ : M → R⧸p (uses Ann M ≤ p).
    obtain ⟨φ, hφ⟩ := exists_nonzero_linearMap_to_quot_of_annihilator_le hp hMle
    -- Step 2: build an injective ι : R⧸p → N from y, with Ann y = p.
    have hker : (p : Submodule R R) ≤ LinearMap.ker (LinearMap.toSpanSingleton R N y) := by
      intro r hr
      rw [LinearMap.mem_ker]
      show r • y = 0
      have : r ∈ (⊥ : Submodule R N).colon {y} := hy ▸ hr
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at this
      exact this
    have hker' : LinearMap.ker (LinearMap.toSpanSingleton R N y) ≤ (p : Submodule R R) := by
      intro r hr
      rw [LinearMap.mem_ker] at hr
      show r ∈ p
      rw [hy, Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact hr
    let ι : R ⧸ p →ₗ[R] N := Submodule.liftQ p (LinearMap.toSpanSingleton R N y) hker
    have hι_inj : Function.Injective ι := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot p _ hker hker'
    -- Step 3: f := ι ∘ φ, and Ann(f) = Ann(φ) = p.
    let f : M →ₗ[R] N := ι ∘ₗ φ
    have hf_apply : ∀ m, f m = ι (φ m) := fun _ => rfl
    refine ⟨hp, f, ?_⟩
    have hAnn_phi : (⊥ : Submodule R (M →ₗ[R] R ⧸ p)).colon {φ} = p :=
      annihilator_linearMap_to_quotient hp φ hφ
    rw [← hAnn_phi]
    apply le_antisymm
    · -- p ≤ Ann(f): r • φ = 0 ⟹ r • f = 0 (functorially)
      intro r hr
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      ext m
      simp only [LinearMap.zero_apply]
      show r • f m = 0
      rw [hf_apply, ← LinearMap.map_smul]
      have h1 : (r • φ) m = 0 := by rw [hr]; rfl
      have h2 : r • φ m = 0 := h1
      rw [h2, map_zero]
    · -- Ann(f) ≤ p: r • f = 0 ⟹ r • φ = 0 (using ι injective)
      intro r hr
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      ext m
      simp only [LinearMap.zero_apply]
      show (r • φ) m = 0
      show r • φ m = 0
      apply hι_inj
      rw [LinearMap.map_smul, ← hf_apply, map_zero]
      have : (r • f) m = 0 := by rw [hr]; rfl
      exact this

end Problem36

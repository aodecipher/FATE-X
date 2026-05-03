import Mathlib

namespace Problem40

open TensorProduct

/-- The image of `m ∈ M` under `(1 : K) ⊗ₜ - : M → K ⊗[R] M` lies in the `K`-span
of `(1 : K) ⊗ₜ f i` whenever `m` lies in the `R`-span of `range f`. -/
private lemma tmul_one_mem_span {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    {ι : Type} (f : ι → M) (K : Type) [CommRing K] [Algebra R K]
    (m : M) (hm : m ∈ Submodule.span R (Set.range f)) (c : K) :
    c ⊗ₜ[R] m ∈ Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[R] f i) := by
  refine Submodule.span_induction
    (p := fun z _ => c ⊗ₜ[R] z ∈ Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[R] f i))
    ?_ ?_ ?_ ?_ hm
  · rintro z ⟨i, rfl⟩
    have h1 : c ⊗ₜ[R] f i = c • ((1 : K) ⊗ₜ[R] f i) := by
      rw [TensorProduct.smul_tmul']; simp
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · simp
  · intro z₁ z₂ _ _ h₁ h₂
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _ h₁ h₂
  · intro a z _ hz
    have heq : c ⊗ₜ[R] (a • z) = (algebraMap R K a) • (c ⊗ₜ[R] z) := by
      simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
    rw [heq]
    exact Submodule.smul_mem _ _ hz

/-- For a minimal prime `p` of a reduced commutative ring `R`, the kernel of the composition
`R → R⧸p → FractionRing (R⧸p)` is exactly `p`. -/
private lemma ker_to_fractionRing_minimalPrime
    {R : Type} [CommRing R] [IsReduced R] {p : Ideal R} (hp : p ∈ minimalPrimes R) (x : R)
    (hx : algebraMap R (FractionRing (R ⧸ p)) x = 0) : x ∈ p := by
  have hp_prime : p.IsPrime := Ideal.minimalPrimes_isPrime hp
  -- algebraMap R (FractionRing (R⧸p)) factors as R → R⧸p → FractionRing (R⧸p).
  have hfact : (algebraMap R (FractionRing (R ⧸ p))) x =
      algebraMap (R ⧸ p) (FractionRing (R ⧸ p)) (Ideal.Quotient.mk p x) := by
    rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p))]
    rfl
  rw [hfact] at hx
  -- The map R⧸p → FractionRing (R⧸p) is injective since R⧸p is a domain.
  have hinj : Function.Injective (algebraMap (R ⧸ p) (FractionRing (R ⧸ p))) :=
    IsFractionRing.injective (R ⧸ p) (FractionRing (R ⧸ p))
  have : Ideal.Quotient.mk p x = 0 := by
    apply hinj
    rw [hx, map_zero]
  rwa [Ideal.Quotient.eq_zero_iff_mem] at this

/-- In a reduced ring with finitely many minimal primes, an element lying in every minimal prime
is zero. -/
private lemma eq_zero_of_mem_all_minimalPrimes
    {R : Type} [CommRing R] [IsReduced R] (x : R)
    (hx : ∀ p ∈ minimalPrimes R, x ∈ p) : x = 0 := by
  have hxnil : x ∈ nilradical R := by
    have hsi : sInf (minimalPrimes R) = (⊥ : Ideal R).radical :=
      Ideal.sInf_minimalPrimes (I := (⊥ : Ideal R))
    have : x ∈ sInf (minimalPrimes R) := Ideal.mem_sInf.mpr hx
    rw [hsi] at this
    exact this
  rcases hxnil with ⟨n, hn⟩
  exact IsReduced.eq_zero x ⟨n, hn⟩

set_option maxHeartbeats 800000 in
/-- The backward direction of the main theorem, separated for clarity. -/
private lemma backward_direction (R : Type) [CommRing R] [IsLocalRing R] [IsReduced R]
    (_h : (minimalPrimes R).Finite) (r : ℕ) (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hk : Module.rank (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] M) = r)
    (hp : ∀ p ∈ minimalPrimes R,
      Module.rank (FractionRing (R ⧸ p)) ((FractionRing (R ⧸ p)) ⊗[R] M) = r) :
    Module.Free R M ∧ Module.rank R M = r := by
  -- Step 1: Pick a basis of (k ⊗ M) over the residue field k.
  set k := IsLocalRing.ResidueField R with k_def
  have hkfr : Module.finrank k (k ⊗[R] M) = r := Module.finrank_eq_of_rank_eq hk
  -- Basis indexed by Fin r
  let bk : Module.Basis (Fin r) k (k ⊗[R] M) := Module.finBasisOfFinrankEq k _ hkfr
  -- Step 2: Lift bk to f : Fin r → M with 1 ⊗ f i = bk i.
  have hsurj : Function.Surjective (fun m : M => (1 : k) ⊗ₜ[R] m) :=
    TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective
  choose f hf using fun i => hsurj (bk i)
  -- Step 3: Define φ : (Fin r → R) →ₗ[R] M
  let φ : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R f
  -- Step 4: φ is surjective.
  have hsp : Submodule.span R (Set.range f) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis (R := R) (f := f) bk hf
  have hφ_surj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span R (Set.range f) := hsp ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun y _ => y ∈ LinearMap.range φ) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨i, rfl⟩
      refine ⟨Pi.single i 1, ?_⟩
      simp [φ, Fintype.linearCombination_apply_single]
    · exact ⟨0, by simp [φ]⟩
    · rintro y z _ _ ⟨ay, hy⟩ ⟨az, hz⟩
      exact ⟨ay + az, by simp [φ, hy, hz]⟩
    · rintro a y _ ⟨ay, hy⟩
      exact ⟨a • ay, by simp [φ, hy]⟩
  -- Step 5: φ is injective.
  have hφ_inj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    -- Show each component x i = 0 via membership in every minimal prime.
    funext i
    apply eq_zero_of_mem_all_minimalPrimes
    intro p hpmin
    apply ker_to_fractionRing_minimalPrime hpmin
    -- Set up K = FractionRing (R⧸p) and compute via tensor products.
    let K := FractionRing (R ⧸ p)
    have _hp_prime : p.IsPrime := Ideal.minimalPrimes_isPrime hpmin
    -- Define ψ : (Fin r → K) →ₗ[K] K ⊗[R] M
    let ψ : (Fin r → K) →ₗ[K] K ⊗[R] M :=
      Fintype.linearCombination K (fun i => (1 : K) ⊗ₜ[R] f i)
    -- ψ is surjective. We show range ψ ⊇ K-span of {1 ⊗ f i} ⊇ everything.
    have hrange_contains : ∀ i, ((1 : K) ⊗ₜ[R] f i) ∈ LinearMap.range ψ := by
      intro i
      refine ⟨Pi.single i 1, ?_⟩
      simp [ψ, Fintype.linearCombination_apply_single]
    have hψ_surj : Function.Surjective ψ := by
      rw [← LinearMap.range_eq_top, eq_top_iff]
      intro y _
      -- Show y ∈ range ψ by induction on y.
      let S : Submodule K (K ⊗[R] M) := LinearMap.range ψ
      change y ∈ S
      have hSspan : Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[R] f i) ≤ S := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hrange_contains i
      -- It suffices to show every element of K ⊗ M is in the K-span of {1 ⊗ f i}.
      apply hSspan
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · exact Submodule.zero_mem _
      · intro c m
        exact tmul_one_mem_span f K m (hsp ▸ Submodule.mem_top) c
      · intro y₁ y₂ hy₁ hy₂
        exact Submodule.add_mem _ hy₁ hy₂
    -- ψ is injective via dimension counting.
    have hKrank : Module.rank K (K ⊗[R] M) = (r : Cardinal) := hp p hpmin
    have hKfr : Module.finrank K (K ⊗[R] M) = r := Module.finrank_eq_of_rank_eq hKrank
    have hKfin_M : Module.Finite K (K ⊗[R] M) := Module.Finite.base_change R K M
    have hψ_inj : Function.Injective ψ := by
      have hfin_eq : Module.finrank K (Fin r → K) = Module.finrank K (K ⊗[R] M) := by
        rw [Module.finrank_pi, hKfr]; simp
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin_eq).mpr hψ_surj
    -- Compute ψ on (algebraMap ∘ x) and conclude.
    have key : ψ (fun i => algebraMap R K (x i)) = 0 := by
      have hsum : ∑ i, x i • f i = 0 := by
        have : φ x = ∑ i, x i • f i := Fintype.linearCombination_apply R f x
        rw [← this]; exact hx
      simp only [ψ, Fintype.linearCombination_apply]
      have rew : (∑ i, (algebraMap R K (x i)) • ((1 : K) ⊗ₜ[R] f i)) =
          (1 : K) ⊗ₜ[R] (∑ i, x i • f i) := by
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show (algebraMap R K (x i)) • ((1 : K) ⊗ₜ[R] f i) =
              (x i) • ((1 : K) ⊗ₜ[R] f i) from
            (algebraMap_smul (R := R) K (x i) ((1 : K) ⊗ₜ[R] f i))]
        rw [TensorProduct.tmul_smul]
      rw [rew, hsum, TensorProduct.tmul_zero]
    have h0 : (fun i => algebraMap R K (x i)) = 0 := hψ_inj (by simpa using key)
    exact congrFun h0 i
  -- Step 6: M ≃ Fin r → R, so Free of rank r.
  let e : (Fin r → R) ≃ₗ[R] M := LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  have hfree : Module.Free R M := Module.Free.of_equiv e
  have hrank : Module.rank R M = (r : Cardinal) := by
    rw [← e.rank_eq]
    simp
  exact ⟨hfree, hrank⟩

/--
Let $A$ be a reduced local ring with residue field $k$ and finite set $\Sigma$ of minimal primes.
For each $\mathfrak{p}\in\Sigma$, set $K(\mathfrak{p})=\mathrm{Frac}(A/\mathfrak{p})$.
Let $P$ be a finitely generated module. Show that $P$ is free of rank $r$ if and only if
$\dim_k(P\otimes_A k) = r$ and $\dim_{K(\mathfrak{p})}(P\otimes_A K(\mathfrak{p})) = r$
for each $\mathfrak{p}\in\Sigma$.
-/
theorem free_of_rank_iff (R : Type) [CommRing R] [IsLocalRing R] [IsReduced R]
    (h : (minimalPrimes R).Finite) (r : ℕ) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Free R M ∧ Module.rank R M = r ↔
    (Module.rank (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] M) = r ∧
    ∀ p ∈ minimalPrimes R,
    Module.rank (FractionRing (R ⧸ p)) ((FractionRing (R ⧸ p)) ⊗[R] M) = r) := by
  refine ⟨fun ⟨hfree, hrank⟩ => ⟨?_, ?_⟩, fun ⟨hk, hp⟩ => ?_⟩
  · -- forward: residue field rank
    have hbc := Module.rank_baseChange (R := IsLocalRing.ResidueField R) (S := R) (M' := M)
    rw [hrank, Cardinal.lift_id] at hbc
    exact hbc
  · -- forward: each minimal prime fraction field rank
    intro p hp
    have hp_prime : p.IsPrime := Ideal.minimalPrimes_isPrime hp
    have hbc := Module.rank_baseChange (R := FractionRing (R ⧸ p)) (S := R) (M' := M)
    rw [hrank, Cardinal.lift_id] at hbc
    exact hbc
  · -- backward: M is free of rank r (the substantive direction)
    exact backward_direction R h r M hk hp

end Problem40

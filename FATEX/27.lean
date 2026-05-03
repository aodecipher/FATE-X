import Mathlib

namespace Problem27

open Polynomial IntermediateField

/-- If `X^p - C a` is irreducible over `K`, `K` contains a primitive `p^2`-th root of unity, and
`p` is prime, then `X^(p^2) - C a` is also irreducible over `K`.  This is the analogue of
`X_pow_sub_C_irreducible_of_prime_pow` from mathlib for the prime power `n = 2`, where the
irreducibility of `X^(p^2) - C a` follows from a norm computation in the cyclic extension
`K(α)/K` where `α^p = a`.  The norm of `α` over `K` is `(-1)^(p+1) * a`; if `α` had a `p`-th root
in `K(α)`, then `(-1)^(p+1) * a` would be a `p`-th power in `K`, which (using `ζ^2 = -1` when
`p = 2`) contradicts the irreducibility of `X^p - C a`. -/
private lemma X_pow_sq_sub_C_irreducible {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ 2)) {a : K} (h : Irreducible (X ^ p - C a)) :
    Irreducible (X ^ (p ^ 2) - C a) := by
  have hsq : p ^ 2 = p * p := sq p
  rw [hsq]
  apply X_pow_mul_sub_C_irreducible h
  intro E _ _ x hx
  have hxinteg : IsIntegral K x := by
    by_contra hni
    rw [minpoly.eq_zero hni] at hx
    have h0 : (0 : K[X]).natDegree = (X ^ p - C a).natDegree := by rw [hx]
    rw [natDegree_zero, natDegree_X_pow_sub_C] at h0
    exact hp.pos.ne' h0.symm
  rw [X_pow_sub_C_irreducible_iff_of_prime hp]
  intro b hb
  set pb := IntermediateField.adjoin.powerBasis hxinteg with pb_def
  have hgen : pb.gen = AdjoinSimple.gen K x := IntermediateField.adjoin.powerBasis_gen hxinteg
  have hdim : pb.dim = p := by
    rw [IntermediateField.adjoin.powerBasis_dim hxinteg, hx]
    exact natDegree_X_pow_sub_C
  have hminpoly_gen : minpoly K pb.gen = X ^ p - C a := by
    rw [hgen, IntermediateField.minpoly_gen, hx]
  have hcoeff0 : (X ^ p - C a : K[X]).coeff 0 = -a := by
    rw [coeff_sub, coeff_X_pow, coeff_C_zero, if_neg hp.pos.ne'.symm, zero_sub]
  have hnorm : Algebra.norm K pb.gen = (-1) ^ (p + 1) * a := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim, hminpoly_gen, hcoeff0]
    ring
  have hNbp : (Algebra.norm K b) ^ p = (-1) ^ (p + 1) * a := by
    rw [← map_pow, hb, ← hgen, hnorm]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · -- p = 2: N(b)^2 = -a; using ζ^2 = -1 (since ζ is a primitive 4th root) we get
    -- a = (ζ * N(b))^2, contradicting `Irreducible (X^2 - C a)`.
    have hp2sign : ((-1 : K)) ^ (2 + 1) = -1 := by norm_num
    rw [hp2sign] at hNbp
    have hNbsq : Algebra.norm K b ^ 2 = -a := by linear_combination hNbp
    have hζ4 : ζ ^ 2 = -1 := by
      have h22 : (ζ ^ 2) ^ 2 = 1 := by
        rw [← pow_mul]; show ζ ^ (2 ^ 2) = 1; exact hζ.pow_eq_one
      have h2ne1 : ζ ^ 2 ≠ 1 := by
        intro heq
        have := hζ.dvd_of_pow_eq_one 2 heq
        omega
      have hsq2 : (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = 0 := by linear_combination h22
      rcases mul_eq_zero.mp hsq2 with hl | hr
      · exact absurd (sub_eq_zero.mp hl) h2ne1
      · linear_combination hr
    have ha_sq : (ζ * Algebra.norm K b) ^ 2 = a := by
      rw [mul_pow, hζ4]; linear_combination -hNbsq
    exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two (a := a)).mp h
      (ζ * Algebra.norm K b) ha_sq
  · -- p odd: N(b)^p = a directly contradicts `Irreducible (X^p - C a)`.
    have hp1even : Even (p + 1) := by
      rcases hodd with ⟨k, rfl⟩
      exact ⟨k + 1, by ring⟩
    have hpw : ((-1 : K)) ^ (p + 1) = 1 := hp1even.neg_one_pow
    rw [hpw, one_mul] at hNbp
    exact (X_pow_sub_C_irreducible_iff_of_prime hp (a := a)).mp h (Algebra.norm K b) hNbp

/--
Let $p$ be a prime number. Let $K/\mathbb{Q}$ be a finite extension, such that the $p^{2}$th
root of unity is contained in $K$. Let $L/K$ be a Galois extension of degree $p$, show that there
exists a Galois extension $L'/L$ of degree $p$, such that the extension $L'/K$ is Galois.
-/
theorem isGalois_and_rank_eq_of_isPrimitiveRoot_sq (p : ℕ) (hp : p.Prime) {K : Type} [Field K]
    [NumberField K] {ζ : K} (h : IsPrimitiveRoot ζ (p^2))
    {L : IntermediateField K (AlgebraicClosure K)} [IsGalois K L]
    (hdeg : Module.rank K L = p) :
    ∃ (L' : Type) (_ : Field L') (_ : Algebra K L')
    (_ : Algebra L L') (_ : IsScalarTower K L L'),
    IsGalois K L' ∧ IsGalois L L' ∧ Module.rank L L' = p := by
  -- Roadmap:
  --   * L/K is cyclic of degree p (Galois of prime degree).
  --   * Since K contains ζ_{p²}, in particular K contains ζ_p, so by Kummer theory
  --     L = K(α) for some α with α^p = a ∈ K*.
  --   * Set L' = L(β) ⊆ AlgebraicClosure K with β^p = α (equivalently β^{p²} = a).
  --   * Then L' is the splitting field over K of X^{p²} - a (since K contains ζ_{p²}),
  --     hence L'/K is Galois.
  --   * [L:K] = p, [L':K] = p², so [L':L] = p.
  --
  -- We package the Kummer construction into a single existence sorry producing an
  -- IntermediateField L' ⊆ AlgebraicClosure K containing L, of degree p² over K and
  -- Galois over K.  The remaining rank computation [L':L] = p is a second sorry.
  obtain ⟨L', hLL', hgal, hrank⟩ : ∃ L' : IntermediateField K (AlgebraicClosure K),
      L ≤ L' ∧ IsGalois K L' ∧ Module.rank K L' = (p : Cardinal) ^ 2 := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hf : Module.finrank K L = p := Module.finrank_eq_of_rank_eq hdeg
    have hfin : FiniteDimensional K L :=
      Module.finite_of_finrank_pos (by rw [hf]; exact hp.pos)
    rw [← IsGalois.card_aut_eq_finrank] at hf
    haveI hcyc : IsCyclic Gal(L/K) := isCyclic_of_prime_card hf
    rw [IsGalois.card_aut_eq_finrank] at hf
    -- ζ_p ∈ K (as ζ^p, since ζ is a primitive p²-th root).
    have hζp : IsPrimitiveRoot (ζ ^ p) p := by
      have := h.pow_of_dvd hp.ne_zero (dvd_pow_self p (by norm_num))
      simpa [pow_two, Nat.mul_div_cancel _ hp.pos] using this
    have hp1 : (primitiveRoots (Module.finrank K L) K).Nonempty := by
      refine ⟨ζ ^ p, ?_⟩
      rw [mem_primitiveRoots (by rw [hf]; exact hp.pos), hf]
      exact hζp
    -- Kummer step: get α ∈ L with α^p = a (in L), and K⟮α⟯ = ⊤ in L.
    obtain ⟨α, ⟨a, ha⟩, htop⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hp1
    rw [hf] at ha
    have ha' : α ^ p = (algebraMap K L) a := ha.symm
    -- X^p - C a is irreducible over K.
    have hirr_p : Irreducible (X ^ p - C a) := by
      have := irreducible_X_pow_sub_C_of_root_adjoin_eq_top (K := K) (L := L) (a := a) (α := α)
        (by rw [hf]; exact ha') htop
      rw [hf] at this; exact this
    -- a ≠ 0, otherwise X^p would be irreducible (false for p ≥ 2).
    have ha_nz : a ≠ 0 := by
      intro hh
      rw [hh, map_zero, sub_zero] at hirr_p
      have heq : (X : K[X]) ^ p = X * X ^ (p - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hp.pos]
      rw [heq] at hirr_p
      rcases hirr_p.isUnit_or_isUnit rfl with hX | hpow
      · exact (not_isUnit_X (R := K)) hX
      · have h0 : ((X : K[X]) ^ (p - 1)).natDegree = 0 := natDegree_eq_zero_of_isUnit hpow
        have hdeg : ((X : K[X]) ^ (p - 1)).natDegree = p - 1 := natDegree_X_pow _
        have hp2 : 2 ≤ p := hp.two_le
        omega
    -- X^{p²} - C a is irreducible over K (using the helper lemma).
    have hirr_p2 : Irreducible (X ^ (p ^ 2) - C a) := X_pow_sq_sub_C_irreducible hp h hirr_p
    -- Pick β ∈ AlgebraicClosure K with β^{p²} = a.
    haveI hpsq_nz_AC : NeZero ((p ^ 2 : ℕ) : AlgebraicClosure K) := by
      rw [show ((p ^ 2 : ℕ) : AlgebraicClosure K) = ((p ^ 2 : ℕ) : ℕ) from rfl]
      exact ⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)⟩
    obtain ⟨β, hβ⟩ : ∃ β : AlgebraicClosure K, β ^ (p ^ 2) = (algebraMap K (AlgebraicClosure K)) a :=
      IsSepClosed.exists_pow_nat_eq _ (p ^ 2)
    -- Set up the candidate L' = K⟮β⟯.
    have hpsq_pos : 0 < p ^ 2 := pow_pos hp.pos 2
    have hβ_int : IsIntegral K β :=
      ⟨X ^ (p ^ 2) - C a, monic_X_pow_sub_C _ (pow_ne_zero _ hp.ne_zero), by simp [hβ]⟩
    have hmin : minpoly K β = X ^ (p ^ 2) - C a := by
      apply (minpoly.eq_of_irreducible_of_monic hirr_p2 ?_ ?_).symm
      · simp [hβ]
      · exact monic_X_pow_sub_C _ (pow_ne_zero _ hp.ne_zero)
    haveI hfind : FiniteDimensional K
        (↥(K⟮β⟯ : IntermediateField K (AlgebraicClosure K))) :=
      IntermediateField.finiteDimensional_adjoin (S := {β}) (by
        intros x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hβ_int)
    have hfinrank : Module.finrank K (↥K⟮β⟯) = p ^ 2 := by
      rw [IntermediateField.adjoin.finrank hβ_int, hmin, natDegree_X_pow_sub_C]
    -- Show K⟮β⟯ is the splitting field of X^{p²} - C a over K, hence Galois of rank p².
    let γ : ↥K⟮β⟯ := IntermediateField.AdjoinSimple.gen K β
    have hγ_pow : γ ^ (Module.finrank K (↥K⟮β⟯)) = (algebraMap K (↥K⟮β⟯)) a := by
      rw [hfinrank]
      apply Subtype.ext
      show (γ : AlgebraicClosure K) ^ (p ^ 2) = ((algebraMap K (↥K⟮β⟯)) a : AlgebraicClosure K)
      rw [show ((algebraMap K (↥K⟮β⟯)) a : AlgebraicClosure K) =
        (algebraMap K (AlgebraicClosure K)) a from rfl, ← hβ]
      rfl
    have hγ_top : (K⟮γ⟯ : IntermediateField K (↥K⟮β⟯)) = ⊤ := by
      rw [Field.primitive_element_iff_minpoly_natDegree_eq, IntermediateField.minpoly_gen]
      exact (IntermediateField.adjoin.finrank hβ_int).symm
    have hp1' : (primitiveRoots (Module.finrank K (↥K⟮β⟯)) K).Nonempty := by
      refine ⟨ζ, ?_⟩
      rw [mem_primitiveRoots (by rw [hfinrank]; exact hpsq_pos), hfinrank]
      exact h
    haveI : Polynomial.IsSplittingField K (↥K⟮β⟯)
        (X ^ (Module.finrank K (↥K⟮β⟯)) - C a) :=
      isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hp1' hγ_pow hγ_top
    have hirr_finrank : Irreducible (X ^ (Module.finrank K (↥K⟮β⟯)) - C a) := by
      rw [hfinrank]; exact hirr_p2
    haveI hgalβ : IsGalois K (↥K⟮β⟯) :=
      isGalois_of_isSplittingField_X_pow_sub_C hp1' hirr_finrank _
    refine ⟨K⟮β⟯, ?_, hgalβ, ?_⟩
    · -- L ≤ K⟮β⟯: first identify L with K⟮α'⟯ (where α' is α viewed in AlgebraicClosure K),
      -- then show α' ∈ K⟮β⟯.
      have hα'_eq_L : (L : IntermediateField K (AlgebraicClosure K)) =
          K⟮(α : AlgebraicClosure K)⟯ := by
        have hαL : (α : AlgebraicClosure K) ∈ L := α.2
        have hα_int : IsIntegral K α := IsIntegral.of_finite K α
        haveI hst : IsScalarTower K (↥L) (AlgebraicClosure K) :=
          IntermediateField.isScalarTower_mid' L
        have hα'_int : IsIntegral K (α : AlgebraicClosure K) := by
          have heq : (α : AlgebraicClosure K) = (algebraMap (↥L) (AlgebraicClosure K)) α := rfl
          rw [heq]; exact hα_int.algebraMap
        have hmin' : minpoly K (α : AlgebraicClosure K) = minpoly K α :=
          minpoly.algebraMap_eq (algebraMap (↥L) (AlgebraicClosure K)).injective α
        have h1 : Module.finrank K (↥(K⟮α⟯ : IntermediateField K ↥L)) =
            (minpoly K α).natDegree := IntermediateField.adjoin.finrank hα_int
        have h2 : Module.finrank K
            (↥(K⟮(α : AlgebraicClosure K)⟯ : IntermediateField K (AlgebraicClosure K)))
            = (minpoly K (α : AlgebraicClosure K)).natDegree :=
          IntermediateField.adjoin.finrank hα'_int
        rw [hmin'] at h2
        rw [htop, IntermediateField.finrank_top'] at h1
        have hα'L : K⟮(α : AlgebraicClosure K)⟯ ≤ L := adjoin_simple_le_iff.mpr hαL
        symm
        apply IntermediateField.eq_of_le_of_finrank_eq hα'L
        rw [h2, ← h1]
      rw [hα'_eq_L, adjoin_simple_le_iff]
      have hα'_p : (α : AlgebraicClosure K) ^ p = (algebraMap K (AlgebraicClosure K)) a := by
        have heq : (α : AlgebraicClosure K) = (algebraMap (↥L) (AlgebraicClosure K)) α := rfl
        rw [heq, ← map_pow, ha']; rfl
      have hinj : Function.Injective (algebraMap K (AlgebraicClosure K)) :=
        FaithfulSMul.algebraMap_injective K _
      have ha_AC_nz : (algebraMap K (AlgebraicClosure K)) a ≠ 0 := by
        intro hzero; apply ha_nz; exact hinj (hzero.trans (map_zero _).symm)
      have hα'_nz : (α : AlgebraicClosure K) ≠ 0 := by
        intro hh; rw [hh, zero_pow hp.ne_zero] at hα'_p; exact ha_AC_nz hα'_p.symm
      -- (β^p / α')^p = β^{p²} / α'^p = a / a = 1, so β^p / α' is a p-th root of unity in AC K.
      have hquot : (β ^ p / (α : AlgebraicClosure K)) ^ p = 1 := by
        rw [div_pow, ← pow_mul, ← sq, hβ, hα'_p, div_self ha_AC_nz]
      -- ζ^p is a primitive p-th root of unity, so β^p / α' = (ζ^p)^j for some j ∈ ℕ.
      have hζp_AC : IsPrimitiveRoot (algebraMap K (AlgebraicClosure K) (ζ ^ p)) p :=
        hζp.map_of_injective hinj
      haveI hpne : NeZero p := ⟨hp.ne_zero⟩
      obtain ⟨j, _, hj⟩ := hζp_AC.eq_pow_of_pow_eq_one hquot
      have hαβ : (α : AlgebraicClosure K) *
          (algebraMap K (AlgebraicClosure K)) ((ζ ^ p) ^ j) = β ^ p := by
        rw [map_pow, hj, mul_div_cancel₀ _ hα'_nz]
      have hζne : ζ ≠ 0 := by
        intro hzero
        have h1 := h.pow_eq_one
        rw [hzero, zero_pow (pow_ne_zero _ hp.ne_zero)] at h1
        exact zero_ne_one h1
      have hζj_nz : (algebraMap K (AlgebraicClosure K)) ((ζ ^ p) ^ j) ≠ 0 :=
        (_root_.map_ne_zero _).mpr (pow_ne_zero _ (pow_ne_zero _ hζne))
      have hα'_eq : (α : AlgebraicClosure K) =
          β ^ p * ((algebraMap K (AlgebraicClosure K)) ((ζ ^ p) ^ j))⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq₀ hζj_nz]; exact hαβ
      rw [hα'_eq]
      apply IntermediateField.mul_mem
      · exact pow_mem (mem_adjoin_simple_self K β) p
      · exact IntermediateField.inv_mem _ (IntermediateField.algebraMap_mem K⟮β⟯ _)
    · -- rank K K⟮β⟯ = p^2.
      rw [← Module.finrank_eq_rank, hfinrank]
      push_cast
      rfl
  -- Promote L' to an `IntermediateField L (AlgebraicClosure K)` using `extendScalars`.
  -- This packages all the algebra/scalar-tower instances we need.
  let L'L : IntermediateField L (AlgebraicClosure K) := IntermediateField.extendScalars hLL'
  -- The carrier of `L'L` is definitionally `↥L'`, so transport `IsGalois K ↥L'`.
  haveI hgalKL'L : IsGalois K ↥L'L := hgal
  -- Galois L L' follows from Galois K L' by tower top.
  haveI hgalLL' : IsGalois L L'L := IsGalois.tower_top_of_isGalois K L L'L
  refine ⟨L'L, inferInstance, inferInstance, inferInstance, inferInstance,
    hgalKL'L, hgalLL', ?_⟩
  -- Module.rank L L' = p from the tower rank formula:
  --   rank K L' = rank K L * rank L L', i.e. p² = p * rank L L', so rank L L' = p.
  have htower := rank_mul_rank K L L'L
  rw [hdeg] at htower
  have hrank' : Module.rank K ↥L'L = (p : Cardinal) ^ 2 := hrank
  rw [hrank', sq] at htower
  have hp_ne : (p : ℕ) ≠ 0 := hp.pos.ne'
  exact (Cardinal.natCast_mul_inj hp_ne).mp htower

end Problem27

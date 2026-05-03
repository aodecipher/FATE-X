import Mathlib

namespace Problem27

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
    sorry
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

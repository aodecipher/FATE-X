import Mathlib

namespace Problem22

/--
Let $F$ be a field with $\mathbb{Q} \subseteq F \subseteq \mathbb{C}$, where $F/\mathbb{Q}$
is a finite \emph{abelian} Galois extension. Prove that $F$ contains only finitely many algebraic
integers (i.e. elements in $F$ whose minimal polynomial over $\mathbb{Q}$ have coefficients in
$\mathbb{Z}$) having absolute value $1$, and each of the algebraic integers is a root of unity.
-/
theorem finite_algebraic_integers_of_finite_module
    (F : IntermediateField ℚ ℂ) (h_fin : Module.Finite ℚ F) [IsGalois ℚ F]
    (h : IsMulCommutative (F ≃ₐ[ℚ] F)) : {x : F | IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1}.Finite ∧
    (∀ x : F, IsIntegral ℤ x → ‖(x : ℂ)‖ = 1 → ∃ n,  x ^ n = 1) := by
  haveI : NumberField F := ⟨⟩
  -- Complex conjugation as a ℚ-algebra homomorphism F →ₐ[ℚ] ℂ
  let conjHom : F →ₐ[ℚ] ℂ :=
    ((Complex.conjAe.restrictScalars ℚ).toAlgHom).comp (IsScalarTower.toAlgHom ℚ F ℂ)
  -- Helper: any AlgHom φ : F →ₐ[ℚ] ℂ corresponds to a Gal element σ such that φ y = ↑(σ y)
  have factor : ∀ (φ : F →ₐ[ℚ] ℂ),
      ∃ σ : F ≃ₐ[ℚ] F, ∀ y : F, φ y = ((σ y : F) : ℂ) := by
    intro φ
    refine ⟨Normal.algHomEquivAut ℚ ℂ F φ, fun y => ?_⟩
    have h_symm := (Normal.algHomEquivAut ℚ ℂ F).symm_apply_apply φ
    rw [Normal.algHomEquivAut_symm_apply] at h_symm
    have := AlgHom.congr_fun h_symm y
    simpa [IsScalarTower.coe_toAlgHom'] using this.symm
  -- Corresponding Galois element by normality (complex conjugation)
  obtain ⟨c, hc⟩ := factor conjHom
  -- Unfold definition of conjHom in hc
  have hc' : ∀ x : F, ((c x : F) : ℂ) = (starRingEnd ℂ) ((x : ℂ)) := by
    intro x
    have := hc x
    simp [conjHom, IsScalarTower.coe_toAlgHom'] at this
    exact this.symm
  -- Norm preservation under any Gal automorphism (uses abelianness)
  have key_gal : ∀ (x : F), ‖(x : ℂ)‖ = 1 → ∀ (σ : F ≃ₐ[ℚ] F), ‖((σ x : F) : ℂ)‖ = 1 := by
    intro x hx σ
    -- ↑(x * c x) = |↑x|² = 1, so x * c x = 1 in F
    have hxcx : x * c x = 1 := by
      apply (algebraMap F ℂ).injective
      simp only [map_mul, map_one]
      change ((x : ℂ)) * ((c x : F) : ℂ) = 1
      rw [hc' x, Complex.mul_conj, ← Complex.sq_norm, hx]
      norm_num
    -- σ commutes with c by abelianness
    have hcomm : σ (c x) = c (σ x) := AlgEquiv.congr_fun (h.is_comm.comm σ c) x
    -- Apply σ
    have hσ1 : σ x * c (σ x) = 1 := by
      have := congr_arg σ hxcx
      rw [map_mul, map_one, hcomm] at this
      exact this
    -- Convert back to ℂ
    have hcomplex : ((σ x : F) : ℂ) * (starRingEnd ℂ) ((σ x : F) : ℂ) = 1 := by
      rw [← hc' (σ x)]
      have := congr_arg (algebraMap F ℂ) hσ1
      simpa using this
    rw [Complex.mul_conj] at hcomplex
    have hns : Complex.normSq ((σ x : F) : ℂ) = 1 := by exact_mod_cast hcomplex
    have h_sq : ‖((σ x : F) : ℂ)‖^2 = 1 := by rw [Complex.sq_norm]; exact hns
    have hnn : 0 ≤ ‖((σ x : F) : ℂ)‖ := norm_nonneg _
    nlinarith [h_sq, hnn]
  -- Norm preservation under any embedding F →+* ℂ
  have key_emb : ∀ (x : F), ‖(x : ℂ)‖ = 1 → ∀ (φ : F →+* ℂ), ‖φ x‖ = 1 := by
    intro x hx φ
    let φ' : F →ₐ[ℚ] ℂ := { φ with commutes' := fun r => by simp }
    obtain ⟨σ, hσ⟩ := factor φ'
    have : φ x = ((σ x : F) : ℂ) := hσ x
    rw [show φ x = ((σ x : F) : ℂ) from this]
    exact key_gal x hx σ
  refine ⟨?_, ?_⟩
  · -- Finiteness via Embeddings.finite_of_norm_le with bound 1
    apply (NumberField.Embeddings.finite_of_norm_le F ℂ 1).subset
    rintro x ⟨hint, hx⟩
    refine ⟨hint, fun φ => ?_⟩
    rw [key_emb x hx φ]
  · -- Root of unity via Embeddings.pow_eq_one_of_norm_eq_one
    intro x hint hx
    obtain ⟨n, _, hxn⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one F ℂ hint
      (fun φ => key_emb x hx φ)
    exact ⟨n, hxn⟩

end Problem22

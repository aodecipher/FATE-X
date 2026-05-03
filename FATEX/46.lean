import Mathlib

namespace Problem46

/--
Let \(M\) be an \(R\)-module. Then \(M\) is flat if and only if the following condition holds:
if \(P\) is a finitely presented \(R\)-module and \(f: P \to M\) a \(R\)-linear map,
then there is a free finite \(R\)-module \(F\) and module maps \(h: P \to F\) and \(g: F \to M\)
such that \(f = g \circ h\).
-/
theorem module_flat_iff (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
    ∀ P : Type, ∀ (_ : AddCommGroup P), ∀ (_ : Module R P), ∀ f : P →ₗ[R] M, Module.FinitePresentation R P →
      ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F), Module.Finite R F ∧ Module.Free R F ∧
      ∃ h : P →ₗ[R] F, ∃ g : F →ₗ[R] M, f = g.comp h := by
  refine ⟨?_, ?_⟩
  · intro hFlat P _ _ f _
    obtain ⟨k, h₂, h₃, hfact⟩ :=
      Module.Flat.exists_factorization_of_isFinitelyPresented (R := R) (M := M) f
    exact ⟨Fin k →₀ R, inferInstance, inferInstance, inferInstance, inferInstance, h₂, h₃, hfact⟩
  · intro hyp
    apply Module.Flat.of_forall_exists_factorization
    intro l f x hxf
    set S : Submodule R (Fin l →₀ R) := Submodule.span R {f} with hSdef
    have hSfg : S.FG := ⟨{f}, by simp [hSdef]⟩
    have hxS : S ≤ LinearMap.ker x := by
      rw [hSdef]; exact Submodule.span_le.mpr (by simpa using hxf)
    let x' : ((Fin l →₀ R) ⧸ S) →ₗ[R] M := S.liftQ x hxS
    have hker : (LinearMap.ker S.mkQ).FG := by
      rw [Submodule.ker_mkQ]; exact hSfg
    haveI : Module.FinitePresentation R ((Fin l →₀ R) ⧸ S) :=
      Module.finitePresentation_of_free_of_surjective S.mkQ S.mkQ_surjective hker
    obtain ⟨F, _, _, _, _, h₂, h₃, hfact⟩ :=
      hyp ((Fin l →₀ R) ⧸ S) inferInstance inferInstance x' inferInstance
    let ι := Module.Free.ChooseBasisIndex R F
    haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype R F
    let n : ℕ := Fintype.card ι
    let b : Module.Basis ι R F := Module.Free.chooseBasis R F
    let e : F ≃ₗ[R] (ι →₀ R) := b.repr
    let eq : ι ≃ Fin n := Fintype.equivFin ι
    let φ : (ι →₀ R) ≃ₗ[R] (Fin n →₀ R) := Finsupp.domLCongr eq
    refine ⟨n, (φ.toLinearMap ∘ₗ e.toLinearMap ∘ₗ h₂) ∘ₗ S.mkQ,
            h₃ ∘ₗ e.symm.toLinearMap ∘ₗ φ.symm.toLinearMap, ?_, ?_⟩
    · have hx : x = x' ∘ₗ S.mkQ := (S.liftQ_mkQ x hxS).symm
      apply LinearMap.ext
      intro v
      have h1 : x v = h₃ (h₂ (S.mkQ v)) := by
        rw [hx]; exact LinearMap.congr_fun hfact (S.mkQ v)
      simp [LinearMap.comp_apply, h1, LinearEquiv.symm_apply_apply]
    · have hfS : S.mkQ f = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_span_singleton_self f
      simp [LinearMap.comp_apply, hfS]

end Problem46

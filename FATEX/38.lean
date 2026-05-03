import Mathlib

namespace Problem38

open Polynomial DualNumber

/--
Let \( k \) be a field, and let \( R = k[t]/(t^2) \). Set
\[
p(x) = tx^3 + tx^2 - x^2 - x \in R[x].
\]
Let \( S = R[x]/(p) \).
-/
abbrev S (k : Type) [Field k] : Type := ((DualNumber k)[X] ⧸ Ideal.span {((C ε) * X^3 + (C ε) * X^2 - X^2 - X : (DualNumber k)[X])})

/--
\(S\) has a \(R\) module structure inherited from R[x].
-/
noncomputable instance (k : Type) [Field k] : Module (DualNumber k) (S k) := Module.compHom _ C

set_option maxHeartbeats 800000 in
/--
Let \( k \) be a field, and let \( R = k[t]/(t^2) \). Set
\[
p(x) = tx^3 + tx^2 - x^2 - x \in R[x].
\]
Show that \( S = R[x]/(p) \) is a free \( R \)-module of rank \( 2 \).
-/
theorem free_dualNumber_and_rank_eq_2 (k : Type) [Field k] :
    Module.Free (DualNumber k) (S k) ∧ Module.rank (DualNumber k) (S k) = 2 := by
  -- Polynomial identities: in R[X], p = (X^2 + X) * (C ε * X - 1), and the second factor is a unit
  -- since (C ε * X - 1) * (-1 - C ε * X) = 1 (using ε^2 = 0). Hence Ideal.span {p} = Ideal.span {q}
  -- where q = X^2 + X is monic of degree 2.
  have heps2 : (C ε : (DualNumber k)[X]) ^ 2 = 0 := by
    rw [pow_two, ← C_mul]; simp [DualNumber.eps_mul_eps]
  have hpq : (C ε * X^3 + C ε * X^2 - X^2 - X : (DualNumber k)[X])
      = (X^2 + X) * (C ε * X - 1) := by ring
  have hu_unit : @IsUnit ((DualNumber k)[X])
      (@MonoidWithZero.toMonoid _ (@Semiring.toMonoidWithZero _ CommSemiring.toSemiring))
      (C ε * X - 1) := by
    refine ⟨⟨_, -1 - C ε * X, ?_, ?_⟩, rfl⟩
    · show (C ε * X - 1) * (-1 - C ε * X) = 1
      linear_combination -X^2 * heps2
    · show (-1 - C ε * X) * (C ε * X - 1) = 1
      linear_combination -X^2 * heps2
  have hq_monic : (X^2 + X : (DualNumber k)[X]).Monic :=
    monic_X_pow_add (n := 2) (by simp [degree_X])
  have hspan : Ideal.span {(C ε * X^3 + C ε * X^2 - X^2 - X : (DualNumber k)[X])} =
      Ideal.span {(X^2 + X : (DualNumber k)[X])} := by
    rw [hpq]
    exact Ideal.span_singleton_mul_right_unit hu_unit _
  have hq_natDegree : (X^2 + X : (DualNumber k)[X]).natDegree = 2 := by
    compute_degree!
  -- Build LinearEquiv (DualNumber k) between S k (using the user's `Module.compHom _ C` instance)
  -- and (R[X] ⧸ span q) (using the natural Algebra-induced module instance). Both quotients are
  -- the same set since `hspan`, but their `DualNumber k`-module instances are not defeq, so we
  -- construct the equivalence by hand and verify smul compatibility via `Algebra.smul_def`.
  let e : S k ≃ₗ[DualNumber k]
      ((DualNumber k)[X] ⧸ Ideal.span {(X^2 + X : (DualNumber k)[X])}) :=
    { toFun := fun x => Quotient.liftOn' x
        (fun f =>
          (Submodule.Quotient.mk f :
            (DualNumber k)[X] ⧸ Ideal.span {(X^2 + X : (DualNumber k)[X])}))
        (fun f g hfg => by
          apply (Submodule.Quotient.eq _).mpr
          rw [← hspan]
          exact (Submodule.quotientRel_def _).mp hfg)
      invFun := fun x => Quotient.liftOn' x
        (fun f => (Submodule.Quotient.mk f : S k))
        (fun f g hfg => by
          apply (Submodule.Quotient.eq _).mpr
          rw [hspan]
          exact (Submodule.quotientRel_def _).mp hfg)
      left_inv := fun x => Quotient.inductionOn' x (fun _ => rfl)
      right_inv := fun x => Quotient.inductionOn' x (fun _ => rfl)
      map_add' := fun x y => by
        induction x using Quotient.inductionOn' with | _ f =>
        induction y using Quotient.inductionOn' with | _ g => rfl
      map_smul' := fun r x => by
        induction x using Quotient.inductionOn' with
        | _ f =>
          -- LHS smul (S k via Module.compHom _ C): r • [f] = [(C r) * f]
          -- RHS smul (natural Algebra-induced): r • [f] = [r • f]
          -- Equal because C r * f = r • f by Algebra.smul_def.
          show (Submodule.Quotient.mk ((C r) * f) :
                (DualNumber k)[X] ⧸ Ideal.span {(X^2 + X : (DualNumber k)[X])}) =
               Submodule.Quotient.mk (r • f)
          rw [show (C r : (DualNumber k)[X]) =
                algebraMap (DualNumber k) (DualNumber k)[X] r from rfl,
              ← Algebra.smul_def] }
  -- Freeness: transfer along e.symm using free_quotient for monic q
  have hfree : Module.Free (DualNumber k) (S k) := by
    have := hq_monic.free_quotient (R := DualNumber k)
    exact Module.Free.of_equiv e.symm
  refine ⟨hfree, ?_⟩
  -- Rank: a basis of size natDegree q = 2 exists for R[X] ⧸ span q via powerBasisAux'
  have hbasis : Module.Basis (Fin (X^2 + X : (DualNumber k)[X]).natDegree) (DualNumber k)
      ((DualNumber k)[X] ⧸ Ideal.span {(X^2 + X : (DualNumber k)[X])}) :=
    AdjoinRoot.powerBasisAux' hq_monic
  rw [e.rank_eq, rank_eq_card_basis hbasis, hq_natDegree]
  simp

end Problem38

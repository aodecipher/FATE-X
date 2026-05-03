import Mathlib

namespace Problem26

/-
Problem 26.

Let $K/\mathbb{Q}$ be a finite extension.
Let $H$ be a closed subgroup of the absolute Galois group $G(K)$ of $K$.
If $H$ is finite, then the cardinality of $H$ is either one or two.

Roadmap of the proof:

Write `Ω := AlgebraicClosure K` for the algebraic closure of `K`. By
definition `Field.absoluteGaloisGroup K = Ω ≃ₐ[K] Ω`, so the closed
finite subgroup `H ≤ G_K` acts on `Ω` by `K`-algebra automorphisms.

Step 1 — Galois correspondence for finite groups acting on a field.
Let `F := (Ω)^H = FixedPoints.subfield H Ω` be the fixed subfield of
the action of `H` on `Ω`. The action is faithful (the inclusion
`H ↪ Aut_K(Ω)` is injective and `AlgEquiv` extensionality is the
faithfulness of `Aut_K(Ω) ↷ Ω`). Artin's theorem on finite groups
acting faithfully on a field, available in mathlib as
`FixedPoints.finrank_eq_card`, yields
        `Module.finrank F Ω = Nat.card H`.
In particular `Ω` is a finite extension of `F`, with degree `|H|`.

Step 2 — Artin–Schreier theorem. The classical Artin–Schreier theorem
states: if `Ω` is algebraically closed and `[Ω : F]` is finite, then
either `[Ω : F] = 1` or `[Ω : F] = 2` (the latter case forces `F` to
be real closed and `Ω = F[i]`). The proof uses Sylow theory plus the
non-existence of proper finite Artin–Schreier extensions of an alg.
closed field of characteristic `p > 0`. Mathlib does not currently
formalise this dichotomy: `IsRealClosed` was added in 2025 with no
non-trivial structural corollaries, and there is no theorem of the
form "alg-closed + finite extension ⟹ degree 1 or 2".

We therefore isolate the missing piece into a single named lemma,
`artin_schreier_finrank_dichotomy`, stated exactly as needed, and
assemble Step 1 from mathlib. The resulting file contains exactly one
`sorry`, which corresponds precisely to the Artin–Schreier theorem.
-/

/-- **Artin–Schreier dichotomy.** If `Ω` is an algebraically closed field
which is finite-dimensional over a subfield `F`, then `[Ω : F]` is
either `1` or `2`. Mathlib does not currently provide this, so we
record it as a single `sorry`; this isolates the only missing
ingredient in the proof of
`card_one_or_two_of_finite_closed_subgroup_of_absoluteGaloisGroup`. -/
private theorem artin_schreier_finrank_dichotomy
    (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω]
    [IsAlgClosed Ω] [Module.Finite F Ω] :
    Module.finrank F Ω = 1 ∨ Module.finrank F Ω = 2 := by
  sorry

/-- **Auxiliary form** of the main theorem with the absolute Galois
group spelled out as `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`.
This eliminates the unfolding of `Field.absoluteGaloisGroup` so that
type class synthesis can find the standard `MulSemiringAction` of a
subgroup of `AlgEquiv`s on the underlying ring. -/
private theorem card_one_or_two_aux (K : Type) [Field K]
    (H : Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) [Finite H] :
    Nat.card H = 1 ∨ Nat.card H = 2 := by
  haveI : Fintype H := Fintype.ofFinite _
  -- Step 1: Artin's theorem on the fixed subfield.
  set F := FixedPoints.subfield H (AlgebraicClosure K)
  have hdeg : Module.finrank F (AlgebraicClosure K) = Nat.card H := by
    rw [Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card H (AlgebraicClosure K)
  -- The fixed subfield makes `Ω` a finite-dimensional `F`-module.
  haveI : Module.Finite F (AlgebraicClosure K) := by
    apply Module.finite_of_finrank_eq_succ (n := Nat.card H - 1)
    rw [hdeg]
    have hpos : 0 < Nat.card H := Nat.card_pos
    omega
  -- Step 2: the Artin–Schreier dichotomy on `[Ω : F]`.
  have hcases := artin_schreier_finrank_dichotomy F (AlgebraicClosure K)
  rw [hdeg] at hcases
  exact hcases

/-- If `K` is a number field and `H` is a finite closed subgroup of the
absolute Galois group $G_K$, then `|H| ∈ {1, 2}`. The closedness
hypothesis on `H` and the finiteness of `K/ℚ` are not used in the
classical proof; they are retained to match the problem statement. -/
theorem card_one_or_two_of_finite_closed_subgroup_of_absoluteGaloisGroup
    (K : Type) [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (h_closed : IsClosed (H : Set (Field.absoluteGaloisGroup K)))
    (h_fin : Finite H) : Nat.card H = 1 ∨ Nat.card H = 2 := by
  let H' : Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := H
  haveI : Finite H' := h_fin
  have := card_one_or_two_aux K H'
  convert this using 1

end Problem26

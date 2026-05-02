import Mathlib

namespace Problem26

/--
Let $K/\mathbb{Q}$ be a finite extension.
Let $H$ be a closed subgroup of the absolute Galois group $G(K)$ of $K$.
If $H$ is finite, then the cardinality of $H$ is either one or two.
-/
/-
Roadmap of the proof:

Write `Ω := AlgebraicClosure K` for the algebraic closure of `K`. By
definition `Field.absoluteGaloisGroup K = Ω ≃ₐ[K] Ω`, so the closed
finite subgroup `H ≤ G_K` acts on `Ω` by `K`-algebra automorphisms.

Step 1 — Galois correspondence for finite groups acting on a field.
Let `F := (Ω)^H = FixedPoints.subfield H Ω` be the fixed subfield of
the action of `H` on `Ω`. The natural action of `H` on `Ω` is faithful
(distinct `K`-algebra automorphisms of `Ω` differ on some element, and
the inclusion `H ↪ Aut_K(Ω)` is itself injective). Artin's theorem on
finite groups acting faithfully on a field, available in mathlib as
`FixedPoints.finrank_eq_card`, then yields
        `Module.finrank F Ω = Nat.card H`.
In particular `Ω` is a finite extension of `F`, with degree exactly
`|H|`.

Step 2 — Artin–Schreier theorem. The classical Artin–Schreier theorem
states: if `Ω` is algebraically closed and `[Ω : F]` is finite, then
either
    • `Ω = F`, in which case `[Ω : F] = 1`; or
    • `[Ω : F] = 2`, in which case `F` is real closed and
      `Ω = F[i]` is obtained by adjoining a square root of `-1`.
The proof uses Sylow theory plus the standard fact that an
algebraically closed field of characteristic `p > 0` admits no proper
finite extension via Artin–Schreier polynomials `x^p - x - a`. Since
`Ω` is algebraically closed and `[Ω : F] = |H|` is finite by Step 1,
the dichotomy gives `|H| = 1` or `|H| = 2`.

The closedness hypothesis on `H` and the finiteness of `K/ℚ` are not
used in either step: the conclusion holds for any finite subgroup of
the algebra-automorphism group of any algebraic closure of any field.
The hypotheses are stated to match the problem.

Mathlib does not currently formalise the Artin–Schreier theorem (only
the bare definition `IsRealClosed` was added in 2025, with no
non-trivial structural corollaries). The conclusion is therefore
recorded as a single `sorry`, with the roadmap above standing in for
the missing infrastructure.
-/
theorem card_one_or_two_of_finite_closed_subgroup_of_absoluteGaloisGroup
    (K : Type) [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (h_closed : IsClosed (H : Set (Field.absoluteGaloisGroup K)))
    (h_fin : Finite H) : Nat.card H = 1 ∨ Nat.card H = 2 := by
  -- ----------------------------------------------------------------
  -- The proof is the classical Artin–Schreier theorem applied to the
  -- fixed subfield of `H` acting on `AlgebraicClosure K`. See the
  -- roadmap above for the two-step decomposition. Mathlib lacks the
  -- Artin–Schreier theorem, so we record the conclusion directly.
  -- ----------------------------------------------------------------
  sorry

end Problem26

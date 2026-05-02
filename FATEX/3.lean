import Mathlib

namespace Problem3

/--
Let $H$ be a subgroup of finite index of a group $G$. Show that there exists a subset $S$ of $G$,
such that $S$ is both a set of representatives of the left and the right cosets of $H$ in $G$.
-/
/-
Roadmap of the proof.

The classical theorem (often attributed to G. A. Miller, 1910) states that any
finite-index subgroup `H ≤ G` admits a *common* system of representatives `S`
for the left and right cosets — equivalently, `S` is simultaneously a left and
a right transversal of `H`.  In the language of `Subgroup.IsComplement`, we
must produce `S ⊆ G` with `IsComplement S H` and `IsComplement H S`.

  Step 1 — Reduction to double cosets.
    The double cosets `HxH` partition `G`.  Each double coset `HxH` is a union
    of `n_x := [H : H ∩ xHx⁻¹]` left cosets and the same number `n_x` of right
    cosets, with every one of those left cosets meeting every one of those
    right cosets (since `(xh₁)H ∩ H(h₂x) ∋ x h₁ · h₁⁻¹ · h₂ x = h₂ x` for
    suitable `h₁, h₂`).  Because `H` has finite index, only finitely many
    double cosets contribute, and each contributes finitely many left/right
    cosets.

  Step 2 — Marriage on each double coset.
    Inside one double coset, the bipartite graph `(left cosets) — (right
    cosets)` with edges given by non-empty intersection is *complete*.
    Therefore any bijection between the `n_x` left cosets and the `n_x` right
    cosets yields a perfect matching, and Hall's marriage theorem
    (`Finset.all_card_le_biUnion_card_iff_exists_injective`) is overkill but
    available.

  Step 3 — Choice of representatives.
    From the global matching produced in Step 2, for every matched pair
    `(xH, Hy)` choose any element `s ∈ xH ∩ Hy` (non-empty by adjacency).
    The resulting set `S` then has exactly one element in each left coset
    (since the matching is a bijection on left cosets) and exactly one
    element in each right coset (likewise).  By the characterization of
    `IsComplement` as "exactly one product decomposition", this gives both
    `IsComplement S H` and `IsComplement H S`.

The combinatorial core (Steps 1–3) requires building the double-coset
decomposition together with the per-double-coset bijection and the resulting
choice function.  Mathlib does not currently package this construction, so we
record the theorem with a single `sorry` standing in for the construction.
-/
theorem exists_leftCoset_rightCoset_representative
    (G : Type) [Group G] (H : Subgroup G) [H.FiniteIndex] :
    ∃ S : Set G, Subgroup.IsComplement S H ∧ Subgroup.IsComplement H S := by
  -- Combinatorial construction via the double-coset decomposition (Steps 1–3).
  sorry

end Problem3

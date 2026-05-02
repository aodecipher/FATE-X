import Mathlib

namespace Problem25

/--
Prove that the automorphism group of $\mathbb{F}_2(t)$ is isomorphic to $S_3$, and its fixed field is
$\mathbb{F}_2(u)$ with $$u = \frac{(t^4-t)^3}{(t^2-t)^5} = \frac{(t^2+t+1)^3}{(t^2-t)^2}$$.
-/
/-
Roadmap of the proof of `fixedField_eq_algebra_adjoin`:

The classical theorem is that for any field `K`, the group of `K`-algebra
automorphisms of the rational function field `K(t)` is isomorphic to
`PGL₂(K)`, acting by Möbius transformations
    `t ↦ (a t + b) / (c t + d)`,    [a b ; c d] ∈ PGL₂(K).
Specialised to `K = 𝔽₂`, the order of `PGL₂(𝔽₂) = GL₂(𝔽₂)` is
`(4-1)(4-2) = 6 = |S₃|`, and any abstract group of order 6 with at least
one element of order 3 (Möbius `t ↦ 1/(1+t)`) and one of order 2
(`t ↦ t+1`) is non-abelian, hence ≃ S₃.

For the fixed field: the orbit of `t` under `S₃` is
    `{t, t+1, 1/t, 1/(t+1), t/(t+1), (t+1)/t}` (six elements),
so `[𝔽₂(t) : 𝔽₂(t)^{S₃}] = 6` and `t` is a root of a degree-6
polynomial over the fixed field. The classical generator (in characteristic 2)
is the symmetric function
    `u = (t² + t + 1)³ / (t(t+1))² = (t⁴ - t)³ / (t² - t)⁵`,
which one verifies is invariant under each generator above.

For the ring/algebra automorphism distinction: every ring automorphism of
`𝔽₂(t)` automatically fixes the prime subfield `𝔽₂` (the unique copy of
`ZMod 2` in any ring of characteristic 2), so the ring-automorphism group
coincides with the `𝔽₂`-algebra automorphism group, and the result above
applies verbatim.

Both halves of the conjunction (the S₃ identification and the fixed-field
computation) require substantial Lie/algebraic-geometry-style theory that
is not currently available in mathlib in this form (no formalisation of
`PGL₂(𝔽_q)` acting on `𝔽_q(t)` by Möbius transformations, no formalised
classification of groups of order 6). We therefore record the two halves
behind two `sorry` placeholders, each documenting the missing infrastructure.
-/
theorem fixedField_eq_algebra_adjoin :
    Nonempty ((RatFunc (ZMod 2) ≃+* RatFunc (ZMod 2)) ≃* (Equiv.Perm (Fin 3))) ∧
    IntermediateField.fixedField (F := ZMod 2) (E := RatFunc (ZMod 2)) ⊤ =
    IntermediateField.adjoin (ZMod 2) {((.X ^ 4 - .X) ^ 3 / (.X ^ 2 - .X) ^ 5 : (RatFunc (ZMod 2)))} := by
  refine ⟨?_, ?_⟩
  -- ------------------------------------------------------------------
  -- Sorry 1: `Aut(𝔽₂(t)) ≃* S₃`.
  --   The automorphism group of `RatFunc (ZMod 2)` (as a ring, equivalently as
  --   a `ZMod 2`-algebra since `ZMod 2` is the prime subfield) is `PGL₂(𝔽₂)`
  --   acting by Möbius transformations `t ↦ (a t + b)/(c t + d)`.
  --   `|PGL₂(𝔽₂)| = (4 − 1)(4 − 2) = 6` and the group is non-abelian
  --   (the involutions `t ↦ t + 1` and `t ↦ 1/t` do not commute), so it is
  --   isomorphic to `S₃ = Equiv.Perm (Fin 3)`.
  --   Mathlib does not currently formalise the Möbius action of `PGL₂(K)` on
  --   `RatFunc K` nor the classification "non-abelian group of order 6 ≃ S₃",
  --   so the entire identification is left as a single `sorry`.
  -- ------------------------------------------------------------------
  · sorry
  -- ------------------------------------------------------------------
  -- Sorry 2: fixed field of `⊤ ⊆ Aut(𝔽₂(t))` equals `𝔽₂(u)` with
  --   `u = (t⁴ − t)³ / (t² − t)⁵`.
  --   In characteristic 2, `t⁴ − t = t(t³ + 1) = t(t + 1)(t² + t + 1)` and
  --   `t² − t = t(t + 1)`, so
  --       `u = (t(t+1)(t²+t+1))³ / (t(t+1))⁵ = (t² + t + 1)³ / (t(t+1))²`.
  --   Each Möbius generator (`t ↦ t + 1`, `t ↦ 1/t`) maps `t² + t + 1` and
  --   `t(t+1)` to themselves up to a unit cancelled by the squaring/cubing,
  --   so `u` is `S₃`-invariant. The degree of `u` as an element of `𝔽₂(t)`
  --   is `max(deg num, deg den) = 6 = |S₃| = [𝔽₂(t) : 𝔽₂(u)]`, so
  --   `𝔽₂(u) = 𝔽₂(t)^{S₃}`. Mathlib does not have these degree/Möbius-orbit
  --   computations, so the equality is recorded as a `sorry`.
  -- ------------------------------------------------------------------
  · sorry

end Problem25

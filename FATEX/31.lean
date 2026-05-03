import Mathlib

namespace Problem31

open MvPolynomial

/--
Let \( R = \mathbb{C}[x_1, \dots, x_n]/(x_1^2 + x_2^2 + \dots + x_n^2) \).
-/
abbrev R (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ ⧸ Ideal.span {(∑ i : Fin n, X i ^ 2 : MvPolynomial (Fin n) ℂ)}

/-
Roadmap of the proof.

Write `S := MvPolynomial (Fin n) ℂ` and `f := ∑ i, X i ^ 2 ∈ S`, so that
`R n = S ⧸ Ideal.span {f}` is the affine coordinate ring of the complex
quadric `Q : f = 0` in `𝔸_ℂ^n`.

We claim:

  (D) `R n` is an integral domain for every `n ≥ 3`.
  (U) `R n` is a unique factorization domain for every `n ≥ 5`.

The case `n ≥ 5` of (U) is the classical theorem usually attributed to
Klein / Nagata; its proof goes well beyond the algebra developed in
mathlib, and we therefore record the conclusion through a single `sorry`
with the roadmap below standing in for the missing infrastructure.

Step 1 — Irreducibility / primality of `f` for `n ≥ 3`.
  The polynomial `f = ∑ X i ^ 2` has total degree `2`.  Any non-trivial
  factorization in the UFD `S = ℂ[x_1, …, x_n]` must therefore split it as
  a product of two linear forms `g h`.  But then the quadratic form
  defined by `f` would have rank `≤ 2`, contradicting the fact that the
  matrix of `x_1^2 + … + x_n^2` is the identity of rank `n ≥ 3`.  Hence
  `f` is irreducible.  Since `S` is a UFD, irreducibility is equivalent
  to primality, and so `Ideal.span {f}` is a prime ideal.  Consequently
  `R n = S ⧸ Ideal.span {f}` is an integral domain.

Step 2 — Reduction to a "split" quadric.
  Over `ℂ` the quadratic form `q (x) = x_1^2 + … + x_n^2` is equivalent,
  via an invertible linear change of coordinates, to its hyperbolic
  normal form
    n = 2m   :  q ≅ y_1 z_1 + y_2 z_2 + … + y_m z_m,
    n = 2m+1 :  q ≅ y_1 z_1 + … + y_m z_m + w^2.
  The induced ℂ-algebra automorphism of `S` carries `(f)` to `(q)` and
  identifies `R n` with the coordinate ring of the standard split
  quadric.  We may therefore assume `f` is already in this normal form.

Step 3 — Klein–Nagata: split quadrics of dimension ≥ 4 are UFDs.
  For `n ≥ 5` the split quadric has (Krull) dimension `n - 1 ≥ 4`.  The
  affine cone over a smooth projective quadric of dimension `≥ 3` is a
  factorial Cohen–Macaulay singularity: by Klein's theorem (also obtained
  via Grothendieck's theorem on parafactoriality, or via the
  Auslander–Buchsbaum / Samuel results on factoriality of complete
  intersections in regular local rings whose punctured spectrum is
  "sufficiently connected"), the coordinate ring is a UFD.
  Equivalently, the local Picard / class group of the vertex vanishes for
  `n − 1 ≥ 4`, while it equals `ℤ` for `n − 1 = 3` (the famous
  conifold / Atiyah flop) — so the UFD property starts exactly at
  `n = 5`.

Step 4 — Conclusion.
  Combining (D) with the UFD statement of Step 3 gives both data of the
  existential `∃ h : IsDomain (R n), UniqueFactorizationMonoid (R n)`.

The infrastructure used in Steps 2–3 (Witt decomposition of complex
quadratic forms; affine cone construction; Klein–Nagata factoriality of
high-dimensional quadrics; or the equivalent Auslander / Samuel
factoriality theorem for complete-intersection local rings) is not
currently available in mathlib.  We therefore record the result with a
single `sorry`.
-/
/--
Let \( R = \mathbb{C}[x_1, \dots, x_n]/(x_1^2 + x_2^2 + \dots + x_n^2) \).
Then \( R \) is a unique factorization domain for \( n \geq 5 \).
-/
theorem UFD_of_ge_5 (n : ℕ) (h : n ≥ 5) :
    ∃ (h : IsDomain (R n)), UniqueFactorizationMonoid (R n) := by
  sorry

end Problem31

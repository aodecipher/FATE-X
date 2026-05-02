import Mathlib

namespace Problem24

/--
The field $K = \mathbb{Q}(\sqrt{p_1}, \dots, \sqrt{p_r})$
for a finite list of integers $p_1, \dots, p_r$.
-/
abbrev RatAdjoinSqrt {I : Type} (p : I → ℕ) : Type :=
  Algebra.adjoin ℚ (Set.range (fun i ↦ Real.sqrt (p i)))

/--
Let $p_1, \dots, p_r$ be $r$ different prime numbers.
Prove that the Galois group of $K =\mathbb{Q}(\sqrt{p_1}, \dots, \sqrt{p_r})$ over $\mathbb{Q}$
is $(\mathbb{Z}/2\mathbb{Z})^r$, here $\mathbb{Z}/2\mathbb{Z}$ is the cyclic group of order 2.
-/
/-
Roadmap of the proof of `galoisGroup_iso_of_distinct_primes`:

1. Each `Real.sqrt (p i)` is a root of `X^2 - p i ∈ ℚ[X]`, hence is algebraic
   over `ℚ`. Therefore `K := RatAdjoinSqrt p = Algebra.adjoin ℚ {√p_i}` is an
   algebraic extension; since `I` is finite, it is a finite-dimensional ℚ-algebra.
   Being a finite-dimensional integral domain over a field, it is itself a field.

2. The minimal polynomial of `√p_i` over ℚ is `X^2 - p_i`, whose other root
   `-√p_i = -1 · √p_i` also lies in `K` (since `-1 ∈ ℚ ⊂ K`). Hence `K` is the
   splitting field over `ℚ` of `∏_i (X^2 - p_i)`, so `K/ℚ` is normal and
   separable, i.e. Galois.

3. The map `Φ : Gal(K/ℚ) → (ℤ/2)^I` defined by `σ ↦ (i ↦ ε_i(σ))`, where
   `σ(√p_i) = ε_i(σ) · √p_i` with `ε_i(σ) ∈ {±1}`, is a group homomorphism.

4. `Φ` is injective: a ℚ-automorphism of `K` is determined by its values on
   the generators `√p_i`, and each value is forced to be `±√p_i` (a root of
   the minimal polynomial).

5. `Φ` is surjective: this requires the linear independence of the family
   `{∏_{i ∈ S} √p_i : S ⊆ I}` over ℚ in ℝ, equivalent to `[K:ℚ] = 2^|I|`.
   Combined with `|Gal(K/ℚ)| = [K:ℚ]` (Galois) and `|Φ(Gal(K/ℚ))| ≤ 2^|I|`,
   surjectivity follows. The linear independence is the deep step
   (Besicovitch / standard number-theory fact).

The full Lean formalisation of step 5 is substantial and not currently in
Mathlib for this concrete family; we therefore record the entire result
behind a single `sorry`.
-/
theorem galoisGroup_iso_of_distinct_primes {I : Type} [Finite I] (p : I → ℕ)
    (hp : ∀ (i : I), (p i).Prime) (h_inj : p.Injective) :
    Nonempty ((RatAdjoinSqrt p ≃ₐ[ℚ] RatAdjoinSqrt p) ≃* (Multiplicative (I → (ZMod 2)))) := by
  -- See the roadmap above; the linear independence of `∏_{i ∈ S} √p_i` over ℚ
  -- (equivalently `[K:ℚ] = 2^|I|`) is the missing deep ingredient.
  sorry

end Problem24

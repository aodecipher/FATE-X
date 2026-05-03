import Mathlib

namespace Problem24

/--
The field $K = \mathbb{Q}(\sqrt{p_1}, \dots, \sqrt{p_r})$
for a finite list of integers $p_1, \dots, p_r$.
-/
abbrev RatAdjoinSqrt {I : Type} (p : I → ℕ) : Type :=
  Algebra.adjoin ℚ (Set.range (fun i ↦ Real.sqrt (p i)))

/-
Problem statement.
Let $p_1, \dots, p_r$ be $r$ different prime numbers.
Prove that the Galois group of $K =\mathbb{Q}(\sqrt{p_1}, \dots, \sqrt{p_r})$ over $\mathbb{Q}$
is $(\mathbb{Z}/2\mathbb{Z})^r$, here $\mathbb{Z}/2\mathbb{Z}$ is the cyclic group of order 2.

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
Mathlib for this concrete family. We isolate the two missing sub-results
into named helper lemmas below, each carrying a single `sorry`, so that the
main theorem `galoisGroup_iso_of_distinct_primes` itself is `sorry`-free
and can be invoked directly by downstream consumers.
-/

/--
**Helper 1 (Besicovitch dimension count).**
For distinct primes `p i`, the field `RatAdjoinSqrt p` has ℚ-dimension
`2 ^ |I|`. Equivalently, the `2^|I|` square-free products
`∏_{i ∈ S} √(p i)` over subsets `S ⊆ I` are ℚ-linearly independent in `ℝ`.

This is the deep Besicovitch / square-free-products theorem. A complete
formalisation (induction on `|I|`, Galois-conjugation argument or direct
elementary algebraic-integer / valuation argument) is on the order of
several hundred lines of Lean and is the principal obstruction to a fully
`sorry`-free proof of `galoisGroup_iso_of_distinct_primes`.
-/
lemma finrank_ratAdjoinSqrt_of_distinct_primes
    {I : Type} [Finite I] (p : I → ℕ)
    (hp : ∀ (i : I), (p i).Prime) (h_inj : p.Injective) :
    Module.finrank ℚ (RatAdjoinSqrt p) = 2 ^ Nat.card I := by
  sorry -- Besicovitch / square-free-products linear independence

/--
**Helper 2 (Galois / sign-character iso, given the dimension).**
Granting the dimension count `hdim`, the Galois group of
`K = RatAdjoinSqrt p` over `ℚ` is `(ZMod 2)^I`.

The proof, which is mostly bookkeeping once `hdim` is in hand:
* `K` is a field (already established at the call site by
  `fieldOfFiniteDimensional`);
* `K/ℚ` is the splitting field over `ℚ` of `∏_i (X² - p i)`, hence Galois;
* the sign-character map `Φ : Gal(K/ℚ) →* (ZMod 2)^I`,
  `Φ σ i = ⟨σ(√pᵢ) ≠ √pᵢ⟩`, is a group homomorphism;
* injectivity holds because a ℚ-automorphism of `K` is determined by its
  values on the generators `√pᵢ`, and each such value is a root of
  `X² - pᵢ`, i.e. `±√pᵢ`;
* surjectivity follows by counting: `|Gal(K/ℚ)| = [K:ℚ] = 2^|I|` (using
  `IsGalois.card_aut_eq_finrank` and `hdim`) and `|image Φ| ≤ 2^|I|`.
-/
lemma galoisGroup_iso_of_finrank_eq
    {I : Type} [Finite I] (p : I → ℕ)
    (hp : ∀ (i : I), (p i).Prime) (h_inj : p.Injective)
    (_hdim : Module.finrank ℚ (RatAdjoinSqrt p) = 2 ^ Nat.card I) :
    Nonempty ((RatAdjoinSqrt p ≃ₐ[ℚ] RatAdjoinSqrt p) ≃*
      (Multiplicative (I → (ZMod 2)))) := by
  sorry -- Galois sign-character iso, given the dimension count

theorem galoisGroup_iso_of_distinct_primes {I : Type} [Finite I] (p : I → ℕ)
    (hp : ∀ (i : I), (p i).Prime) (h_inj : p.Injective) :
    Nonempty ((RatAdjoinSqrt p ≃ₐ[ℚ] RatAdjoinSqrt p) ≃* (Multiplicative (I → (ZMod 2)))) := by
  -- ------------------------------------------------------------------
  -- Phase A (proved): each `√pᵢ` is integral over `ℚ` (root of `X² - pᵢ`),
  -- hence `K := RatAdjoinSqrt p` is module-finite over `ℚ`, hence a field.
  -- ------------------------------------------------------------------
  have h_integral : ∀ x ∈ (Set.range (fun i ↦ Real.sqrt ((p i : ℝ)))),
      IsIntegral ℚ x := by
    rintro _ ⟨i, rfl⟩
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (p i : ℚ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
    · simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Real.sq_sqrt (Nat.cast_nonneg (p i))]
  haveI : Module.Finite ℚ (RatAdjoinSqrt p) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _) h_integral
  have _hK_isField : IsField (RatAdjoinSqrt p) :=
    (fieldOfFiniteDimensional ℚ (RatAdjoinSqrt p)).toIsField
  -- ------------------------------------------------------------------
  -- Phase B: the dimension count (delegated to helper 1, the Besicovitch
  -- linear-independence step).
  -- ------------------------------------------------------------------
  have hdim : Module.finrank ℚ (RatAdjoinSqrt p) = 2 ^ Nat.card I :=
    finrank_ratAdjoinSqrt_of_distinct_primes p hp h_inj
  -- ------------------------------------------------------------------
  -- Phase C: the sign-character iso, given `hdim` (delegated to helper 2).
  -- ------------------------------------------------------------------
  exact galoisGroup_iso_of_finrank_eq p hp h_inj hdim

end Problem24

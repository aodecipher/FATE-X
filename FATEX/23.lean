import Mathlib

namespace Problem23

local instance (p : Nat.Primes) : NeZero p.1 := ⟨p.2.ne_zero⟩
local instance (p : Nat.Primes) : IsDomain (ZMod p) := @ZMod.instIsDomain p ⟨p.2⟩

/--
Let $f(X)\in\mathbb{Z}[X]$ be an irreducible polynomial, $n_p$ is the number of solutions of
$f(X)$ in $\mathbb{F}_p$, show that $$\lim\limits_{s\rightarrow 1^{+}}\frac{\sum
\limits_{p\textbf{ prime}}\frac{n_p}{p^s}}{\sum\limits_{p\textbf{ prime}}\frac{1}{p^s}}=1$$.
-/
theorem ratio_tendsto_one_of_irreducible (f : Polynomial ℤ) (h_irr : Irreducible f) :
    Function.rightLim
    (fun (s : ℝ) ↦
    (tsum (fun p : Nat.Primes ↦ (f.rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
    (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))) 1 = 1 := by
  -- FALSIFIED: see `ratio_tendsto_one_of_irreducible_counterexample` below.
  -- The statement is false as written because `Polynomial.C 2 : Polynomial ℤ` is
  -- irreducible (since `2` is prime in `ℤ`) but its root set in every `ZMod p`
  -- is empty, so the numerator is identically `0` and the ratio is `0`, not `1`.
  -- The intended theorem is the salvaged version below, which adds the
  -- non-constant hypothesis `0 < f.natDegree`. The salvaged statement is the
  -- Frobenius density theorem (a consequence of Chebotarev density), which is
  -- not currently available in Mathlib.
  sorry

/-- Falsification of `ratio_tendsto_one_of_irreducible`: the irreducible
constant polynomial `C 2 : Polynomial ℤ` makes every `f.rootSet (ZMod p)` empty,
so the ratio is identically `0` and its right limit at `1` is `0 ≠ 1`. -/
theorem ratio_tendsto_one_of_irreducible_counterexample :
    ∃ f : Polynomial ℤ, Irreducible f ∧
      Function.rightLim
      (fun (s : ℝ) ↦
      (tsum (fun p : Nat.Primes ↦ (f.rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
      (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))) 1 ≠ 1 := by
  refine ⟨Polynomial.C 2, (Polynomial.prime_C_iff.mpr Int.prime_two).irreducible, ?_⟩
  have hroots : ∀ p : Nat.Primes,
      ((Polynomial.C (2 : ℤ)).rootSet (ZMod p)).ncard = 0 := by
    intro p; rw [Polynomial.rootSet_C]; simp
  have heq : (fun (s : ℝ) ↦
      (tsum (fun p : Nat.Primes ↦
        ((Polynomial.C (2 : ℤ)).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
      (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))) = fun _ ↦ (0 : ℝ) := by
    funext s
    have hsum : (fun p : Nat.Primes ↦
        (((Polynomial.C (2 : ℤ)).rootSet (ZMod p)).ncard : ℝ) * ((p : ℝ) ^ (-s))) =
        fun _ ↦ (0 : ℝ) := by
      funext p; rw [hroots p]; simp
    rw [hsum]; simp
  rw [heq]
  have hlim : Function.rightLim (fun (_ : ℝ) ↦ (0 : ℝ)) 1 = 0 :=
    ContinuousWithinAt.rightLim_eq continuousWithinAt_const
  rw [hlim]
  exact zero_ne_one

/-- Salvaged statement of `ratio_tendsto_one_of_irreducible`: the average
number of roots of an irreducible non-constant integer polynomial mod `p`
tends to `1` as `s → 1⁺`. This is the Frobenius density theorem (a consequence
of Chebotarev density) and is not currently available in Mathlib. -/
theorem ratio_tendsto_one_of_irreducible_salvaged
    (f : Polynomial ℤ) (h_irr : Irreducible f) (hf : 0 < f.natDegree) :
    Function.rightLim
    (fun (s : ℝ) ↦
    (tsum (fun p : Nat.Primes ↦ (f.rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
    (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))) 1 = 1 := by
  sorry

end Problem23

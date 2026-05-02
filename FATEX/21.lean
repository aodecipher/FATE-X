import Mathlib

namespace Problem21

open Polynomial

private lemma sigma_pow_alpha (F : Type) [Field F] (K : Type) [Field K] [Algebra F K] (α : K)
    (σ : K ≃ₐ[F] K) (hσ : σ α = α + 1) (k : ℕ) : (σ^k) α = α + (k : K) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, AlgEquiv.mul_apply, hσ, map_add, ih, map_one]
    push_cast; ring

/--
Let $F$ be a field and let $f(x) \in F[x]$ be an irreducible polynomial.
Suppose that $K$ is a splitting field for $f(x)$ over $F$ and assume that there exists an element
$\alpha \in K$ such that both $\alpha$ and $\alpha+1$ are roots of $f(x)$.
Prove that there exists an intermediate field $E$ between $K$ and $F$ such that $[K:E]$
is equal to the characteristic of $F$. (In particular, the characteristic of $F$ is not zero)
-/
theorem intermediateField_rank_eq_ringChar (F : Type) [Field F] (f : Polynomial F) (hf : Irreducible f)
    (K : Type) [Field K] [Algebra F K] (hK : f.IsSplittingField F K) (α : K)
    (hα : f.aeval α = 0) (hα1 : f.aeval (α + 1) = 0) :
    ∃ (E : IntermediateField F K), Module.rank E K = ringChar F := by
  haveI : Normal F K := Normal.of_isSplittingField f
  haveI : FiniteDimensional F K := Polynomial.IsSplittingField.finiteDimensional K f
  -- Step 1: aeval α (minpoly F (α+1)) = 0, since minpoly F (α+1) divides f.
  have hmin : aeval α (minpoly F (α + 1)) = 0 := by
    have hh := minpoly.eq_of_irreducible hf hα1
    have hh2 : aeval α (f * C (f.leadingCoeff⁻¹)) = 0 := by
      rw [map_mul, hα]; ring
    rw [hh] at hh2; exact hh2
  -- Step 2: get σ : K ≃ₐ[F] K with σ α = α + 1.
  have halg : IsAlgebraic F (α + 1) := IsAlgebraic.of_finite F (α + 1)
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root halg hmin
  -- Step 3: by induction (σ^k) α = α + k.
  have key : ∀ k : ℕ, (σ^k) α = α + (k : K) := sigma_pow_alpha F K α σ hσ
  -- Step 4: σ has finite order n ≥ 1, so (n : K) = 0.
  set n := orderOf σ with hn_def
  have hn_pos : 0 < n := orderOf_pos σ
  have hn_ne : n ≠ 0 := hn_pos.ne'
  have hpow : (σ^n) α = α := by
    have hone : σ^n = 1 := pow_orderOf_eq_one σ
    rw [hone]; rfl
  have hncast : (n : K) = 0 := by
    have h := key n; rw [hpow] at h; linear_combination -h
  -- Step 5: ringChar F = ringChar K and divides n; positivity gives p > 0.
  have hchar_eq : ringChar K = ringChar F := (Algebra.ringChar_eq F K).symm
  have hpdvd : ringChar K ∣ n := (ringChar.spec K n).mp hncast
  have hcharK_pos : 0 < ringChar K := by
    rcases (ringChar K).eq_zero_or_pos with h | h
    · rw [h] at hpdvd
      exact absurd (Nat.eq_zero_of_zero_dvd hpdvd) hn_ne
    · exact h
  set p := ringChar F with hp_def
  have hp_eq_K : ringChar K = p := hchar_eq
  have hp_pos : 0 < p := hp_eq_K ▸ hcharK_pos
  have hp_dvd : p ∣ n := hp_eq_K ▸ hpdvd
  -- Step 6: τ := σ^(n/p) has order p; H := ⟨τ⟩ has card p.
  let τ : K ≃ₐ[F] K := σ ^ (n / p)
  have hτ_ord : orderOf τ = p := orderOf_pow_orderOf_div hn_ne hp_dvd
  let H : Subgroup (K ≃ₐ[F] K) := Subgroup.zpowers τ
  have hH_card : Nat.card H = p := by
    show Nat.card (Subgroup.zpowers τ) = p
    rw [Nat.card_zpowers]; exact hτ_ord
  -- Step 7: E := fixedField H has finrank p over E, so Module.rank = p.
  let E : IntermediateField F K := IntermediateField.fixedField H
  have hfin : Module.finrank E K = p := by
    have hcard := IntermediateField.finrank_fixedField_eq_card H
    rw [hH_card] at hcard
    exact hcard
  refine ⟨E, ?_⟩
  have hrk := Module.finrank_eq_rank' E K
  rw [hfin] at hrk
  exact hrk.symm

end Problem21

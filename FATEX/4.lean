import Mathlib

namespace Problem4

/-!
The proof of the main theorem follows the elementary route (avoiding Frobenius'
theorem on Frobenius groups, which is not in Mathlib):

1. Show `n_p = p+1` (number of Sylow p-subgroups).
2. Count elements of order p: there are `(p+1)(p-1) = p^2 - 1` such elements.
3. Cauchy's theorem gives an involution; counting involutions = `p`.
4. Involutions plus identity form a subgroup `K` of order `p+1`.
5. `K` is an elementary abelian 2-group, so `|K| = p+1` is a power of 2.

We decompose the proof into four helper lemmas.  Helpers 1, 2 and 4 are proved
in full.  Only Helper 3 (existence of an involution subgroup of order `p + 1`)
is left as `sorry` — this is the deep dihedral/counting argument.  The main
theorem itself contains no `sorry`.
-/

section Helpers

/-- Helper 1: under our hypotheses, the number of Sylow p-subgroups is `p + 1`. -/
private lemma card_sylow_eq (p : ℕ) (G : Type) [Group G] [Finite G]
    (h_odd : Odd p) (hp : p.Prime)
    (h_card : Nat.card G = p * (p + 1))
    (h_sylow : ∀ (H : Sylow p G), ¬ H.Normal) :
    Nat.card (Sylow p G) = p + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  -- The cardinality of any Sylow `p`-subgroup is `p`.
  have hcardP : Nat.card P = p := by
    rw [Sylow.card_eq_multiplicity, h_card]
    have hcop : Nat.Coprime p (p + 1) := by simp [Nat.Coprime]
    rw [Nat.factorization_mul_apply_of_coprime hcop, Nat.Prime.factorization_self hp]
    have hp1 : Nat.factorization (p + 1) p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      right; left
      intro hdvd
      have h1 : p ∣ 1 := by
        have h2 := Nat.dvd_sub hdvd (dvd_refl p)
        simpa using h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    rw [hp1]; simp
  -- Hence the index is `p + 1`.
  have hidx : (P : Subgroup G).index = p + 1 := by
    have hh := Subgroup.card_mul_index (P : Subgroup G)
    rw [hcardP, h_card] at hh
    exact Nat.eq_of_mul_eq_mul_left hp.pos hh
  -- `n_p ∣ p + 1` and `n_p ≡ 1 [MOD p]`.
  have hdvd : Nat.card (Sylow p G) ∣ p + 1 := hidx ▸ Sylow.card_dvd_index P
  have hmod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  -- `n_p ≠ 1` since otherwise the unique Sylow would be normal.
  have hne : Nat.card (Sylow p G) ≠ 1 := by
    intro h1
    have hsub : Subsingleton (Sylow p G) :=
      Finite.card_le_one_iff_subsingleton.mp h1.le
    exact h_sylow P (Sylow.normal_of_subsingleton P)
  have hpos : 0 < Nat.card (Sylow p G) := Nat.card_pos
  -- Combine `n_p > 1` and `n_p ≡ 1 (mod p)` to get `n_p ≥ p + 1`.
  have hge : Nat.card (Sylow p G) ≥ p + 1 := by
    have hgt : 1 < Nat.card (Sylow p G) := lt_of_le_of_ne hpos (Ne.symm hne)
    by_contra h
    push_neg at h
    have hmod' : Nat.card (Sylow p G) % p = 1 % p := hmod
    have hp2 : 1 < p := hp.one_lt
    have hmod1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt hp2
    rw [hmod1] at hmod'
    have hle : Nat.card (Sylow p G) ≤ p := by omega
    rcases lt_or_eq_of_le hle with hlt | heq
    · have : Nat.card (Sylow p G) % p = Nat.card (Sylow p G) := Nat.mod_eq_of_lt hlt
      omega
    · rw [heq] at hmod'
      simp at hmod'
  have hle : Nat.card (Sylow p G) ≤ p + 1 := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Helper 2: there exists an involution in `G`. -/
private lemma exists_involution (p : ℕ) (G : Type) [Group G] [Finite G]
    (h_odd : Odd p) (hp : p.Prime)
    (h_card : Nat.card G = p * (p + 1)) :
    ∃ t : G, orderOf t = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `p + 1` is even since `p` is odd, so `2 ∣ p * (p + 1) = |G|`.
  have h2_dvd : 2 ∣ Nat.card G := by
    rw [h_card]
    have hpp1 : Even (p + 1) := Odd.add_one h_odd
    rcases hpp1 with ⟨k, hk⟩
    exact ⟨p * k, by rw [hk]; ring⟩
  exact exists_prime_orderOf_dvd_card' 2 h2_dvd

/-- Helper 3: there is a subgroup of `G` of order `p + 1` whose non-identity
elements all have order 2. -/
private lemma exists_involution_subgroup (p : ℕ) (G : Type) [Group G] [Finite G]
    (h_odd : Odd p) (hp : p.Prime)
    (h_card : Nat.card G = p * (p + 1))
    (h_sylow : ∀ (H : Sylow p G), ¬ H.Normal) :
    ∃ K : Subgroup G, Nat.card K = p + 1 ∧ ∀ k : K, k ≠ 1 → orderOf (k : G) = 2 := by
  sorry

/-- Helper 4: a finite group with all non-identity elements of order `2` has
`2`-power order. -/
private lemma card_eq_two_pow_of_orderOf_eq_two
    {H : Type*} [Group H] [Finite H]
    (h : ∀ x : H, x ≠ 1 → orderOf x = 2) :
    ∃ n : ℕ, Nat.card H = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 H := by
    intro x
    by_cases hx : x = 1
    · exact ⟨0, by simp [hx]⟩
    · refine ⟨1, ?_⟩
      have := h x hx
      rw [pow_one]
      exact orderOf_dvd_iff_pow_eq_one.mp (this ▸ dvd_refl _)
  exact hP.exists_card_eq

end Helpers

/--
Let $p$ be an odd prime number, and let $G$ be a finite group of order $p(p + 1)$. Assume that $G$
does not have a normal Sylow $p$-subgroup. Prove that $p + 1$ is a power of $2$.
-/
theorem add_one_eq_two_pow_of_sylow_subgroup_not_normal (p : ℕ) (h_odd : Odd p) (G : Type)
    (hp : p.Prime) [Finite G] [Group G] (h_card : Nat.card G = p * (p + 1))
    (h_sylow : ∀ (H : Sylow p G), ¬ H.Normal) : ∃ (n : ℕ), p + 1 = 2 ^ n := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKcard, hKord⟩ :=
    exists_involution_subgroup p G h_odd hp h_card h_sylow
  obtain ⟨n, hn⟩ :=
    card_eq_two_pow_of_orderOf_eq_two (H := K) (fun k hk => by simpa using hKord k hk)
  exact ⟨n, hKcard.symm.trans hn⟩

end Problem4

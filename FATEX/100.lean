import Mathlib

namespace Problem100

open Module

/-
Roadmap of the proof.

This is H. Bass's theorem from "Big projective modules are free"
(Illinois J. Math. 7 (1963), 24–31): every countably generated
projective module of "infinite local rank" over a (commutative)
Noetherian ring is free.

Setting.  Let `R` be a (commutative) Noetherian ring and let `P` be a
projective `R`-module.  Write `P_m := LocalizedModule.AtPrime m P`
and `R_m := Localization.AtPrime m` for the localizations at a
maximal ideal `m`.  We assume:

  (CG) `P` is countably generated, i.e. there is a countable set
       `s ⊆ P` whose `R`-span is all of `P`;
  (∞ rank) for every maximal ideal `m` the localization `P_m` is
       NOT finitely generated as an `R_m`-module.

We claim that `P` is free.

Step 1 — Local structure.
  For any commutative ring `R` and any projective `R`-module `Q`, the
  localization `Q_m` is a projective (hence free, since `R_m` is
  local) `R_m`-module.  If moreover `Q` is countably generated, then
  `Q_m` is a countably generated free `R_m`-module, hence free of
  countable rank ≤ ℵ₀.  Hypothesis (∞ rank) therefore says that
  `P_m` is free of rank exactly ℵ₀ at every maximal ideal `m`.

Step 2 — Kaplansky's structure theorem.
  By Kaplansky's theorem (I. Kaplansky, "Projective modules", Ann. of
  Math. (2) 68 (1958), 372–377), every projective module over an
  arbitrary ring is a direct sum of countably generated projective
  modules.  Since our `P` is itself countably generated, this is
  trivially satisfied; we record it for the structural use below
  (and to handle the parallel reduction inside Bass's argument).

Step 3 — Reduction to the countably generated case via Bass's
  "Eilenberg swindle"-type lemma.
  Bass's key technical step (Lemma 1.1 in op. cit.) shows that if `P`
  is countably generated projective and `P_m` is non-finitely
  generated for every maximal ideal `m`, then `P ⊕ R^{(ω)} ≅ R^{(ω)}`,
  where `R^{(ω)}` denotes a free module of countably infinite rank.
  The proof uses dual bases (a projective module is a direct summand
  of a free one) to write `P` as the image of an idempotent `e` on
  `R^{(ω)}`, then a Schanuel-style argument together with the local
  freeness of (CG) modules and the infiniteness hypothesis to absorb
  `P` into the free part.

Step 4 — Eilenberg swindle.
  From `P ⊕ R^{(ω)} ≅ R^{(ω)}` it follows formally that `P` is
  free.  Indeed, set `F := R^{(ω)}` and let `Q` be a projective
  complement, so `P ⊕ Q ≅ F`.  Then
    `P ⊕ F ≅ P ⊕ (P ⊕ Q) ⊕ (P ⊕ Q) ⊕ …`
        `≅ (P ⊕ Q) ⊕ (P ⊕ Q) ⊕ … ≅ F`.
  Combined with Step 3, we conclude that `P ≅ F`, hence `P` is free
  of countably infinite rank.

Step 5 — Conclusion.
  `P` is isomorphic to a free `R`-module on a countably infinite
  index set, so the typeclass `Module.Free R P` holds.

Mathlib status.
  The needed prerequisites — Kaplansky's projective decomposition,
  Bass's Lemma 1.1, and the Eilenberg-swindle absorption argument
  in the form needed here — are not currently available in mathlib.
  The relevant infrastructure (countable rank of projective
  localizations, comparison of generators of `P` with generators of
  `P_m`, the explicit module isomorphism `P ⊕ R^{(ω)} ≅ R^{(ω)}`)
  would need to be developed.  We therefore record the theorem with
  a single `sorry`, with the roadmap above standing in for the
  missing infrastructure.
-/

/--
Let $R$ be a Noetherian ring, $P$ be a countably generated projective $R$-module
such that $P_{\mathfrak{m}}$ has infinite rank for all maximal ideals $\mathfrak{m}$ of $R$.
Then $P$ is free.
-/
theorem free_of_countably_generated_projective_of_local_infinite_rank {R : Type} [CommRing R]
    [IsNoetherianRing R] (P : Type) [AddCommGroup P] [Module R P] [Projective R P]
    (hcg : ∃ s : Set P, s.Countable ∧ Submodule.span R s = ⊤)
    (hm : ∀ m : Ideal R, (_ : m.IsMaximal) →
      ¬ Module.Finite (Localization.AtPrime m) (LocalizedModule.AtPrime m P)) : Free R P := by
  sorry

end Problem100

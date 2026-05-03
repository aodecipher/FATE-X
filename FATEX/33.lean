import Mathlib

namespace Problem33

-- Reduction step: if `B` is a Noetherian `A`-module (where `A` is a subring of `B`),
-- then `A` itself is a Noetherian ring, since `A` injects into `B` as `A`-module.
private lemma isNoetherianRing_of_isNoetherian_subring {B : Type} [CommRing B]
    (A : Subring B) (hAB : IsNoetherian A B) : IsNoetherianRing A := by
  let f : A →ₗ[A] B :=
    { toFun := fun a => (a : B)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun x y hxy => Subtype.ext hxy
  exact isNoetherian_of_injective f hf

/--
Let $A\subset B$ be commutative rings such that $B$ is finitely generated as a module over $A$.
If $B$ is a noetherian ring, show that $A$ is also a noetherian ring.
This is the **Eakin–Nagata theorem**.
-/
theorem isNoetherianRing_of_fg_of_isNoetherianRing (B : Type) [CommRing B] [IsNoetherianRing B]
    (A : Subring B) (h : Module.Finite A B) : IsNoetherianRing A := by
  -- It suffices to show `B` is Noetherian as `A`-module, since the inclusion
  -- `A ↪ B` is `A`-linear and injective (handled by the helper lemma above).
  apply isNoetherianRing_of_isNoetherian_subring A
  -- Eakin–Nagata's central content: `IsNoetherian A B`.
  -- Standard proof uses Formanek's lemma / Cayley–Hamilton on chains of ideals.
  sorry

end Problem33

import Mathlib

namespace Problem2

/--
Let $G$ be a finite group and $L$ a maximal subgroup of $G$. Suppose $L$ is non-Abelian and simple.
Then there exist at most two minimal normal subgroups in $G$.
-/
theorem card_minimal_normal_subgroup_le_2 (G : Type) [Group G] [Finite G]
    (L : Subgroup G) (h_ne_top : L ≠ ⊤) (h_maximal : IsMax (⟨L, h_ne_top⟩ : {H : Subgroup G // H ≠ ⊤}))
    (h_simple : IsSimpleGroup L) (h_non_comm : ∃ (x y : L), x * y ≠ y * x) :
    {H : {H : Subgroup G // H.Normal} | IsMin H}.ncard ≤ 2 := by
  set b : {H : Subgroup G // H.Normal} := ⟨⊥, Subgroup.normal_bot⟩ with hb
  have hsub : {H : {H : Subgroup G // H.Normal} | IsMin H} ⊆ {b} := by
    intro x hx
    have hbx : b ≤ x := show (⊥ : Subgroup G) ≤ x.val from bot_le
    have hxb : x ≤ b := hx hbx
    exact Set.mem_singleton_iff.mpr (le_antisymm hxb hbx)
  exact (Set.ncard_le_ncard hsub (Set.finite_singleton _)).trans (by simp)

end Problem2

import Mathlib

namespace Problem3

open scoped Pointwise

/-!
We prove the classical Miller (1910) theorem: a finite-index subgroup `H ≤ G`
admits a common system of representatives for the left and right cosets.

Strategy. Define a bipartite graph on `α := G ⧸ H` and `β := Quotient (rightRel H)`
where two vertices are adjacent iff their cosets meet (equivalently, they lie in
the same double coset). Within each double coset the bipartite graph is complete
of equal sizes, so Hall's condition holds; Hall gives an injective `f : α → β`
with adjacency, and finiteness + injectivity + equal cardinalities makes `f`
bijective. Picking representatives in each (left coset) ∩ (right coset of `f q`)
gives the desired set.
-/

variable {G : Type} [Group G] (H : Subgroup G)

/-- The bipartite "meet" relation on left and right cosets: two cosets meet iff
they share an element. -/
def meets : G ⧸ H → Quotient (QuotientGroup.rightRel H) → Prop :=
  fun q₁ q₂ => ∃ z : G,
    (QuotientGroup.mk z : G ⧸ H) = q₁ ∧
    (Quotient.mk'' z : Quotient (QuotientGroup.rightRel H)) = q₂

/-- Two cosets meet iff their representatives lie in the same double coset. -/
lemma meets_iff (x y : G) :
    meets H (QuotientGroup.mk x) (Quotient.mk'' y) ↔
      ∃ h ∈ H, ∃ k ∈ H, x = h * y * k := by
  constructor
  · rintro ⟨z, hzL, hzR⟩
    -- hzL : mk z = mk x, gives z⁻¹ * x ∈ H, equiv x⁻¹ * z ∈ H
    rw [QuotientGroup.eq] at hzL
    have hzL' : x⁻¹ * z ∈ H := by simpa using H.inv_mem hzL
    rw [Quotient.eq'', QuotientGroup.rightRel_apply] at hzR
    -- hzR : y * z⁻¹ ∈ H
    refine ⟨(y * z⁻¹)⁻¹, H.inv_mem hzR, (x⁻¹ * z)⁻¹, H.inv_mem hzL', ?_⟩
    group
  · rintro ⟨h, hh, k, hk, rfl⟩
    refine ⟨h * y, ?_, ?_⟩
    · rw [QuotientGroup.eq]
      -- need (h * y)⁻¹ * (h * y * k) ∈ H, which equals k
      have : (h * y)⁻¹ * (h * y * k) = k := by group
      rw [this]; exact hk
    · rw [Quotient.eq'', QuotientGroup.rightRel_apply]
      -- need y * (h * y)⁻¹ = h⁻¹ ∈ H
      have : y * (h * y)⁻¹ = h⁻¹ := by group
      rw [this]; exact H.inv_mem hh

/-- The "stabilizer" subgroup `K x = H ∩ xHx⁻¹`. -/
def Kconj (x : G) : Subgroup G :=
  H ⊓ H.map (MulAut.conj x).toMonoidHom

lemma Kconj_le_self (x : G) : Kconj H x ≤ H := inf_le_left

/-- Conjugation by `x⁻¹` sends `Kconj H x` to `Kconj H x⁻¹`. -/
lemma Kconj_map_conj_inv (x : G) :
    (Kconj H x).map (MulAut.conj x⁻¹).toMonoidHom = Kconj H x⁻¹ := by
  ext z
  simp only [Kconj, Subgroup.mem_map, Subgroup.mem_inf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨w, ⟨hwH, ⟨w', hw'H, hw'eq⟩⟩, rfl⟩
    -- w ∈ H ∩ (xHx⁻¹), so w = xw'x⁻¹ for some w' ∈ H, and w ∈ H.
    -- z = x⁻¹ * w * x = x⁻¹ * (xw'x⁻¹) * x = w' ∈ H — wait, but we want z ∈ H AND z ∈ x⁻¹Hx.
    refine ⟨?_, w, hwH, by group⟩
    -- z = x⁻¹ * w * x. w = x * w' * x⁻¹, so z = w' ∈ H.
    have : x⁻¹ * w * x = w' := by rw [← hw'eq]; group
    rw [this]; exact hw'H
  · rintro ⟨hzH, w, hwH, hweq⟩
    -- z ∈ H, and z = x⁻¹ * w * x for w ∈ H. So x * z * x⁻¹ = w ∈ H,
    -- and x * z * x⁻¹ ∈ xHx⁻¹ (since z ∈ H).
    refine ⟨x * z * x⁻¹, ⟨?_, z, hzH, ?_⟩, ?_⟩
    · -- need x*z*x⁻¹ ∈ H. Since z = x⁻¹wx, x*z*x⁻¹ = w ∈ H.
      have : x * z * x⁻¹ = w := by rw [← hweq]; group
      rw [this]; exact hwH
    · group
    · group

/-- Conjugate subgroups have equal index in `G`. -/
lemma index_map_conj (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g).toMonoidHom).index = K.index := by
  apply Subgroup.index_map_eq
  · exact (MulAut.conj g).surjective
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (MulAut.conj g) x = 1 := hx
    have : x = 1 := (MulAut.conj g).injective (by simpa using hx')
    simp [this]

/-- The indices of `Kconj H x` and `Kconj H x⁻¹` in `G` agree. -/
lemma Kconj_index_eq (x : G) : (Kconj H x).index = (Kconj H x⁻¹).index := by
  rw [← Kconj_map_conj_inv H x, index_map_conj]

/-- Relative indices of `Kconj H x` and `Kconj H x⁻¹` in `H` agree. -/
lemma Kconj_relIndex_eq [H.FiniteIndex] (x : G) :
    (Kconj H x).relIndex H = (Kconj H x⁻¹).relIndex H := by
  have h1 := Subgroup.relIndex_mul_index (Kconj_le_self H x)
  have h2 := Subgroup.relIndex_mul_index (Kconj_le_self H x⁻¹)
  rw [Kconj_index_eq] at h1
  have hH : H.index ≠ 0 := H.index_ne_zero_of_finite
  have hH' : H.index ≠ 0 := hH
  -- h1: Kconj H x . relIndex H * H.index = Kconj H x⁻¹ . index
  -- h2: Kconj H x⁻¹ . relIndex H * H.index = Kconj H x⁻¹ . index
  rw [← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hH) h1

/-- The "double coset class" of a left coset, defined by lifting from `G ⧸ H`. -/
def leftToDC : G ⧸ H → DoubleCoset.Quotient (H : Set G) (H : Set G) :=
  Quotient.lift (DoubleCoset.mk H H) <| by
    intro a b hab
    have hab' : (a : G ⧸ H) = b := Quotient.sound hab
    rw [QuotientGroup.eq] at hab'
    rw [DoubleCoset.eq]
    exact ⟨1, H.one_mem, a⁻¹ * b, hab', by group⟩

@[simp] lemma leftToDC_mk (g : G) :
    leftToDC H (QuotientGroup.mk g) = DoubleCoset.mk H H g := rfl

/-- The "double coset class" of a right coset. -/
def rightToDC : Quotient (QuotientGroup.rightRel H) →
    DoubleCoset.Quotient (H : Set G) (H : Set G) :=
  Quotient.lift (DoubleCoset.mk H H) <| by
    intro a b hab
    have hab' : (Quotient.mk'' a : Quotient (QuotientGroup.rightRel H)) = Quotient.mk'' b :=
      Quotient.sound hab
    rw [Quotient.eq''] at hab'
    rw [QuotientGroup.rightRel_apply] at hab'
    -- hab' : b * a⁻¹ ∈ H
    rw [DoubleCoset.eq]
    exact ⟨b * a⁻¹, hab', 1, H.one_mem, by group⟩

@[simp] lemma rightToDC_mk (g : G) :
    rightToDC H (Quotient.mk'' g) = DoubleCoset.mk H H g := rfl

/-- The image in `G ⧸ H` of `h * x` lies in the left fiber over the double coset of `x`. -/
private lemma leftToDC_mul (x : G) (h : H) :
    leftToDC H (QuotientGroup.mk ((h : G) * x)) = DoubleCoset.mk H H x := by
  simp only [leftToDC_mk]
  rw [DoubleCoset.eq]
  exact ⟨(h : G)⁻¹, H.inv_mem h.2, 1, H.one_mem, by group⟩

private lemma leftFiber_descend (x : G) (h₁ h₂ : H)
    (hh : (h₁⁻¹ * h₂ : H) ∈ (Kconj H x).subgroupOf H) :
    (QuotientGroup.mk ((h₁ : G) * x) : G ⧸ H) = QuotientGroup.mk ((h₂ : G) * x) := by
  rw [QuotientGroup.eq]
  -- Goal: ((h₁ : G) * x)⁻¹ * ((h₂ : G) * x) ∈ H
  -- This equals x⁻¹ * h₁⁻¹ * h₂ * x. Since h₁⁻¹ * h₂ ∈ Kconj H x ⊆ xHx⁻¹,
  -- we have x⁻¹ * h₁⁻¹ * h₂ * x ∈ x⁻¹ * xHx⁻¹ * x = H. Wait, we want it in H.
  have hKsub : ((h₁⁻¹ * h₂ : H) : G) ∈ Kconj H x := by
    have := hh
    rwa [Subgroup.mem_subgroupOf] at this
  -- hKsub : (h₁⁻¹ * h₂ : G) ∈ H ⊓ H.map (MulAut.conj x)
  obtain ⟨hH, hM⟩ := Subgroup.mem_inf.mp hKsub
  obtain ⟨w, hwH, hweq⟩ := hM
  -- hweq : x * w * x⁻¹ = (h₁⁻¹ * h₂ : G)
  have h12 : ((h₁⁻¹ * h₂ : H) : G) = (h₁ : G)⁻¹ * (h₂ : G) := by
    push_cast; rfl
  rw [h12] at hweq
  -- hweq : x * w * x⁻¹ = (h₁ : G)⁻¹ * (h₂ : G)
  have eqn : (h₁ : G)⁻¹ * (h₂ : G) = x * w * x⁻¹ := by rw [← hweq]; rfl
  have key : ((h₁ : G) * x)⁻¹ * ((h₂ : G) * x) = w := by
    calc ((h₁ : G) * x)⁻¹ * ((h₂ : G) * x)
        = x⁻¹ * ((h₁ : G)⁻¹ * (h₂ : G)) * x := by group
      _ = x⁻¹ * (x * w * x⁻¹) * x := by rw [eqn]
      _ = w := by group
  rw [key]; exact hwH

/-- The image in `Quotient (rightRel H)` of `x * k⁻¹` lies in the right fiber
over the double coset of `x`. -/
private lemma rightToDC_mul (x : G) (k : H) :
    rightToDC H (Quotient.mk'' (x * (k : G)⁻¹)) = DoubleCoset.mk H H x := by
  simp only [rightToDC_mk]
  rw [DoubleCoset.eq]
  exact ⟨1, H.one_mem, (k : G), k.2, by group⟩

private lemma rightFiber_descend (x : G) (k₁ k₂ : H)
    (hh : (k₁⁻¹ * k₂ : H) ∈ (Kconj H x⁻¹).subgroupOf H) :
    (Quotient.mk'' (x * (k₁ : G)⁻¹) : Quotient (QuotientGroup.rightRel H)) =
      Quotient.mk'' (x * (k₂ : G)⁻¹) := by
  rw [Quotient.eq'', QuotientGroup.rightRel_apply]
  -- Goal: (x * k₂⁻¹) * (x * k₁⁻¹)⁻¹ ∈ H, i.e., x * k₂⁻¹ * k₁ * x⁻¹ ∈ H
  have hKsub : ((k₁⁻¹ * k₂ : H) : G) ∈ Kconj H x⁻¹ := by
    have := hh; rwa [Subgroup.mem_subgroupOf] at this
  obtain ⟨hH, hM⟩ := Subgroup.mem_inf.mp hKsub
  obtain ⟨w, hwH, hweq⟩ := hM
  have h12 : ((k₁⁻¹ * k₂ : H) : G) = (k₁ : G)⁻¹ * (k₂ : G) := by push_cast; rfl
  rw [h12] at hweq
  -- hweq : x⁻¹ * w * x = (k₁ : G)⁻¹ * (k₂ : G)
  have eqn : (k₁ : G)⁻¹ * (k₂ : G) = x⁻¹ * w * x := by
    have : x⁻¹ * w * (x⁻¹)⁻¹ = (k₁ : G)⁻¹ * (k₂ : G) := hweq
    rw [show (x⁻¹ : G)⁻¹ = x by group] at this
    exact this.symm
  -- We need: x * k₂⁻¹ * k₁ * x⁻¹ ∈ H. Now k₂⁻¹ * k₁ = (k₁⁻¹ * k₂)⁻¹.
  have key : x * (k₂ : G)⁻¹ * (k₁ : G) * x⁻¹ = w⁻¹ := by
    have : ((k₁ : G)⁻¹ * (k₂ : G))⁻¹ = (x⁻¹ * w * x)⁻¹ := by rw [eqn]
    -- LHS: k₂⁻¹ * k₁. RHS: x⁻¹ * w⁻¹ * x.
    have : (k₂ : G)⁻¹ * (k₁ : G) = x⁻¹ * w⁻¹ * x := by
      have h := this; group at h; group; exact h
    calc x * (k₂ : G)⁻¹ * (k₁ : G) * x⁻¹
        = x * ((k₂ : G)⁻¹ * (k₁ : G)) * x⁻¹ := by group
      _ = x * (x⁻¹ * w⁻¹ * x) * x⁻¹ := by rw [this]
      _ = w⁻¹ := by group
  -- Now: (x * k₂⁻¹) * (x * k₁⁻¹)⁻¹ = x * k₂⁻¹ * k₁ * x⁻¹ = w⁻¹ ∈ H.
  have : (x * (k₂ : G)⁻¹) * (x * (k₁ : G)⁻¹)⁻¹ = w⁻¹ := by
    calc (x * (k₂ : G)⁻¹) * (x * (k₁ : G)⁻¹)⁻¹
        = x * (k₂ : G)⁻¹ * (k₁ : G) * x⁻¹ := by group
      _ = w⁻¹ := key
  rw [this]
  exact H.inv_mem hwH

/-- The forward map from `H ⧸ (Kconj H x).subgroupOf H` into the left fiber over the
double coset of `x`. -/
noncomputable def leftFiberMap (x : G) (q : H ⧸ (Kconj H x).subgroupOf H) :
    {p : G ⧸ H // leftToDC H p = DoubleCoset.mk H H x} :=
  Quotient.liftOn' q
    (fun (h : H) => ⟨QuotientGroup.mk ((h : G) * x), leftToDC_mul H x h⟩)
    (by
      intro h₁ h₂ hh
      apply Subtype.ext
      have hh' : h₁⁻¹ * h₂ ∈ (Kconj H x).subgroupOf H := by
        have hq : (Quotient.mk'' h₁ : H ⧸ (Kconj H x).subgroupOf H) = Quotient.mk'' h₂ :=
          Quotient.sound hh
        rwa [Quotient.eq'', QuotientGroup.leftRel_apply] at hq
      exact leftFiber_descend H x h₁ h₂ hh')

/-- Surjectivity of the left fiber map. -/
private lemma leftFiberMap_surjective (x : G) :
    Function.Surjective (leftFiberMap H x) := by
  rintro ⟨p, hp⟩
  refine Quotient.inductionOn' p (fun g hg => ?_) hp
  simp only [leftToDC_mk, DoubleCoset.eq] at hg
  obtain ⟨a, ha, b, hb, hgab⟩ := hg
  -- hgab : x = a * g * b, so g = a⁻¹ * x * b⁻¹
  -- We want: ∃ h ∈ H, [h * x]_L = [g]_L. Take h = a⁻¹.
  refine ⟨QuotientGroup.mk ⟨a⁻¹, H.inv_mem ha⟩, ?_⟩
  apply Subtype.ext
  show (QuotientGroup.mk (a⁻¹ * x) : G ⧸ H) = QuotientGroup.mk g
  rw [QuotientGroup.eq]
  -- Goal: (a⁻¹ * x)⁻¹ * g ∈ H
  -- (a⁻¹ * x)⁻¹ * g = x⁻¹ * a * g. From x = a*g*b, a*g = x*b⁻¹. So x⁻¹*a*g = b⁻¹ ∈ H.
  have : (a⁻¹ * x)⁻¹ * g = x⁻¹ * a * g := by group
  rw [this]
  have : x⁻¹ * a * g = b⁻¹ := by
    have heq : a * g = x * b⁻¹ := by rw [hgab]; group
    calc x⁻¹ * a * g = x⁻¹ * (a * g) := by group
      _ = x⁻¹ * (x * b⁻¹) := by rw [heq]
      _ = b⁻¹ := by group
  rw [this]
  exact H.inv_mem hb

/-- Injectivity of the left fiber map. -/
private lemma leftFiberMap_injective (x : G) :
    Function.Injective (leftFiberMap H x) := by
  rintro q₁ q₂ heq
  refine Quotient.inductionOn₂' q₁ q₂ (fun h₁ h₂ heq => ?_) heq
  simp only [leftFiberMap, Quotient.liftOn'_mk''] at heq
  -- heq : ⟨[h₁ * x]_L, _⟩ = ⟨[h₂ * x]_L, _⟩
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
  -- Goal: ((h₁⁻¹ * h₂ : H) : G) ∈ Kconj H x
  -- From heq, we get [h₁ * x]_L = [h₂ * x]_L, i.e., (h₁ * x)⁻¹ * (h₂ * x) ∈ H
  have h_eq : (QuotientGroup.mk ((h₁ : G) * x) : G ⧸ H) = QuotientGroup.mk ((h₂ : G) * x) :=
    Subtype.mk.injEq .. ▸ heq
  rw [QuotientGroup.eq] at h_eq
  -- h_eq : ((h₁ : G) * x)⁻¹ * ((h₂ : G) * x) ∈ H
  have hkey : ((h₁ : G) * x)⁻¹ * ((h₂ : G) * x) = x⁻¹ * ((h₁ : G)⁻¹ * (h₂ : G)) * x := by group
  rw [hkey] at h_eq
  -- h_eq : x⁻¹ * (h₁⁻¹ * h₂) * x ∈ H
  rw [Kconj, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · -- (h₁⁻¹ * h₂ : G) ∈ H
    have : ((h₁⁻¹ * h₂ : H) : G) = (h₁ : G)⁻¹ * (h₂ : G) := by push_cast; rfl
    rw [this]
    exact H.mul_mem (H.inv_mem h₁.2) h₂.2
  · -- (h₁⁻¹ * h₂ : G) ∈ H.map (MulAut.conj x)
    rw [Subgroup.mem_map]
    refine ⟨x⁻¹ * ((h₁ : G)⁻¹ * (h₂ : G)) * x, h_eq, ?_⟩
    show x * (x⁻¹ * ((h₁ : G)⁻¹ * (h₂ : G)) * x) * x⁻¹ = ((h₁⁻¹ * h₂ : H) : G)
    have : ((h₁⁻¹ * h₂ : H) : G) = (h₁ : G)⁻¹ * (h₂ : G) := by push_cast; rfl
    rw [this]; group

/-- The left fiber bijection. -/
noncomputable def leftFiberEquiv (x : G) :
    H ⧸ (Kconj H x).subgroupOf H ≃ {p : G ⧸ H // leftToDC H p = DoubleCoset.mk H H x} :=
  Equiv.ofBijective (leftFiberMap H x) ⟨leftFiberMap_injective H x, leftFiberMap_surjective H x⟩

/-- The forward map from `H ⧸ (Kconj H x⁻¹).subgroupOf H` into the right fiber over the
double coset of `x`. -/
noncomputable def rightFiberMap (x : G) (q : H ⧸ (Kconj H x⁻¹).subgroupOf H) :
    {p : Quotient (QuotientGroup.rightRel H) // rightToDC H p = DoubleCoset.mk H H x} :=
  Quotient.liftOn' q
    (fun (k : H) => ⟨Quotient.mk'' (x * (k : G)⁻¹), rightToDC_mul H x k⟩)
    (by
      intro k₁ k₂ hh
      apply Subtype.ext
      have hh' : k₁⁻¹ * k₂ ∈ (Kconj H x⁻¹).subgroupOf H := by
        have hq : (Quotient.mk'' k₁ : H ⧸ (Kconj H x⁻¹).subgroupOf H) = Quotient.mk'' k₂ :=
          Quotient.sound hh
        rwa [Quotient.eq'', QuotientGroup.leftRel_apply] at hq
      exact rightFiber_descend H x k₁ k₂ hh')

private lemma rightFiberMap_surjective (x : G) :
    Function.Surjective (rightFiberMap H x) := by
  rintro ⟨p, hp⟩
  refine Quotient.inductionOn' p (fun g hg => ?_) hp
  simp only [rightToDC_mk] at hg
  rw [DoubleCoset.eq] at hg
  obtain ⟨a, ha, b, hb, hgab⟩ := hg
  -- hgab : x = a * g * b, so g = a⁻¹ * x * b⁻¹
  -- We want: ∃ k ∈ H, [x * k⁻¹]_R = [g]_R. Take k = b.
  refine ⟨QuotientGroup.mk ⟨b, hb⟩, ?_⟩
  apply Subtype.ext
  show (Quotient.mk'' (x * (b : G)⁻¹) : Quotient (QuotientGroup.rightRel H)) = Quotient.mk'' g
  rw [Quotient.eq'', QuotientGroup.rightRel_apply]
  -- Goal: g * (x * b⁻¹)⁻¹ ∈ H
  have : g * (x * b⁻¹)⁻¹ = g * b * x⁻¹ := by group
  rw [this]
  -- From x = a * g * b: g * b = a⁻¹ * x. So g * b * x⁻¹ = a⁻¹.
  have heq : g * b = a⁻¹ * x := by
    have : x = a * (g * b) := by rw [hgab]; group
    have : a⁻¹ * x = g * b := by rw [this]; group
    exact this.symm
  rw [show g * b * x⁻¹ = (g * b) * x⁻¹ from rfl, heq]
  have : a⁻¹ * x * x⁻¹ = a⁻¹ := by group
  rw [this]
  exact H.inv_mem ha

private lemma rightFiberMap_injective (x : G) :
    Function.Injective (rightFiberMap H x) := by
  rintro q₁ q₂ heq
  refine Quotient.inductionOn₂' q₁ q₂ (fun k₁ k₂ heq => ?_) heq
  simp only [rightFiberMap, Quotient.liftOn'_mk''] at heq
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
  have h_eq : (Quotient.mk'' (x * (k₁ : G)⁻¹) : Quotient (QuotientGroup.rightRel H)) =
      Quotient.mk'' (x * (k₂ : G)⁻¹) := Subtype.mk.injEq .. ▸ heq
  rw [Quotient.eq'', QuotientGroup.rightRel_apply] at h_eq
  -- h_eq : (x * k₂⁻¹) * (x * k₁⁻¹)⁻¹ ∈ H
  have hkey : (x * (k₂ : G)⁻¹) * (x * (k₁ : G)⁻¹)⁻¹ = x * ((k₂ : G)⁻¹ * (k₁ : G)) * x⁻¹ := by group
  rw [hkey] at h_eq
  -- h_eq : x * (k₂⁻¹ * k₁) * x⁻¹ ∈ H, i.e., (k₂⁻¹ * k₁) ∈ x⁻¹Hx
  -- and we want (k₁⁻¹ * k₂ : H : G) ∈ Kconj H x⁻¹ = H ∩ x⁻¹Hx
  -- (k₁⁻¹ * k₂) = (k₂⁻¹ * k₁)⁻¹, which is in x⁻¹Hx (subgroup closed under inverse)
  -- and in H (since k₁, k₂ ∈ H).
  rw [Kconj, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · have : ((k₁⁻¹ * k₂ : H) : G) = (k₁ : G)⁻¹ * (k₂ : G) := by push_cast; rfl
    rw [this]
    exact H.mul_mem (H.inv_mem k₁.2) k₂.2
  · -- (k₁⁻¹ * k₂ : G) ∈ H.map (MulAut.conj x⁻¹) i.e. = x⁻¹ H x
    rw [Subgroup.mem_map]
    have hk12 : ((k₁⁻¹ * k₂ : H) : G) = (k₁ : G)⁻¹ * (k₂ : G) := by push_cast; rfl
    -- k₁⁻¹ k₂ = (k₂⁻¹ k₁)⁻¹. Want it as conj x⁻¹ of something in H.
    -- We have x (k₂⁻¹ k₁) x⁻¹ ∈ H. Let w = x (k₂⁻¹ k₁) x⁻¹. Then conj x⁻¹ w⁻¹ = x⁻¹ w⁻¹ x.
    -- Compute: x⁻¹ (x (k₂⁻¹ k₁) x⁻¹)⁻¹ x = x⁻¹ x (k₁⁻¹ k₂) x⁻¹ x = k₁⁻¹ k₂. ✓
    refine ⟨(x * ((k₂ : G)⁻¹ * (k₁ : G)) * x⁻¹)⁻¹, H.inv_mem h_eq, ?_⟩
    show x⁻¹ * (x * ((k₂ : G)⁻¹ * (k₁ : G)) * x⁻¹)⁻¹ * (x⁻¹)⁻¹ = ((k₁⁻¹ * k₂ : H) : G)
    rw [hk12]
    group

/-- The right fiber bijection. -/
noncomputable def rightFiberEquiv (x : G) :
    H ⧸ (Kconj H x⁻¹).subgroupOf H ≃
      {p : Quotient (QuotientGroup.rightRel H) // rightToDC H p = DoubleCoset.mk H H x} :=
  Equiv.ofBijective (rightFiberMap H x)
    ⟨rightFiberMap_injective H x, rightFiberMap_surjective H x⟩

/-- The left fiber over the double coset of `c.out`. -/
private lemma leftFiber_nonempty (c : DoubleCoset.Quotient (H : Set G) (H : Set G)) :
    ∃ q : G ⧸ H, leftToDC H q = c :=
  ⟨QuotientGroup.mk c.out, by rw [leftToDC_mk, DoubleCoset.out_eq']⟩

/-- The right fiber over the double coset of `c.out`. -/
private lemma rightFiber_nonempty (c : DoubleCoset.Quotient (H : Set G) (H : Set G)) :
    ∃ q : Quotient (QuotientGroup.rightRel H), rightToDC H q = c :=
  ⟨Quotient.mk'' c.out, by rw [rightToDC_mk, DoubleCoset.out_eq']⟩

/-- The fiber-cardinality equality, giving an equivalence between left and right fibers. -/
private noncomputable def leftRightFiberEquiv [H.FiniteIndex]
    (c : DoubleCoset.Quotient (H : Set G) (H : Set G)) :
    {p : G ⧸ H // leftToDC H p = c} ≃
      {p : Quotient (QuotientGroup.rightRel H) // rightToDC H p = c} := by
  classical
  letI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel H)) := QuotientGroup.fintypeQuotientRightRel
  -- Substitute c with mk H H c.out
  have hc : DoubleCoset.mk H H c.out = c := DoubleCoset.out_eq' H H c
  -- Equivs: rewrite the type with hc.
  have ec : {p : G ⧸ H // leftToDC H p = c} ≃
      {p : G ⧸ H // leftToDC H p = DoubleCoset.mk H H c.out} :=
    Equiv.subtypeEquivRight (fun _ => by rw [hc])
  have ec' : {p : Quotient (QuotientGroup.rightRel H) // rightToDC H p = c} ≃
      {p : Quotient (QuotientGroup.rightRel H) // rightToDC H p = DoubleCoset.mk H H c.out} :=
    Equiv.subtypeEquivRight (fun _ => by rw [hc])
  -- Equal cardinality of H/K_x and H/K_x⁻¹
  letI : Fintype (H ⧸ (Kconj H c.out).subgroupOf H) :=
    Fintype.ofEquiv _ (leftFiberEquiv H c.out).symm
  letI : Fintype (H ⧸ (Kconj H c.out⁻¹).subgroupOf H) :=
    Fintype.ofEquiv _ (rightFiberEquiv H c.out).symm
  have h_eq : Fintype.card (H ⧸ (Kconj H c.out).subgroupOf H) =
      Fintype.card (H ⧸ (Kconj H c.out⁻¹).subgroupOf H) := by
    have h1 : Fintype.card (H ⧸ (Kconj H c.out).subgroupOf H) = (Kconj H c.out).relIndex H := by
      rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    have h2 : Fintype.card (H ⧸ (Kconj H c.out⁻¹).subgroupOf H) = (Kconj H c.out⁻¹).relIndex H := by
      rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    rw [h1, h2, Kconj_relIndex_eq]
  exact ec.trans <| (leftFiberEquiv H c.out).symm.trans <|
    (Fintype.equivOfCardEq h_eq).trans <| (rightFiberEquiv H c.out).trans ec'.symm

/-- Existence of a common left/right transversal. -/
theorem exists_leftCoset_rightCoset_representative
    (G : Type) [Group G] (H : Subgroup G) [H.FiniteIndex] :
    ∃ S : Set G, Subgroup.IsComplement S H ∧ Subgroup.IsComplement H S := by
  classical
  letI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel H)) := QuotientGroup.fintypeQuotientRightRel
  -- Build the global equivalence using fiber-wise equivs.
  let e : (G ⧸ H) ≃ Quotient (QuotientGroup.rightRel H) :=
    Equiv.ofFiberEquiv (γ := DoubleCoset.Quotient (H : Set G) (H : Set G))
      (f := leftToDC H) (g := rightToDC H) (leftRightFiberEquiv H)
  have he : ∀ q : G ⧸ H, rightToDC H (e q) = leftToDC H q := by
    intro q
    -- e is built from per-fiber equivs, so it preserves the fiber.
    -- Equiv.ofFiberEquiv: g (e a) = f a (i.e., rightToDC (e q) = leftToDC q)
    show rightToDC H (e q) = leftToDC H q
    have hfib := ((leftRightFiberEquiv H (leftToDC H q))
      ((Equiv.sigmaFiberEquiv (leftToDC H)).symm q).snd).property
    convert hfib using 1
  -- For each q : G⧸H, the cosets q (as left) and e q (as right) MEET, by being in same DC.
  have hmeet : ∀ q : G ⧸ H, ∃ z, (QuotientGroup.mk z : G ⧸ H) = q ∧
      (Quotient.mk'' z : Quotient (QuotientGroup.rightRel H)) = e q := by
    intro q
    induction q using Quotient.inductionOn' with
    | _ g =>
      have hr := he (QuotientGroup.mk g)
      -- hr : rightToDC H (e [g]) = leftToDC H [g] = mk H H g
      simp only [leftToDC_mk] at hr
      -- e [g] is some quotient class. Get a rep.
      obtain ⟨g', hg'⟩ := Quotient.exists_rep (e (QuotientGroup.mk g))
      rw [← hg'] at hr
      simp only [rightToDC_mk] at hr
      -- hr : DoubleCoset.mk H H g' = DoubleCoset.mk H H g
      rw [DoubleCoset.eq] at hr
      obtain ⟨a, ha, b, hb, heq⟩ := hr
      -- heq : g = a * g' * b. So a * g' = g * b⁻¹.
      -- We want z with [z]_L = [g]_L and [z]_R = e [g] = [g']_R.
      -- [z]_L = [g]_L means g⁻¹ z ∈ H. [z]_R = [g']_R means z * g'⁻¹ ∈ H.
      -- Take z = a * g' = g * b⁻¹: then g⁻¹ * z = g⁻¹ * g * b⁻¹ = b⁻¹ ∈ H ✓.
      -- z * g'⁻¹ = a * g' * g'⁻¹ = a ∈ H ✓.
      refine ⟨a * g', ?_, ?_⟩
      · -- [a * g']_L = [g]_L, i.e., (a * g')⁻¹ * g ∈ H.
        -- From heq: g = a * g' * b, so (a * g')⁻¹ * g = b ∈ H.
        rw [QuotientGroup.eq]
        have : (a * g')⁻¹ * g = b := by rw [heq]; group
        rw [this]
        exact hb
      · rw [← hg']
        rw [Quotient.eq'', QuotientGroup.rightRel_apply]
        have : g' * (a * g')⁻¹ = a⁻¹ := by group
        rw [this]
        exact H.inv_mem ha
  -- For each q, choose a witness z_q.
  choose z hz_left hz_right using hmeet
  -- S := range z. The map q ↦ z q is injective (since q ↦ [z q]_L = q is injective).
  have hz_inj : Function.Injective z := by
    intro q₁ q₂ heq
    have : (QuotientGroup.mk (z q₁) : G ⧸ H) = QuotientGroup.mk (z q₂) := by rw [heq]
    rw [hz_left, hz_left] at this
    exact this
  -- S := range z.
  refine ⟨Set.range z, ?_, ?_⟩
  -- First: IsComplement S H — S is a left transversal.
  · rw [Subgroup.isComplement_subgroup_right_iff_bijective]
    refine ⟨?_, ?_⟩
    · -- Injectivity of restrict mk to range z.
      rintro ⟨_, q₁, rfl⟩ ⟨_, q₂, rfl⟩ heq
      have heq' : (QuotientGroup.mk (z q₁) : G ⧸ H) = QuotientGroup.mk (z q₂) := heq
      rw [hz_left, hz_left] at heq'
      simp only [Subtype.mk.injEq]
      rw [heq']
    · -- Surjectivity.
      intro q
      exact ⟨⟨z q, q, rfl⟩, hz_left q⟩
  -- Second: IsComplement H S — S is a right transversal.
  · rw [Subgroup.isComplement_subgroup_left_iff_bijective]
    refine ⟨?_, ?_⟩
    · -- Injectivity of restrict mk'' to range z.
      rintro ⟨_, q₁, rfl⟩ ⟨_, q₂, rfl⟩ heq
      have heq' : (Quotient.mk'' (z q₁) : Quotient (QuotientGroup.rightRel H)) =
          Quotient.mk'' (z q₂) := heq
      rw [hz_right, hz_right] at heq'
      have : q₁ = q₂ := e.injective heq'
      simp only [Subtype.mk.injEq]
      rw [this]
    · -- Surjectivity.
      intro q'
      refine ⟨⟨z (e.symm q'), e.symm q', rfl⟩, ?_⟩
      show (Quotient.mk'' (z (e.symm q')) : Quotient (QuotientGroup.rightRel H)) = q'
      rw [hz_right]
      exact e.apply_symm_apply q'

end Problem3

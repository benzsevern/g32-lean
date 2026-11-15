module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Constructions

/-! # Section traces for finite orbit quotients
The trace sums over the group, retaining stabilizer multiplicities.
-/
public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The orbit sum is invariant, including for an action with stabilizers.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter III, section 7, transfer for finite orbit maps. -/
theorem finite_orbit_sum_invariant
    {A : Type*} [TopologicalSpace A] (G : Type*) [Group G] [Fintype G]
    (a : G → (A ≃ₜ A)) (ha : ∀ g h x, a (g * h) x = a g (a h x))
    (f : A → ℚ) (g : G) (x : A) :
    (∑ h : G, f (a h (a g x))) = ∑ h : G, f (a h x) := by
  simp_rw [← ha]
  exact Function.Bijective.sum_comp (Group.mulRight_bijective g) (fun h => f (a h x))

/-- Orbit sums descend to a linear trace on locally constant rational sections.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter III, section 7, transfer for finite orbit maps. -/
theorem finite_quotient_locallyConstant_trace
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (G : Type*) [Group G] [Fintype G]
    (a : G → (A ≃ₜ A)) (ha : ∀ g h x, a (g * h) x = a g (a h x))
    (q : A → B) (hq : Topology.IsQuotientMap q)
    (horbit : ∀ x y, q x = q y → ∃ g, a g x = y) :
    ∃ T : LocallyConstant A ℚ →ₗ[ℚ] LocallyConstant B ℚ,
      ∀ f x, T f (q x) = ∑ g : G, f (a g x) := by
  let N : LocallyConstant A ℚ →ₗ[ℚ] LocallyConstant A ℚ :=
    ∑ g : G, LocallyConstant.comapₗ ℚ ⟨a g, (a g).continuous⟩
  have hN (f : LocallyConstant A ℚ) (x : A) :
      N f x = ∑ g : G, f (a g x) := by
    change (LocallyConstant.evalₗ ℚ x)
      ((∑ g : G, LocallyConstant.comapₗ ℚ ⟨a g, (a g).continuous⟩) f) = _
    rw [LinearMap.sum_apply, map_sum]
    rfl
  have hfiber (f : LocallyConstant A ℚ) {x y : A} (h : q x = q y) : N f x = N f y := by
    obtain ⟨g, rfl⟩ := horbit x y h
    rw [hN, hN]
    exact (finite_orbit_sum_invariant G a ha f g x).symm
  let s := Function.surjInv hq.surjective
  have hs (y : B) : q (s y) = y := Function.rightInverse_surjInv hq.surjective y
  have hn (f : LocallyConstant A ℚ) (x : A) : N f (s (q x)) = N f x :=
    hfiber f (hs (q x))
  let tr (f : LocallyConstant A ℚ) : LocallyConstant B ℚ :=
    ⟨fun y => N f (s y), fun U => hq.isOpen_preimage.mp (by
      have he : q ⁻¹' ((fun y => N f (s y)) ⁻¹' U) = (N f) ⁻¹' U := by
        ext x
        simp only [Set.mem_preimage, hn]
      rw [he]
      exact (N f).isLocallyConstant U)⟩
  refine ⟨{ toFun := tr, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro f g
    ext y
    change N (f + g) (s y) = N f (s y) + N g (s y)
    rw [map_add]
    rfl
  · intro r f
    ext y
    change N (r • f) (s y) = r • N f (s y)
    rw [map_smul]
    rfl
  · intro f x
    change N f (s (q x)) = _
    rw [hn, hN]

/-- The section trace composed with pullback multiplies by the group order.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter III, section 7, transfer degree identity. -/
theorem finite_quotient_section_trace_degree
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (G : Type*) [Group G] [Fintype G] (a : G → (A ≃ₜ A))
    (q : C(A, B)) (hsurj : Function.Surjective q)
    (hinv : ∀ g x, q (a g x) = q x)
    (T : LocallyConstant A ℚ →ₗ[ℚ] LocallyConstant B ℚ)
    (hT : ∀ f x, T f (q x) = ∑ g : G, f (a g x)) :
    T.comp (LocallyConstant.comapₗ ℚ q) =
      (Fintype.card G : ℚ) • LinearMap.id := by
  ext f y
  obtain ⟨x, rfl⟩ := hsurj y
  change T (f.comap q) (q x) = (Fintype.card G : ℚ) • f (q x)
  rw [hT]
  change (∑ g : G, f (q (a g x))) = _
  simp only [hinv, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

/-- Pullback of the section trace is exactly the sum of the group pullbacks.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter III, section 7, transfer norm identity. -/
theorem finite_quotient_section_trace_norm
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (G : Type*) [Fintype G] (a : G → (A ≃ₜ A)) (q : C(A, B))
    (T : LocallyConstant A ℚ →ₗ[ℚ] LocallyConstant B ℚ)
    (hT : ∀ f x, T f (q x) = ∑ g : G, f (a g x)) :
    (LocallyConstant.comapₗ ℚ q).comp T =
      ∑ g : G, LocallyConstant.comapₗ ℚ ⟨a g, (a g).continuous⟩ := by
  ext f x
  change T f (q x) = ((∑ g : G,
    LocallyConstant.comapₗ ℚ ⟨a g, (a g).continuous⟩) f) x
  rw [hT, LinearMap.sum_apply]
  change _ = (LocallyConstant.evalₗ ℚ x)
    (∑ g : G, LocallyConstant.comapₗ ℚ ⟨a g, (a g).continuous⟩ f)
  rw [map_sum]
  rfl

/-- Section traces commute with equivariant maps between orbit quotients.
This includes restriction to invariant open subsets.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter III, section 7, naturality of transfer. -/
theorem finite_quotient_section_trace_naturality
    {A B C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D]
    (G : Type*) [Fintype G] (a : G → (A ≃ₜ A)) (b : G → (C ≃ₜ C))
    (q : C(A, B)) (r : C(C, D)) (hr : Function.Surjective r)
    (i : C(C, A)) (j : C(D, B))
    (hcomm : ∀ x, q (i x) = j (r x))
    (hequiv : ∀ g x, i (b g x) = a g (i x))
    (T : LocallyConstant A ℚ →ₗ[ℚ] LocallyConstant B ℚ)
    (S : LocallyConstant C ℚ →ₗ[ℚ] LocallyConstant D ℚ)
    (hT : ∀ f x, T f (q x) = ∑ g : G, f (a g x))
    (hS : ∀ f x, S f (r x) = ∑ g : G, f (b g x)) :
    S.comp (LocallyConstant.comapₗ ℚ i) = (LocallyConstant.comapₗ ℚ j).comp T := by
  ext f y
  obtain ⟨x, rfl⟩ := hr y
  change S (f.comap i) (r x) = T f (j (r x))
  rw [hS, ← hcomm x, hT]
  change (∑ g : G, f (i (b g x))) = _
  simp_rw [hequiv]

/-- Orbit traces exist on the inverse image of every open subset of the quotient. -/
theorem finite_quotient_open_locallyConstant_trace
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (G : Type*) [Group G] [Fintype G]
    (a : G → (A ≃ₜ A)) (ha : ∀ g h x, a (g * h) x = a g (a h x))
    (q : A → B) (hq : Topology.IsQuotientMap q)
    (hinv : ∀ g x, q (a g x) = q x)
    (horbit : ∀ x y, q x = q y → ∃ g, a g x = y)
    (U : TopologicalSpace.Opens B) :
    ∃ T : LocallyConstant (q ⁻¹' U) ℚ →ₗ[ℚ] LocallyConstant U ℚ,
      ∀ f (x : q ⁻¹' U), T f ⟨q x, x.property⟩ =
        ∑ g : G, f ⟨a g x, by simpa only [Set.mem_preimage, hinv] using x.property⟩ := by
  let aU : G → ((q ⁻¹' U) ≃ₜ (q ⁻¹' U)) := fun g =>
    (a g).subtype (fun x => by simp only [Set.mem_preimage, hinv])
  have haU : ∀ g h (x : q ⁻¹' U), aU (g * h) x = aU g (aU h x) := by
    intro g h x
    apply Subtype.ext
    exact ha g h x
  apply finite_quotient_locallyConstant_trace G aU haU
    ((U : Set B).restrictPreimage q) (hq.restrictPreimage_isOpen U.isOpen)
  intro x y hxy
  obtain ⟨g, hg⟩ := horbit x y (congrArg Subtype.val hxy)
  exact ⟨g, Subtype.ext hg⟩

end HodgeLean.Foundations.Program

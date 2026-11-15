import HodgeLean.Adapters.NormalConeB4Defs
import HodgeLean.Foundations.AlgebraicTopology.Singular.CohomologyWithSupportProofs
import HodgeLean.Adapters.NormalConeB4aClassRestriction
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologySheaf

/-!
Finite weighted cycle data and local support comparisons.
Source: Fulton, Intersection Theory, §19.1.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open scoped BigOperators
namespace HodgeLean.Adapters.SupportedCycleClasses

def weightedCycle {ι : Type*} [Fintype ι] {Z : Scheme.{0}}
    (γ : ι → AlgebraicCycle Z ℚ) (a : ι → ℚ) : AlgebraicCycle Z ℚ :=
  ∑ i, (γ i).mapRange (a i * ·) (mul_zero _)

theorem weightedCycle_apply {ι : Type*} [Fintype ι] {Z : Scheme.{0}}
    (γ : ι → AlgebraicCycle Z ℚ) (a : ι → ℚ) (ξ : Z) :
    weightedCycle γ a ξ = ∑ i, a i * γ i ξ := by
  classical
  simp [weightedCycle]

theorem coefficient_at_component {ι : Type*} [Fintype ι] {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) (γ : ι → AlgebraicCycle Z ℚ)
    (hd : ∀ i j, i ≠ j → Disjoint (a3b4_cycleSupport q (γ i)) (a3b4_cycleSupport q (γ j)))
    (a : ι → ℚ) (t : ι) (x : ComplexPoint (Over.mk q))
    (hx : x ∈ a3b4_cycleSupport q (γ t)) (ξ : Z)
    (hξ : x.underlying ∈ closure ({ξ} : Set Z)) :
    weightedCycle γ a ξ = a t * γ t ξ := by
  classical
  rw [weightedCycle_apply, Finset.sum_eq_single t]
  · intro i _ hit
    have hz : γ i ξ = 0 := by
      by_contra hn
      have hxi : x ∈ a3b4_cycleSupport q (γ i) :=
        Set.mem_iUnion₂.mpr ⟨ξ, hn, hξ⟩
      exact Set.disjoint_left.mp (hd i t hit) hxi hx
    rw [hz, mul_zero]
  · simp

theorem weightedCycle_support {ι : Type*} [Fintype ι] {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) (γ : ι → AlgebraicCycle Z ℚ)
    (hd : ∀ i j, i ≠ j → Disjoint (a3b4_cycleSupport q (γ i)) (a3b4_cycleSupport q (γ j)))
    (a : ι → ℚ) :
    a3b4_cycleSupport q (weightedCycle γ a) =
      ⋃ i, ⋃ (_ : a i ≠ 0), a3b4_cycleSupport q (γ i) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨ξ, hξ, hxξ⟩ := Set.mem_iUnion₂.mp hx
    have hn : ∃ i, a i * γ i ξ ≠ 0 := by
      by_contra h
      have hz : ∀ i, a i * γ i ξ = 0 := by
        push_neg at h
        exact h
      have : weightedCycle γ a ξ = 0 := by rw [weightedCycle_apply]; exact Finset.sum_eq_zero (fun i _ => hz i)
      exact hξ this
    obtain ⟨i, hi⟩ := hn
    exact Set.mem_iUnion₂.mpr ⟨i, (mul_ne_zero_iff.mp hi).1,
      Set.mem_iUnion₂.mpr ⟨ξ, (mul_ne_zero_iff.mp hi).2, hxξ⟩⟩
  · intro hx
    obtain ⟨i, ha, hxi⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨ξ, hξ, hxξ⟩ := Set.mem_iUnion₂.mp hxi
    refine Set.mem_iUnion₂.mpr ⟨ξ, ?_, hxξ⟩
    change weightedCycle γ a ξ ≠ 0
    rw [coefficient_at_component q γ hd a i x (Set.mem_iUnion₂.mpr ⟨ξ, hξ, hxξ⟩) ξ hxξ]
    exact mul_ne_zero ha hξ

theorem multiplicity_finset {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q]
    (γ : AlgebraicCycle Z ℚ) (x : ComplexPoint (Over.mk q)) (F : Finset Z)
    (hF : γ.support ⊆ (F : Set Z)) :
    a3b4_multiplicity q γ x = ∑ ξ ∈ F,
      if ∃ U : Set (ComplexPoint (Over.mk q)), IsOpen U ∧ x ∈ U ∧
        U ∩ a3b4_cycleSupport q γ ⊆ Point.underlying ⁻¹' closure {ξ}
      then γ ξ else 0 := by
  classical
  haveI := a3b4_compactSpace q
  unfold a3b4_multiplicity
  apply Finset.sum_subset
  · intro ξ hξ
    exact hF ((a3b2_support_finite γ).mem_toFinset.mp hξ)
  · intro ξ _ hξ
    have hz : γ ξ = 0 := by
      simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hξ
    simp only [hz, ite_self]

theorem weightedCycle_multiplicity {ι : Type*} [Fintype ι] {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q]
    (γ : ι → AlgebraicCycle Z ℚ)
    (hd : ∀ i j, i ≠ j → Disjoint (a3b4_cycleSupport q (γ i)) (a3b4_cycleSupport q (γ j)))
    (a : ι → ℚ) (t : ι) (x : ComplexPoint (Over.mk q))
    (hx : x ∈ a3b4_cycleSupport q (γ t))
    (V : Set (ComplexPoint (Over.mk q))) (hVo : IsOpen V) (hxV : x ∈ V)
    (hlocal : ∀ y ∈ V, y ∈ a3b4_cycleSupport q (weightedCycle γ a) ↔
      y ∈ a3b4_cycleSupport q (γ t)) :
    a3b4_multiplicity q (weightedCycle γ a) x = a t * a3b4_multiplicity q (γ t) x := by
  classical
  haveI := a3b4_compactSpace q
  let F := (a3b2_support_finite (weightedCycle γ a)).toFinset ∪
    (a3b2_support_finite (γ t)).toFinset
  rw [multiplicity_finset q (weightedCycle γ a) x F (by
    intro ξ hξ; exact Finset.mem_union_left _ ((a3b2_support_finite (weightedCycle γ a)).mem_toFinset.mpr hξ)),
    multiplicity_finset q (γ t) x F (by
    intro ξ hξ; exact Finset.mem_union_right _ ((a3b2_support_finite (γ t)).mem_toFinset.mpr hξ)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ξ _
  have he : (∃ U : Set (ComplexPoint (Over.mk q)), IsOpen U ∧ x ∈ U ∧
      U ∩ a3b4_cycleSupport q (weightedCycle γ a) ⊆ Point.underlying ⁻¹' closure {ξ}) ↔
      (∃ U : Set (ComplexPoint (Over.mk q)), IsOpen U ∧ x ∈ U ∧
      U ∩ a3b4_cycleSupport q (γ t) ⊆ Point.underlying ⁻¹' closure {ξ}) := by
    constructor
    · rintro ⟨U, hU, hxU, hsub⟩
      exact ⟨U ∩ V, hU.inter hVo, ⟨hxU, hxV⟩,
        fun y hy => hsub ⟨hy.1.1, (hlocal y hy.1.2).mpr hy.2⟩⟩
    · rintro ⟨U, hU, hxU, hsub⟩
      exact ⟨U ∩ V, hU.inter hVo, ⟨hxU, hxV⟩,
        fun y hy => hsub ⟨hy.1.1, (hlocal y hy.1.2).mp hy.2⟩⟩
  rw [if_congr he rfl rfl]
  split_ifs with h
  · obtain ⟨U, _, hxU, hsub⟩ := h
    exact coefficient_at_component q γ hd a t x hx ξ (hsub ⟨hxU, hx⟩)
  · exact (mul_zero _).symm

end HodgeLean.Adapters.SupportedCycleClasses

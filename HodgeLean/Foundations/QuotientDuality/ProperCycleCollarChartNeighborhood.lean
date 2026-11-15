import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarPointTriad

/-! # Actual collar neighborhoods retained inside a specified local chart
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- A support point in an original chart has an actual ambient open neighborhood inside both the chart and collar, whose retraction values stay in the same original chart.
Source: ProperCycleSupportCollar.inclusion_factor; ProperCycleSupportCollar.inclusion_retraction; continuity of the retained retraction.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_neighborhood
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    {Z : Type} [TopologicalSpace Z] (e : OpenPartialHomeomorph X Z)
    (z : S) (hz : z.val ∈ e.source) :
    ∃ W : Opens X, z.val ∈ W ∧ (W : Set X) ⊆ e.source ∧
      ∃ hWN : (W : Set X) ⊆ C.neighborhood,
        ∀ (x : X) (hx : x ∈ W),
          (C.retraction ⟨x, hWN hx⟩).val ∈ e.source := by
  let V : Set C.neighborhood :=
    Subtype.val ⁻¹' e.source ∩ C.retraction ⁻¹' (Subtype.val ⁻¹' e.source)
  have hV : IsOpen V :=
    (e.open_source.preimage continuous_subtype_val).inter
      ((e.open_source.preimage continuous_subtype_val).preimage C.retraction.hom.continuous)
  have hj : (C.inclusion z).val = z.val := by
    have h := ConcreteCategory.congr_hom C.inclusion_factor (z : TopCat.of S)
    exact h
  have hr : C.retraction (C.inclusion z) = z :=
    ConcreteCategory.congr_hom C.inclusion_retraction z
  have hzV : C.inclusion z ∈ V := by
    constructor
    · change (C.inclusion z).val ∈ e.source
      rw [hj]
      exact hz
    · change (C.retraction (C.inclusion z)).val ∈ e.source
      rw [hr]
      exact hz
  let W : Opens X := ⟨Subtype.val '' V,
    C.isOpen.isOpenEmbedding_subtypeVal.isOpenMap V hV⟩
  have hWN : (W : Set X) ⊆ C.neighborhood := by
    rintro x ⟨u, _, rfl⟩
    exact u.property
  refine ⟨W, ⟨C.inclusion z, hzV, hj⟩, ?_, hWN, ?_⟩
  · rintro x ⟨u, hu, rfl⟩
    exact hu.1
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact hu.2

end HodgeLean.Foundations.QuotientDuality

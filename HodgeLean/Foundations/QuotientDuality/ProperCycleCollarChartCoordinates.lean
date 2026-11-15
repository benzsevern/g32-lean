import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarRetractionOnSupport

/-! # Actual tangential retraction coordinates on original chart images
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Express the retained collar retraction in the original tangential chart coordinates on an actual chart-contained neighborhood.
Source: OpenPartialHomeomorph.homeomorphOfImageSubsetSource; ProperCycleSupportCollar.chart_neighborhood.
HC no distance; AV milestone no distance. -/
def ProperCycleSupportCollar.chart_tangential_coordinates
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    {E Y : Type} [TopologicalSpace E] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source) :
    C(e '' (W : Set X), E) := by
  let H : W ≃ₜ e '' (W : Set X) := e.homeomorphOfImageSubsetSource hWe rfl
  let F : C(e '' (W : Set X), C.neighborhood) :=
    ⟨fun u => ⟨(H.symm u).val, hWN (H.symm u).property⟩,
      (continuous_subtype_val.comp H.symm.continuous).subtype_mk _⟩
  let R : C(e '' (W : Set X), e.source) :=
    ⟨fun u => ⟨(C.retraction (F u)).val, hR (H.symm u).val (H.symm u).property⟩,
      (continuous_subtype_val.comp (C.retraction.hom.continuous.comp F.continuous)).subtype_mk _⟩
  exact ⟨fun u => (e.toHomeomorphSourceTarget (R u)).val.1,
    continuous_fst.comp (continuous_subtype_val.comp
      (e.toHomeomorphSourceTarget.continuous.comp R.continuous))⟩

/-- At an actual original chart point, the constructed tangential retraction coordinates retain the literal chart value of the original collar retraction.
Source: OpenPartialHomeomorph.homeomorphOfImageSubsetSource; Homeomorph.symm_apply_apply.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_tangential_coordinates_image
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    {E Y : Type} [TopologicalSpace E] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (x : X) (hx : x ∈ W) :
    C.chart_tangential_coordinates e W hWe hWN hR ⟨e x, ⟨x, hx, rfl⟩⟩ =
      (e (C.retraction ⟨x, hWN hx⟩).val).1 := by
  let H : W ≃ₜ e '' (W : Set X) := e.homeomorphOfImageSubsetSource hWe rfl
  change (e (C.retraction ⟨(H.symm (H ⟨x, hx⟩)).val,
    hWN (H.symm (H ⟨x, hx⟩)).property⟩).val).1 = _
  rw [H.symm_apply_apply]

end HodgeLean.Foundations.QuotientDuality

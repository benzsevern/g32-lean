import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartCoordinates

/-! # Tangential collar coordinates on the original flattened support
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- On the original normal fibre of a flattened support chart, the actual collar tangential coordinates equal the original tangential coordinates.
Source: ProperCycleSupportCollar.retraction_on_support; OpenPartialHomeomorph.homeomorphOfImageSubsetSource.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_tangential_coordinates_on_normal_fibre
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    {E Y : Type} [TopologicalSpace E] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (u : e '' (W : Set X)) (hu : u.val.2 = y) :
    C.chart_tangential_coordinates e W hWe hWN hR u = u.val.1 := by
  let H : W ≃ₜ e '' (W : Set X) := e.homeomorphOfImageSubsetSource hWe rfl
  let x := (H.symm u).val
  have hxW : x ∈ W := (H.symm u).property
  have he : e x = u.val := congrArg Subtype.val (H.apply_symm_apply u)
  have hxS : x ∈ S := (hflat x (hWe hxW)).mpr ((congrArg Prod.snd he).trans hu)
  change (e (C.retraction ⟨x, hWN hxW⟩).val).1 = u.val.1
  rw [C.retraction_on_support ⟨x, hWN hxW⟩ hxS, he]

end HodgeLean.Foundations.QuotientDuality

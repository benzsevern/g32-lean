import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartCoordinates

/-! # Actual tangential charts on the original flattened support
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- The original flattened chart identifies its actual support-open with its literal tangential target slice.
Source: OpenPartialHomeomorph.toHomeomorphSourceTarget; Homeomorph.subtype; subspace topology.
HC no distance; AV milestone no distance. -/
def properCycle_flat_support_chart_homeomorph
    (X : TopCat.{0}) (S : Set X) {E Y : Type} [TopologicalSpace E] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (y : Y)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y) :
    {s : S | s.val ∈ e.source} ≃ₜ {v : E | (v, y) ∈ e.target} := by
  let P : {s : S | s.val ∈ e.source} ≃ₜ {x : e.source | x.val ∈ S} :=
    { toFun s := ⟨⟨s.val.val, s.property⟩, s.val.property⟩
      invFun s := ⟨⟨s.val.val, s.property⟩, s.val.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _ }
  let Q : {x : e.source | x.val ∈ S} ≃ₜ {u : e.target | u.val.2 = y} :=
    e.toHomeomorphSourceTarget.subtype (fun x => hflat x.val x.property)
  have htarget (u : {u : e.target | u.val.2 = y}) : (u.val.val.1, y) ∈ e.target := by
    have he : (u.val.val.1, y) = u.val.val := Prod.ext rfl u.property.symm
    exact he.symm ▸ u.val.property
  let R : {u : e.target | u.val.2 = y} ≃ₜ {v : E | (v, y) ∈ e.target} :=
    { toFun u := ⟨u.val.val.1, htarget u⟩
      invFun v := ⟨⟨(v.val, y), v.property⟩, rfl⟩
      left_inv u := Subtype.ext (Subtype.ext (Prod.ext rfl u.property.symm))
      right_inv _ := rfl
      continuous_toFun := (continuous_fst.comp
        (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk htarget
      continuous_invFun := (continuous_subtype_val.prodMk continuous_const).subtype_mk _ |>.subtype_mk _ }
  exact P.trans (Q.trans R)

end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.Program.SchoenCycleC2ImmersionChartMapHelpers

/-! # Original immersion section maps in canonical affine coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The affine-coordinate map on actual ideal sections is exactly the
original immersion section map after the original source top-open comparison. -/
theorem affineOpenImmersion_sections {Q W : Scheme.{0}} (i : Q ⟶ W)
    [IsClosedImmersion i] (U : W.Opens) (hU : IsAffineOpen U) :
    (Scheme.ΓSpecIso Γ(W, U)).inv ≫ ((i ∣_ U) ≫ hU.isoSpec.hom).appTop ≫
      (i ⁻¹ᵁ U).topIso.hom = i.app U := by
  let V := i ⁻¹ᵁ U
  let hV := hU.preimage i
  let j := (i ∣_ U) ≫ hU.isoSpec.hom
  have h : hV.isoSpec.inv ≫ j = Spec.map (i.app U) :=
    s2e_closedImmersion_affine_chart_map i U hU
  have he := congrArg (fun t : Spec Γ(Q, V) ⟶ Spec Γ(W, U) =>
    t.appTop ≫ (Scheme.ΓSpecIso Γ(Q, V)).hom) h
  simp only [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_inv_appTop,
    Category.assoc, Iso.inv_hom_id_assoc] at he
  change j.appTop ≫ V.topIso.hom ≫ (Scheme.ΓSpecIso Γ(Q, V)).inv ≫
    (Scheme.ΓSpecIso Γ(Q, V)).hom = _ at he
  simp only [Iso.inv_hom_id, Category.comp_id] at he
  rw [Scheme.ΓSpecIso_naturality] at he
  change (Scheme.ΓSpecIso Γ(W, U)).inv ≫ (j.appTop ≫ V.topIso.hom) = _
  rw [he, Iso.inv_hom_id_assoc]

#print axioms affineOpenImmersion_sections
end HodgeLean.Foundations.Program.G32Native

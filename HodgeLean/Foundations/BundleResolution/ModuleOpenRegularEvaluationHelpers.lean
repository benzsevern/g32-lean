import HodgeLean.Foundations.BundleResolution.ModuleOpenTopEvaluationHelpers

/-! # Normalized local scalar evaluation is the original regular evaluation

The original section is retained under the actual open-point equivalence.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleResolution

theorem i1_openRegularEvaluation {Q : Over (Spec ↧ℂ)}
    (U : Q.left.Opens) (c : Γ(Q.left, U)) (x : ComplexPoint Q)
    (hx : x ∈ Point.overOpen U) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((ComplexPoint.liftToOpen Q U x hx).appTop (U.topIso.inv c)) =
      Point.evaluate U c x := by
  let z := ComplexPoint.asOpenPoint Q U x hx
  have hz : Point.map (ComplexPoint.openInclusion Q U) z = x :=
    congrArg Subtype.val ((ComplexPoint.openEquiv Q U).apply_symm_apply ⟨x, hx⟩)
  have h := ComplexPoint.evaluate_openEquiv (X := Q) (U := U) (V := ⊤)
    (U.topIso.inv c) z
  rw [hz] at h
  have he := ComplexPoint.evaluate_eq (Y := Q) U.ι_image_top
    ((U.ι.appIso ⊤).inv (U.topIso.inv c)) x
  have hs : Q.left.presheaf.map (eqToHom U.ι_image_top.symm).op
      ((U.ι.appIso ⊤).inv (U.topIso.inv c)) = c := by
    rw [Scheme.Opens.ι_appIso]
    change U.topIso.hom (U.topIso.inv c) = c
    exact U.topIso.inv_hom_id_apply c
  rw [hs] at he
  exact (ComplexPoint.evaluate_top_eq_appTop (X := ComplexPoint.openScheme Q U)
    (U.topIso.inv c) z).symm.trans (h.symm.trans he)

end HodgeLean.Foundations.BundleResolution

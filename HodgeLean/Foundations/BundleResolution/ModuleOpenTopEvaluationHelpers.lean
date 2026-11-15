import HodgeLean.Foundations.BundleResolution.ModuleFrameCoefficientHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
/-! # Continuous evaluation of sections on actual open subschemes

Top sections evaluate continuously at lifted complex points.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleResolution
variable {Q : Over (Spec ↧ℂ)}
theorem i1_openTopEvaluation_continuous (U : Q.left.Opens) (r : Γ(U.toScheme, ⊤)) :
    Continuous (Y := ℂ) (fun x : {z : ComplexPoint Q // z ∈ Point.overOpen U} =>
      (show ℂ from
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((ComplexPoint.liftToOpen Q U x.val x.property).appTop r))) := by
  have hc : Continuous (fun x : {z : ComplexPoint Q // z ∈ Point.overOpen U} =>
      ComplexPoint.asOpenPoint Q U x.val x.property) :=
    (ComplexPoint.openHomeomorph Q U).symm.continuous
  have ht : Continuous (Point.evaluate (X := ComplexPoint.openScheme Q U) ⊤ r) := by
    apply continuous_def.mpr
    intro O hO
    simpa [Point.overOpen] using Point.isOpen_overOpen_inter_preimage
      (X := ComplexPoint.openScheme Q U) ⊤ r O hO
  have h := ht.comp hc
  apply h.congr
  intro x
  exact ComplexPoint.evaluate_top_eq_appTop (X := ComplexPoint.openScheme Q U) r (ComplexPoint.asOpenPoint Q U x.val x.property)
end HodgeLean.Foundations.BundleResolution

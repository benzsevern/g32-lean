import HodgeLean.Foundations.Program.G32Native.PairedConormalHyperplaneComap
import HodgeLean.Foundations.Program.G32Native.PairedConormalIdealIsoPullback

/-! # The actual hyperplane ideal isomorphism preserving its original inclusion -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The canonical actual ideal comparison for the original hyperplane and polynomial projective isomorphism. -/
def conormalHyperplanePolynomialIdealIso (k : ℕ) :
    (Scheme.Modules.pullback (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom).obj
      (idealModule (s2e_hyperplaneIdeal k)) ≅
        idealModule (conormalNativeHyperplaneIdeal ℂ k) := by
  let f := (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom
  letI : IsIso (idealPullbackHom f (s2e_hyperplaneIdeal k)) :=
    conormal_idealPullbackHom_isIso f (s2e_hyperplaneIdeal k)
  exact (idealPullbackIso_exists f (s2e_hyperplaneIdeal k)
    (conormalNativeHyperplaneIdeal ℂ k) (conormal_polynomial_hyperplane_comap k).symm).choose

/-- The specified polynomial ideal isomorphism retains the actual inclusion into the structure module. -/
theorem conormalHyperplanePolynomialIdealIso_inclusion (k : ℕ) :
    (conormalHyperplanePolynomialIdealIso k).hom ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (conormalNativeHyperplaneIdeal ℂ k).subschemeι.toRingCatSheafHom) =
    (Scheme.Modules.pullback (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom).map
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (s2e_hyperplaneIdeal k).subschemeι.toRingCatSheafHom)) ≫
      (pullbackUnit (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom).hom := by
  let f := (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom
  letI : IsIso (idealPullbackHom f (s2e_hyperplaneIdeal k)) :=
    conormal_idealPullbackHom_isIso f (s2e_hyperplaneIdeal k)
  exact (idealPullbackIso_exists f (s2e_hyperplaneIdeal k)
    (conormalNativeHyperplaneIdeal ℂ k) (conormal_polynomial_hyperplane_comap k).symm).choose_spec

end HodgeLean.Foundations.Program.G32Native

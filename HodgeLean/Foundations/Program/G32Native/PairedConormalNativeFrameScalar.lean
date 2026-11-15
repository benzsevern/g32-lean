import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeNormalizedFrame
import HodgeLean.Foundations.Program.G32Native.PairedConormalIdealFrameScalar

/-! # Actual row scalars in the specified native hyperplane frame -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual normalized native frame evaluates each ideal row to its
literal coefficient, retaining the specified pullback and unit comparisons. -/
theorem conormal_native_normalized_frame_scalar (k : ℕ) (i : Fin (k + 1))
    (φ : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.unit (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf) :
    ((conormalNativeHyperplaneNormalizedPullbackFrame k i).hom ≫
      (Scheme.Modules.pullback (conormalNativeCoordinateOpen ℂ k i).1.ι).map φ ≫
        (pullbackUnit (conormalNativeCoordinateOpen ℂ k i).1.ι).hom).val.app
          (Opposite.op ⊤) (1 : Γ((conormalNativeCoordinateOpen ℂ k i).1.toScheme, ⊤)) =
      (conormalNativeCoordinateOpen ℂ k i).1.topIso.inv
        (conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k) φ
          (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
          (conormal_native_hyperplane_coordinate_mem ℂ k i)) := by
  change (((conormalNativeHyperplaneNormalizedFrame k i).hom ≫
      ((Scheme.Modules.restrictFunctorIsoPullback
        (conormalNativeCoordinateOpen ℂ k i).1.ι).app
          (idealModule (conormalNativeHyperplaneIdeal ℂ k))).hom) ≫ _ ≫ _).val.app _ _ = _
  rw [conormalNativeHyperplaneNormalizedFrame_hom]
  exact conormal_ideal_pullback_frame_scalar _ _ _ _ φ

end HodgeLean.Foundations.Program.G32Native

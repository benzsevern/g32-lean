import HodgeLean.Foundations.Program.G32Native.PairedConormalHyperplaneIdealIso
import HodgeLean.Foundations.BundleThom.FreeSheafProjectionHelpers
/-! # Homogeneous linear rows of the supplied original hyperplane-ideal relation map -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.Picard.LineBundles
open HodgeLean.Foundations.BundleThom
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Pull back one original row through the actual ideal isomorphism and structural unit comparison. -/
def conormalOriginalIdealRow (k m : ℕ)
    (b : idealModule (s2e_hyperplaneIdeal k) ⟶
      (SheafOfModules.free (Fin m) : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules))
    (t : Fin m) :
    idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.unit (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf :=
  (conormalHyperplanePolynomialIdealIso k).inv ≫
    (Scheme.Modules.pullback (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom).map
      (b ≫ i1_freeSheafProjection (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)) m t) ≫
    (pullbackUnit (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom).hom

/-- Every row of the actual original relation map has its normalized homogeneous linear numerator. -/
theorem conormal_original_ideal_rows_linear_forms (k m : ℕ) (hk : 1 ≤ k)
    (b : idealModule (s2e_hyperplaneIdeal k) ⟶
      (SheafOfModules.free (Fin m) : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules)) :
    ∃ p : Fin m → MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ 1,
      ∀ (t : Fin m) (i : Fin (k + 1)),
        conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k)
          (conormalOriginalIdealRow k m b t) (conormalNativeCoordinateOpen ℂ k i)
          (ProjSpace.coordinateRatioSection ℂ k i 0) (conormal_native_hyperplane_coordinate_mem ℂ k i) =
        ProjSpace.homogeneousRatioSection ℂ k 1 (p t) i := by
  classical
  choose p hp using fun t : Fin m => conormal_native_hyperplane_map_linear_form ℂ k hk
    (conormalOriginalIdealRow k m b t)
  exact ⟨p, hp⟩

end HodgeLean.Foundations.Program.G32Native

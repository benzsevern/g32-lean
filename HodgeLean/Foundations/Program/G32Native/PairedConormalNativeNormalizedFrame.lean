import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeGeneratorRegular

/-! # Native hyperplane frames pinned to the literal normalized equation -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual native ideal frame whose unit generator is the literal ratio X₀/Xᵢ. -/
def conormalNativeHyperplaneNormalizedFrame (k : ℕ) (i : Fin (k + 1)) :
    SheafOfModules.unit (conormalNativeCoordinateOpen ℂ k i).1.toScheme.ringCatSheaf ≅
      (idealModule (conormalNativeHyperplaneIdeal ℂ k)).restrict
        (conormalNativeCoordinateOpen ℂ k i).1.ι :=
  (idealLocalGeneratorIso (conormalNativeHyperplaneIdeal ℂ k)
    (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
    (conormal_native_hyperplane_generator_regular k i)
    (conormal_native_hyperplane_ideal_principal k i)).symm

/-- The specified frame arrow is the actual local-section map of the exact ratio section. -/
theorem conormalNativeHyperplaneNormalizedFrame_hom (k : ℕ) (i : Fin (k + 1)) :
    (conormalNativeHyperplaneNormalizedFrame k i).hom =
      localSectionHom (idealModule (conormalNativeHyperplaneIdeal ℂ k))
        (conormalNativeCoordinateOpen ℂ k i).1
        (idealSection (conormalNativeHyperplaneIdeal ℂ k)
          (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
          (conormal_native_hyperplane_coordinate_mem ℂ k i)) := by
  rfl

/-- The same normalized frame with its canonical restriction-to-pullback comparison retained. -/
def conormalNativeHyperplaneNormalizedPullbackFrame (k : ℕ) (i : Fin (k + 1)) :
    SheafOfModules.unit (conormalNativeCoordinateOpen ℂ k i).1.toScheme.ringCatSheaf ≅
      (Scheme.Modules.pullback (conormalNativeCoordinateOpen ℂ k i).1.ι).obj
        (idealModule (conormalNativeHyperplaneIdeal ℂ k)) :=
  conormalNativeHyperplaneNormalizedFrame k i ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback
      (conormalNativeCoordinateOpen ℂ k i).1.ι).app
        (idealModule (conormalNativeHyperplaneIdeal ℂ k))

end HodgeLean.Foundations.Program.G32Native

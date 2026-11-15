import HodgeLean.Foundations.Program.G32Native.PairedConormalGeneratorValues
import HodgeLean.Foundations.Program.G32Native.PairedConormalPresentationPointMap

/-! # Actual quotient generator values in the point presentation -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.BundleThom

/-- Applying the actual point presentation to a standard coordinate gives
exactly the point value of the corresponding supplied quotient generator. -/
theorem conormal_presentation_point_generator {X : Scheme.{0}} (k : ℕ)
    {M : X.Modules}
    (π : (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶ M)
    (x : Spec ↧ℂ ⟶ X) (r : Fin (k + 1)) :
    conormalPresentationPointMap k π x
      ((EulerModel.normalHomogeneousCoordinates k).symm (Pi.single r 1)) =
      pairedPointSectionValue M (conormalPresentationGenerator X k r ≫ π) x := by
  rw [← conormal_point_generator_coordinates x k r]
  change (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
    ((Scheme.Modules.pullback x).map π)
      ((conormalUnitFreeFibreCoordinates x k).symm
        (conormalUnitFreeFibreCoordinates x k _)) = _
  rw [LinearEquiv.symm_apply_apply]
  exact (paired_pointSectionValue_naturality π (conormalPresentationGenerator X k r) x).symm

#print axioms conormal_presentation_point_generator
end HodgeLean.Foundations.Program.G32Native

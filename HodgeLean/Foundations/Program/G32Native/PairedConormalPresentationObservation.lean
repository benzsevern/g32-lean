import HodgeLean.Foundations.Program.G32Native.PairedConormalPresentationGeneratorPoint
import HodgeLean.Foundations.Program.G32Native.PairedConormalKernelDualCoordinates

/-! # Ordered observations give exactly the actual quotient dual coordinates -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual dual coordinate vector evaluates the actual supplied ordered
quotient generators, retaining every index. -/
theorem conormal_presentation_dual_observations {X : Scheme.{0}} (k : ℕ)
    {M : X.Modules}
    (π : (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶ M)
    (x : Spec ↧ℂ ⟶ X)
    (ψ : Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj M))) :
    EulerModel.normalHomogeneousCoordinates k
      ((conormalModelDualCoordinates k).symm
        ((conormalPresentationPointMap k π x).dualMap ψ)) =
      fun r => ψ (pairedPointSectionValue M (conormalPresentationGenerator X k r ≫ π) x) := by
  funext r
  rw [← conormal_model_dual_coordinate, LinearEquiv.apply_symm_apply]
  change ψ (conormalPresentationPointMap k π x
    ((EulerModel.normalHomogeneousCoordinates k).symm (Pi.single r 1))) = _
  rw [conormal_presentation_point_generator]

#print axioms conormal_presentation_dual_observations
end HodgeLean.Foundations.Program.G32Native

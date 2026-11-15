import HodgeLean.Foundations.Program.G32Native.PairedConormalPresentationObservation
import HodgeLean.Foundations.Program.G32Native.PairedConormalGeneratorPullback
import HodgeLean.Foundations.Program.G32Native.PairedConormalModelPointValues

/-! # Actual quotient dual observations through the supplied conormal model -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.BundleThom

/-- Canonical model transport retains all original quotient generator evaluations
in exactly their ordered dual coordinates. -/
theorem paired_model_presentation_dual_observations {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) (d : Z ⟶ Y) (C : X.Modules) (M : Y.Modules)
    (E : C ≅ (Scheme.Modules.pullback f).obj M) (k : ℕ)
    (π : (SheafOfModules.unit Y.ringCatSheaf ⊞
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin k)) ⟶ M)
    (x : Spec ↧ℂ ⟶ X) (z : Spec ↧ℂ ⟶ Z) (h : x ≫ f = z ≫ d)
    (ψ : Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj C))) :
    EulerModel.normalHomogeneousCoordinates k ((conormalModelDualCoordinates k).symm
      ((conormalPresentationPointMap k (conormalPresentationPullback d k M π) z).dualMap
        ((pairedModelPointFibreIso f d C M E x z h).toLinearEquiv.symm.dualMap ψ))) =
      fun r => ψ (pairedPointSectionValue C
        (i1_moduleSectionPullback f M
          (conormalPresentationGenerator Y k r ≫ π) ≫ E.inv) x) := by
  rw [conormal_presentation_dual_observations]
  funext r
  rw [conormal_presentation_generator_pullback]
  exact paired_modelPointFibre_dual_value f d C M E x z h _ ψ

/-- The actual quotient dual vector is recovered directly from the ordered
global section observations, before any concrete projective normalization. -/
theorem paired_model_presentation_dual_vector {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) (d : Z ⟶ Y) (C : X.Modules) (M : Y.Modules)
    (E : C ≅ (Scheme.Modules.pullback f).obj M) (k : ℕ)
    (π : (SheafOfModules.unit Y.ringCatSheaf ⊞
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin k)) ⟶ M)
    (x : Spec ↧ℂ ⟶ X) (z : Spec ↧ℂ ⟶ Z) (h : x ≫ f = z ≫ d)
    (ψ : Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj C))) :
    (conormalModelDualCoordinates k).symm
      ((conormalPresentationPointMap k (conormalPresentationPullback d k M π) z).dualMap
        ((pairedModelPointFibreIso f d C M E x z h).toLinearEquiv.symm.dualMap ψ)) =
      (EulerModel.normalHomogeneousCoordinates k).symm (fun r => ψ (pairedPointSectionValue C
        (i1_moduleSectionPullback f M
          (conormalPresentationGenerator Y k r ≫ π) ≫ E.inv) x)) := by
  exact (EulerModel.normalHomogeneousCoordinates k).eq_symm_apply.mpr
    (paired_model_presentation_dual_observations f d C M E k π x z h ψ)

#print axioms paired_model_presentation_dual_vector
#print axioms paired_model_presentation_dual_observations
end HodgeLean.Foundations.Program.G32Native

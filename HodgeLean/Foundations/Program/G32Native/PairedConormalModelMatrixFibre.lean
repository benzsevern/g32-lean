import HodgeLean.Foundations.Program.G32Native.PairedConormalPresentationMatrixFibre
import HodgeLean.Foundations.Program.G32Native.PairedConormalModelPresentationObservations

/-! # Actual conormal fibre comparison through supplied model and quotient maps -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.BundleThom

/-- The supplied conormal model and actual quotient identify the actual normal
fibre with its matrix-corrected projective kernel. -/
def pairedModelMatrixFibreEquiv {Q : Over (Spec ↧ℂ)} {Y Z V : Scheme.{0}}
    (j : Q.left ⟶ V) (f : Q.left ⟶ Y) (d : Z ⟶ Y) (M : Y.Modules)
    (E : Conormal.sheaf j ≅ (Scheme.Modules.pullback f).obj M) (k : ℕ)
    (π : (SheafOfModules.unit Y.ringCatSheaf ⊞
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin k)) ⟶ M) [Epi π]
    [((Scheme.Modules.pullback d).obj M).IsLocallyFree]
    (x : ComplexPoint Q) (z : Spec ↧ℂ ⟶ Z) (h : x.left ≫ f = z ≫ d)
    (hdim : Module.finrank ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback z).obj ((Scheme.Modules.pullback d).obj M))) = k)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : IsUnit A)
    (v : Fin (k + 1) → ℂ) (hv : v ≠ 0) (r : ℂ × (Fin k → ℂ))
    (c : ℂ) (hc : c ≠ 0)
    (hcoords : EulerModel.normalHomogeneousCoordinates k r = c • A.mulVec v)
    (hrel : conormalPresentationPointMap k (conormalPresentationPullback d k M π) z r = 0) :
    i1_normalFibre j x ≃ₗ[ℂ]
      EulerModel.projectiveNormalKernel k
        (Projectivization.mk ℂ ((EulerModel.normalHomogeneousCoordinates k).symm v)
          ((EulerModel.normalHomogeneousCoordinates k).symm.map_ne_zero_iff.mpr hv)) := by
  letI : Epi (conormalPresentationPullback d k M π) :=
    conormal_presentation_pullback_epi d k M π
  exact (pairedModelPointFibreIso f d (Conormal.sheaf j) M E x.left z h).toLinearEquiv.symm.dualMap.trans
    (conormalPresentationMatrixFibreEquiv k (conormalPresentationPullback d k M π) z hdim
      A hA v hv r c hc hcoords hrel)

/-- The actual normal fibre comparison has the fixed matrix-corrected
coordinates of the supplied global conormal generator evaluations. -/
theorem pairedModelMatrixFibreEquiv_val {Q : Over (Spec ↧ℂ)} {Y Z V : Scheme.{0}}
    (j : Q.left ⟶ V) (f : Q.left ⟶ Y) (d : Z ⟶ Y) (M : Y.Modules)
    (E : Conormal.sheaf j ≅ (Scheme.Modules.pullback f).obj M) (k : ℕ)
    (π : (SheafOfModules.unit Y.ringCatSheaf ⊞
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin k)) ⟶ M) [Epi π]
    [((Scheme.Modules.pullback d).obj M).IsLocallyFree]
    (x : ComplexPoint Q) (z : Spec ↧ℂ ⟶ Z) (h : x.left ≫ f = z ≫ d)
    (hdim : Module.finrank ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback z).obj ((Scheme.Modules.pullback d).obj M))) = k)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : IsUnit A)
    (v : Fin (k + 1) → ℂ) (hv : v ≠ 0) (r : ℂ × (Fin k → ℂ))
    (c : ℂ) (hc : c ≠ 0)
    (hcoords : EulerModel.normalHomogeneousCoordinates k r = c • A.mulVec v)
    (hrel : conormalPresentationPointMap k (conormalPresentationPullback d k M π) z r = 0)
    (ψ : i1_normalFibre j x) :
    (pairedModelMatrixFibreEquiv j f d M E k π x z h hdim A hA v hv r c hc hcoords hrel ψ).val =
      ((conormalModelMatrixDualEquiv k A hA).toLinearMap.comp
        (EulerModel.normalHomogeneousCoordinates k).symm.toLinearMap)
        (pairedNormalGlobalObservations j (k + 1)
          (fun i => i1_moduleSectionPullback f M
            (conormalPresentationGenerator Y k i ≫ π) ≫ E.inv) x ψ) := by
  letI : Epi (conormalPresentationPullback d k M π) :=
    conormal_presentation_pullback_epi d k M π
  simp only [pairedModelMatrixFibreEquiv, LinearEquiv.trans_apply,
    conormalPresentationMatrixFibreEquiv_val]
  apply congrArg (conormalModelMatrixDualEquiv k A hA)
  exact paired_model_presentation_dual_vector f d (Conormal.sheaf j) M E k π x.left z h ψ

#print axioms pairedModelMatrixFibreEquiv_val
#print axioms pairedModelMatrixFibreEquiv
end HodgeLean.Foundations.Program.G32Native

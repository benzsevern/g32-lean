import HodgeLean.Foundations.Program.G32Native.PairedConormalScaledMatrixKernel
import HodgeLean.Foundations.Program.G32Native.PairedConormalPresentationDualKernel

/-! # The actual presented dual fibre corrected by its literal coefficient matrix -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
namespace HodgeLean.Foundations.Program.G32Native

/-- The supplied quotient and a nonzero scaled matrix relation identify its
actual dual fibre over the original homogeneous projective point. -/
def conormalPresentationMatrixFibreEquiv {X : Scheme.{0}} (k : ℕ)
    {M : X.Modules} [M.IsLocallyFree]
    (π : (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶ M) [Epi π]
    (x : Spec ↧ℂ ⟶ X)
    (hdim : Module.finrank ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj M)) = k)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : IsUnit A)
    (v : Fin (k + 1) → ℂ) (hv : v ≠ 0) (r : ℂ × (Fin k → ℂ))
    (c : ℂ) (hc : c ≠ 0)
    (hcoords : EulerModel.normalHomogeneousCoordinates k r = c • A.mulVec v)
    (hrel : conormalPresentationPointMap k π x r = 0) :
    Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj M)) ≃ₗ[ℂ]
      EulerModel.projectiveNormalKernel k
        (Projectivization.mk ℂ ((EulerModel.normalHomogeneousCoordinates k).symm v)
          ((EulerModel.normalHomogeneousCoordinates k).symm.map_ne_zero_iff.mpr hv)) := by
  have hAi := Matrix.mulVec_injective_iff_isUnit.mpr hA
  have hAv : A.mulVec v ≠ 0 := by
    intro hz
    apply hv
    apply hAi
    exact hz.trans (Matrix.mulVec_zero A).symm
  have hr : r ≠ 0 := by
    intro hz
    have h := congrArg (EulerModel.normalHomogeneousCoordinates k) hz
    rw [hcoords, map_zero] at h
    exact (smul_ne_zero hc hAv) h
  exact (conormalPresentationDualKernelEquiv k π x hdim r hr hrel).trans
    (conormalScaledMatrixKernelEquiv k A hA v hv r c hc hcoords)

/-- Matrix correction retains the literal dual coordinates of the supplied quotient. -/
theorem conormalPresentationMatrixFibreEquiv_val {X : Scheme.{0}} (k : ℕ)
    {M : X.Modules} [M.IsLocallyFree]
    (π : (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶ M) [Epi π]
    (x : Spec ↧ℂ ⟶ X)
    (hdim : Module.finrank ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj M)) = k)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : IsUnit A)
    (v : Fin (k + 1) → ℂ) (hv : v ≠ 0) (r : ℂ × (Fin k → ℂ))
    (c : ℂ) (hc : c ≠ 0)
    (hcoords : EulerModel.normalHomogeneousCoordinates k r = c • A.mulVec v)
    (hrel : conormalPresentationPointMap k π x r = 0)
    (ψ : Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj M))) :
    (conormalPresentationMatrixFibreEquiv k π x hdim A hA v hv r c hc hcoords hrel ψ).val =
      conormalModelMatrixDualEquiv k A hA ((conormalModelDualCoordinates k).symm
        ((conormalPresentationPointMap k π x).dualMap ψ)) := by
  simp only [conormalPresentationMatrixFibreEquiv, LinearEquiv.trans_apply,
    conormalScaledMatrixKernelEquiv_val]
  rfl

#print axioms conormalPresentationMatrixFibreEquiv_val
#print axioms conormalPresentationMatrixFibreEquiv
end HodgeLean.Foundations.Program.G32Native

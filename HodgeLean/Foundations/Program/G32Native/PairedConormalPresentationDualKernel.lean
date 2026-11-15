import HodgeLean.Foundations.Program.G32Native.PairedConormalPresentationPointMap
import HodgeLean.Foundations.Program.G32Native.PairedConormalQuotientDualRange

/-! # Actual presentation dual fibres in prescribed evaluation kernels -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual dual fibre of a supplied elementary presentation is identified
with the prescribed kernel by its nonzero actual relation vector. -/
def conormalPresentationDualKernelEquiv {X : Scheme.{0}} (k : ℕ)
    {M : X.Modules} [M.IsLocallyFree]
    (π : (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶ M) [Epi π]
    (x : Spec (CommRingCat.of ℂ) ⟶ X)
    (hdim : Module.finrank ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj M)) = k)
    (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0)
    (hrel : conormalPresentationPointMap k π x v = 0) :
    Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj M)) ≃ₗ[ℂ]
      LinearMap.ker (EulerModel.homogeneousNormalEvaluation k v) :=
  conormalQuotientDualKernelEquiv k (conormalPresentationPointMap k π x)
    (conormal_presentation_point_map_surjective k π x) v
    (conormal_quotient_kernel_eq_relation_span k (conormalPresentationPointMap k π x)
      (conormal_presentation_point_map_surjective k π x) hdim v hv hrel)

/-- The actual fibre comparison retains evaluation on every supplied presentation generator. -/
theorem conormal_presentation_dual_kernel_evaluation {X : Scheme.{0}} (k : ℕ)
    {M : X.Modules} [M.IsLocallyFree]
    (π : (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶ M) [Epi π]
    (x : Spec (CommRingCat.of ℂ) ⟶ X)
    (hdim : Module.finrank ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj M)) = k)
    (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0)
    (hrel : conormalPresentationPointMap k π x v = 0)
    (ψ : Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj M))) (w : ℂ × (Fin k → ℂ)) :
    EulerModel.homogeneousNormalEvaluation k
      (conormalPresentationDualKernelEquiv k π x hdim v hv hrel ψ).val w =
      ψ (conormalPresentationPointMap k π x w) := by
  rw [← conormal_model_dual_evaluation]
  change conormalModelDualCoordinates k
    ((conormalModelDualCoordinates k).symm
      ((conormalPresentationPointMap k π x).dualMap ψ)) w = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end HodgeLean.Foundations.Program.G32Native

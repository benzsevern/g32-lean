import HodgeLean.Foundations.BundleThom.ImmersionDefs

/-! # Matrix entries of a jointly continuous normal-coordinate family -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Joint continuity of a finite linear family gives continuity of its matrix entries. -/
theorem continuous_normalMatrix_of_joint {B : Type} [TopologicalSpace B] (k : ℕ)
    (L : B → (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (hL : Continuous (fun bv : B × (Fin k → ℂ) => L bv.1 bv.2)) :
    Continuous (fun b => LinearMap.toMatrix' (L b)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hc : Continuous (fun b : B => (b, (Pi.single j 1 : Fin k → ℂ))) :=
    continuous_id.prodMk continuous_const
  have h := (continuous_apply i).comp (hL.comp hc)
  exact h

end HodgeLean.Foundations.BundleThom

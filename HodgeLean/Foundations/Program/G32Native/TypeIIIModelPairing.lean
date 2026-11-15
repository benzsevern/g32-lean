import HodgeLean.Foundations.Program.G32Native.TypeIIIHomologyRank
import HodgeLean.Foundations.Program.G32Native.TypeIIIHomologyPairing
import HodgeLean.Foundations.Program.G32Native.TypeIIITraceInvariance

noncomputable section
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open Module
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite

/-- The actual homology pairing in the retained rank-three coordinates. -/
def typeIIIModelPairing (b : ℚ)
    (e : Dual ℚ (HQ A 1) ≃ₗ[ℚ] (Fin 3 → ℍ[ℚ, -3, 0, b]))
    (ω : ⋀[ℚ]^2 (HQ A 1)) : LinearMap.BilinForm ℚ (Fin 3 → ℍ[ℚ, -3, 0, b]) :=
  (typeIIIHomologyPairing ω).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap

/-- Inverse coordinates intertwine the actual homology action with left
quaternion multiplication. -/
theorem typeIII_model_inverse_action (b : ℚ)
    (θ : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A)
    (e : Dual ℚ (HQ A 1) ≃ₗ[ℚ] (Fin 3 → ℍ[ℚ, -3, 0, b]))
    (he : ∀ q x i, e (((abelianEnd0Action A (θ q)).unop).dualMap x) i = q * e x i)
    (q : ℍ[ℚ, -3, 0, b]) (x : Fin 3 → ℍ[ℚ, -3, 0, b]) :
    e.symm (q • x) = ((abelianEnd0Action A (θ q)).unop).dualMap (e.symm x) := by
  apply e.injective
  funext i
  rw [e.apply_symm_apply, he, e.apply_symm_apply]
  rfl

/-- The actual pairing in rank-three coordinates is quaternion invariant. -/
theorem typeIII_model_pairing_invariant (b : ℚ) (hb : b < 0)
    (θ : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A) (hP : p1_IsPolarization A pol)
    (e : Dual ℚ (HQ A 1) ≃ₗ[ℚ] (Fin 3 → ℍ[ℚ, -3, 0, b]))
    (he : ∀ q x i, e (((abelianEnd0Action A (θ q)).unop).dualMap x) i = q * e x i)
    (q : ℍ[ℚ, -3, 0, b]) (x y : Fin 3 → ℍ[ℚ, -3, 0, b]) :
    typeIIIModelPairing b e (polarizationVec (torusCohomology_cupProductOf A) pol) (q • x) y =
      typeIIIModelPairing b e (polarizationVec (torusCohomology_cupProductOf A) pol)
        x (star q • y) := by
  change (e.symm y) (contract _ (e.symm (q • x))) =
    (e.symm (star q • y)) (contract _ (e.symm x))
  rw [typeIII_model_inverse_action b θ e he, typeIII_model_inverse_action b θ e he]
  exact typeIII_actual_trace_invariance b hb θ hP q _ _

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_model_inverse_action
#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_model_pairing_invariant

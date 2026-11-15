import HodgeLean.Foundations.Program.G32Native.TypeIIIActualRosati

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

/-- The actual homology form is invariant under the full quaternion action
with canonical conjugation in the second argument. -/
theorem typeIII_actual_trace_invariance (b : ℚ) (hb : b < 0)
    (θ : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A) (hP : p1_IsPolarization A pol)
    (q : ℍ[ℚ, -3, 0, b]) (φ ψ : Dual ℚ (HQ A 1)) :
    ψ (contract (polarizationVec (torusCohomology_cupProductOf A) pol)
      (((abelianEnd0Action A (θ q)).unop).dualMap φ)) =
    (((abelianEnd0Action A (θ (star q))).unop).dualMap ψ)
      (contract (polarizationVec (torusCohomology_cupProductOf A) pol) φ) := by
  have ha := p1r_abelianEnd0Action_rosati (p1_isNondegenerate_of_isPositive_aux hP)
    (p1_adjoint_mem_range_aux A hP) (θ q)
  rw [typeIII_actual_rosati b hb θ hP q] at ha
  have h := LinearMap.congr_fun (p1l_contract_dualMap_adjoint
    (p1_isNondegenerate_of_isPositive_aux hP) (abelianEnd0Action A (θ q)).unop) φ
  rw [← ha] at h
  simpa only [LinearMap.comp_apply, LinearMap.dualMap_apply] using congrArg ψ h

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_actual_trace_invariance

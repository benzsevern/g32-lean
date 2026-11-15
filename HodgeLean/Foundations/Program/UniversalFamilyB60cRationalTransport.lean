import HodgeLean.Foundations.Program.UniversalFamilyB60cMarkedChart
import HodgeLean.Foundations.Program.UniversalFamilyB60cFibreMarking

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

/-- A rational polarization-bivector marking preserves the complex alternating forms. -/
theorem b60c_complex_polarization_isometry (P Q : g32t_Sixfold)
    (hP : g32t_IsMember P) (hQ : g32t_IsMember Q)
    (e : HQ P.X 1 ≃ₗ[ℚ] HQ Q.X 1)
    (he : exteriorPower.map 2 e.toLinearMap
      (polarizationVec (torusCohomology_cupProductOf P.X) P.pol) =
      polarizationVec (torusCohomology_cupProductOf Q.X) Q.pol)
    (x y : ℂ ⊗[ℚ] HQ P.X 1) :
    (polarizationForm (torusCohomology_cupProductOf Q.X) hQ.nondegenerate).baseChange ℂ
      ((LinearEquiv.baseChange ℚ ℂ _ _ e) x) ((LinearEquiv.baseChange ℚ ℂ _ _ e) y) =
      (polarizationForm (torusCohomology_cupProductOf P.X) hP.nondegenerate).baseChange ℂ x y := by
  letI := (torusCohomology_cupProductOf P.X).finite
  letI := (torusCohomology_cupProductOf Q.X).finite
  have hmap := b2a_isNondegenerate_map e hP.nondegenerate
  have hform (u v : HQ P.X 1) :
      polarizationForm (torusCohomology_cupProductOf Q.X) hQ.nondegenerate (e u) (e v) =
      polarizationForm (torusCohomology_cupProductOf P.X) hP.nondegenerate u v := by
    have h := b60b_dualForm_map_equiv e hP.nondegenerate hmap u v
    rw [b60b_dualForm_congr he hmap hQ.nondegenerate] at h
    exact h
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul c x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul d y =>
      simp only [LinearEquiv.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hform]

#print axioms b60c_complex_polarization_isometry

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenCyclePointIdealStabilizer

/-! # Underlying points determine complex-valued points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Complex-valued points over the fixed complex base are determined by their
underlying points, without a finite-type hypothesis on the target.
Source: Hartshorne, Algebraic Geometry, II.2, rational points and evaluation ideals. -/
theorem s2e_complex_point_eq_of_underlying_eq
    (X : Over (Spec ↧ℂ)) (x y : ComplexPoint X) (h : x.underlying = y.underlying) : x = y := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x.underlying ∈ (⊤ : X.left.Opens) from trivial)
  have hyU : y.underlying ∈ U := h ▸ hxU
  have hx := s2e_step1_point_preimage X x U hxU
  have hy := s2e_step1_point_preimage X y U hyU
  apply s2e_step1_point_ext_on_affine X U hU x y hx hy
  letI := s2e_step1_sectionAlgebra X U
  apply s2e_complex_evaluation_eq_of_ker_eq
  rw [s2e_pointEvaluation_kernel_primeIdealOf X U hU x hx,
    s2e_pointEvaluation_kernel_primeIdealOf X U hU y hy]
  exact congrArg (fun z : U => (hU.primeIdealOf z).asIdeal) (Subtype.ext h)

#print axioms s2e_complex_point_eq_of_underlying_eq
end HodgeLean.Foundations.Program

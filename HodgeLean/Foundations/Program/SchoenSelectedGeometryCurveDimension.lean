import HodgeLean.Foundations.Program.SchoenSelectedGeometryQuasiFiniteDimension
import HodgeLean.Foundations.Program.SchoenSelectedGeometryDimensionLower

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A nontrivial integral scheme quasi-finite over the projective line has dimension one.
Source: discreteness of quasi-finite fibres and the generic-point dimension bound. -/
theorem s0_dimension_one_of_quasiFinite_line_projection
    (X : Scheme.{0}) [IsIntegral X] [Nontrivial X]
    (q : X ⟶ ProjectiveSpace (Fin 2) (Spec ↧ℂ)) [LocallyQuasiFinite q] :
    TopologicalSpace.dim X = 1 := by
  have hu : topologicalKrullDim X ≤ 1 := by
    have h := s0_quasiFinite_krull_dimension_le q
    rwa [s0_complex_projective_krull_dimension 1] at h
  have he : topologicalKrullDim X = 1 := le_antisymm hu (s0_irreducible_krull_dimension_lower X)
  unfold TopologicalSpace.dim
  rw [he]
  simp

#print axioms s0_dimension_one_of_quasiFinite_line_projection
end HodgeLean.Foundations.Program

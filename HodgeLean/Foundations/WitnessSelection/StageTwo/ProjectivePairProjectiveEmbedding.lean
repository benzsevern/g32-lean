import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairProjectiveMatrix
import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairKernelContinuity
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective

/-! A compact matrix embedding of finite-dimensional complex projective space.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped LinearAlgebra.Projectivization
namespace HodgeLean.WitnessSelection.StageTwo

/-- The Hermitian matrix realization is a closed topological embedding of complex projective space.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_projectiveMatrix_isClosedEmbedding (n : ℕ) :
    Topology.IsClosedEmbedding
      (s2e_pair_projectiveMatrix (ι := Fin (n + 1))) := by
  have hc : Continuous (s2e_pair_projectiveMatrix (ι := Fin (n + 1))) := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact s2e_pair_projectiveKernel_continuous
  exact hc.isClosedEmbedding s2e_pair_projectiveMatrix_injective

end HodgeLean.WitnessSelection.StageTwo

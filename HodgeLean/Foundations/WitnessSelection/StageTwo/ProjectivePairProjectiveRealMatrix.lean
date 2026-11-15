import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairProjectiveEmbedding
import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairRealCoordinates

/-! Explicit real matrix coordinates for finite complex projective spaces.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped LinearAlgebra.Projectivization
namespace HodgeLean.WitnessSelection.StageTwo

/-- Record the normalized Hermitian matrix in explicit real and imaginary coordinates.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
def s2e_pair_projectiveRealMatrix (n : ℕ)
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) :
    EuclideanSpace ℝ (Fin (Fintype.card
      ((Fin (n + 1) × Fin (n + 1)) ⊕ (Fin (n + 1) × Fin (n + 1))))) :=
  s2e_pair_complexRealCoordinates
    (fun a : Fin (n + 1) × Fin (n + 1) => s2e_pair_projectiveMatrix p a.1 a.2)

/-- Explicit real matrix coordinates give a closed embedding of complex projective space.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_projectiveRealMatrix_isClosedEmbedding (n : ℕ) :
    Topology.IsClosedEmbedding (s2e_pair_projectiveRealMatrix n) := by
  have hc : Continuous (fun p : Projectivization ℂ (Fin (n + 1) → ℂ) =>
      fun a : Fin (n + 1) × Fin (n + 1) => s2e_pair_projectiveMatrix p a.1 a.2) := by
    apply continuous_pi
    intro a
    exact (continuous_apply a.2).comp ((continuous_apply a.1).comp
      (s2e_pair_projectiveMatrix_isClosedEmbedding n).continuous)
  have hcont : Continuous (s2e_pair_projectiveRealMatrix n) :=
    s2e_pair_complexRealCoordinates_continuous.comp hc
  apply hcont.isClosedEmbedding
  intro p q he
  have h := s2e_pair_complexRealCoordinates_injective he
  apply s2e_pair_projectiveMatrix_injective
  funext i j
  exact congrFun h (i, j)

end HodgeLean.WitnessSelection.StageTwo

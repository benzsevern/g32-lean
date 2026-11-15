import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicZeroHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveHomologyDimension

/-! # Ordinary homology above intrinsic complex dimension -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Ordinary rational homology of an integral projective complex scheme vanishes above twice its intrinsic complex dimension.
Source: Hatcher, Algebraic Topology, section 2.1, simplicial homology dimension; semialgebraic finite triangulation of projective complex schemes.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_homology_above_dimension
    (V : Over (Spec ↧ℂ)) [IsIntegral V.left] [IsProjective V.hom]
    (d : ℕ) (hdim : topologicalKrullDim V.left = (d : ℕ))
    (n : ℕ) (hn : 2 * d < n) : Subsingleton (Homology ℚ (a3b4_an V.hom) n) := by
  by_cases hd : d = 0
  · subst d
    exact properCycle_zero_dimensional_homology_vanishes V hdim n (by omega)
  · exact properCycle_projective_homology_dimension_vanishes V d hdim.le n hn

end HodgeLean.Foundations.QuotientDuality

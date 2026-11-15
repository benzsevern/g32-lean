import HodgeLean.Foundations.QuotientDuality.ProperCycleAcyclicCoverPieces
import HodgeLean.Foundations.QuotientDuality.ProperCycleZeroDimension

/-! # Actual positive-degree homology of zero-dimensional complex schemes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Every actual integral zero-dimensional finite-type complex scheme has zero ordinary rational homology in positive degree.
Source: Hilbert's Nullstellensatz; Hatcher, Algebraic Topology, section 2.1, contractibility of a singleton.
HC no distance; AV milestone no distance. -/
lemma properCycle_zero_dimensional_homology_vanishes
    (V : Over (Spec ↧ℂ)) [IsIntegral V.left] [LocallyOfFiniteType V.hom]
    (hdim : topologicalKrullDim V.left = (0 : ℕ))
    (n : ℕ) (hn : n ≠ 0) : Subsingleton (Homology ℚ (a3b4_an V.hom) n) := by
  have hd : TopologicalSpace.dim V.left = 0 := by
    unfold TopologicalSpace.dim
    rw [hdim]
    rfl
  letI : Subsingleton (a3b4_an V.hom) := properCycle_zero_dimension_complex_subsingleton V hd
  letI : Nonempty (a3b4_an V.hom) := properCycle_zero_dimension_complex_nonempty V hd
  exact properCycle_contractible_homology_subsingleton (a3b4_an V.hom) n hn

end HodgeLean.Foundations.QuotientDuality

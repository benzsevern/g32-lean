import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothGenericNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleFiniteDimensionPredecessor
import HodgeConjecture.Lemmas.Topology.Dimension.ClosedSubset

/-! # Actual smooth affine generic opens with intrinsically smaller boundaries -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- An original integral finite type complex scheme has an actual affine smooth generic open of its intrinsic dimension whose original closed boundary has dimension at most the intrinsic predecessor.
Source: properCycle_smooth_affine_generic_neighborhood; topologicalKrullDim_lt_of_isClosed_of_ne_univ; properCycle_dimension_le_pred_of_lt.
HC no distance; AV milestone no distance. -/
theorem properCycle_intrinsic_smooth_open_small_boundary
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (d : ℕ) (hdim : topologicalKrullDim X.left = (d : ℕ)) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ genericPoint X.left ∈ U ∧
      SmoothOfRelativeDimension d (ComplexPoint.openScheme X U).hom ∧
        topologicalKrullDim (U.compl : Set X.left) ≤ (d-1 : ℕ) := by
  have hd : TopologicalSpace.dim X.left = d := by
    unfold TopologicalSpace.dim
    rw [hdim]
    rfl
  obtain ⟨U, hU, hg, _, hs⟩ := properCycle_smooth_affine_generic_neighborhood X d hd ⊤ (by trivial)
  have hproper : (U.compl : Set X.left) ≠ Set.univ := by
    intro he
    have hgB : genericPoint X.left ∈ (U.compl : Set X.left) := by rw [he]; trivial
    exact hgB hg
  have hlt : topologicalKrullDim (U.compl : Set X.left) < (d : ℕ) :=
    topologicalKrullDim_lt_of_isClosed_of_ne_univ U.compl.isClosed hproper hdim.le
  exact ⟨U, hU, hg, hs, properCycle_dimension_le_pred_of_lt _ d hlt⟩

end HodgeLean.Foundations.QuotientDuality

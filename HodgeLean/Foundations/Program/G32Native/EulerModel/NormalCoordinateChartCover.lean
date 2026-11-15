import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPermutationBase
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalProjectiveChartTopology

/-! # Every actual projective kernel base point lies in a specified coordinate chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Some specified coordinate swap carries every actual projective base point into the original normalized affine chart. -/
theorem normalPermutationBase_chart_cover (k : ℕ)
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) :
    ∃ j : Fin (k + 1), normalPermutationBaseHomeomorph k (Equiv.swap 0 j) p ∈
      Set.range (normalProjectiveChart k) := by
  classical
  induction p using Projectivization.ind with
  | h v hv =>
    have hne : normalHomogeneousCoordinates k v ≠ 0 :=
      (normalHomogeneousCoordinates k).map_ne_zero_iff.mpr hv
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 1), normalHomogeneousCoordinates k v j ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hne
      funext j
      exact hn j
    refine ⟨j, ?_⟩
    rw [normalPermutationBaseHomeomorph_mk, normalProjectiveChart_range_mk]
    have hc : (normalCoordinatePermutation k (Equiv.swap 0 j) v).1 =
        normalHomogeneousCoordinates k v j := by
      simpa [normalHomogeneousCoordinates] using
        normalCoordinatePermutation_coordinate k (Equiv.swap 0 j) v 0
    rw [hc]
    exact hj

#print axioms normalPermutationBase_chart_cover
end HodgeLean.Foundations.Program.G32Native.EulerModel

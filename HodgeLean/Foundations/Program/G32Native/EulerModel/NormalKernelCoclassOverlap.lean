import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelChartAnalyticity
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionOverlap

/-! # Compatibility of the actual kernel atlas normal coclasses -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The two actual chart normal coclasses agree near every original zero vector in their overlap. -/
theorem normalCoordinateKernelCoclass_overlap (k : ℕ) (i j : Fin (k + 1))
    (v : ProjectiveNormalTotalSpace k) (hv : v.1.2 = 0)
    (hj : v ∈ (normalCoordinateKernelChart k j).source)
    (hi : v ∈ (normalCoordinateKernelChart k i).source) :
    ∃ (W : TopologicalSpace.Opens (ProjectiveNormalTotalSpace k))
      (hW : (W : Set (ProjectiveNormalTotalSpace k)) ⊆ (normalCoordinateKernelChart k j).source)
      (hW' : (W : Set (ProjectiveNormalTotalSpace k)) ⊆ (normalCoordinateKernelChart k i).source),
      v ∈ W ∧
      chartNormalProjectionCoclass (Fin k → ℂ) k (normalCoordinateKernelChart k j)
        {w | w.1.2 = 0} (normalCoordinateKernelChart_support k j) W hW =
      chartNormalProjectionCoclass (Fin k → ℂ) k (normalCoordinateKernelChart k i)
        {w | w.1.2 = 0} (normalCoordinateKernelChart_support k i) W hW' := by
  have hp (l : Fin (k + 1)) (hl : v ∈ (normalCoordinateKernelChart k l).source) :
      normalCoordinateKernelParam k l (normalCoordinateKernelChart k l v) = v := by
    rw [← normalCoordinateKernelChart_symm_apply]
    exact (normalCoordinateKernelChart k l).left_inv hl
  apply exists_open_chartNormalProjectionCoclass_eq k
    (normalCoordinateKernelChart k j) (normalCoordinateKernelChart k i)
    {w | w.1.2 = 0} (normalCoordinateKernelChart_support k j)
    (normalCoordinateKernelChart_support k i) v hj
    ((normalCoordinateKernelChart_support k j v hj).mp hv) hi
  · apply normalCoordinateKernelChart_transition_analyticAt k i j
    rw [hp j hj]
    exact hi
  · have h := normalCoordinateKernelChart_transition_analyticAt k j i
      (normalCoordinateKernelChart k i v) (by rw [hp i hi]; exact hj)
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_apply,
      (normalCoordinateKernelChart k j).left_inv hj] using h

#print axioms normalCoordinateKernelCoclass_overlap
end HodgeLean.Foundations.Program.G32Native.EulerModel

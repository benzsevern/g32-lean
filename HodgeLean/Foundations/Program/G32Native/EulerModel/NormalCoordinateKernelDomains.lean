import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalCoordinateChartCover
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelTotalChart

/-! # Actual open kernel domains over every specified projective coordinate -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The part of the original kernel total space over the specified coordinate open. -/
abbrev NormalCoordinateKernelDomain (k : ℕ) (j : Fin (k + 1)) :=
  {v : ProjectiveNormalTotalSpace k |
    normalPermutationBaseHomeomorph k (Equiv.swap 0 j) v.1.1 ∈
      Set.range (normalProjectiveChart k)}

/-- Every specified coordinate kernel domain is open in the original global total space. -/
theorem isOpen_normalCoordinateKernelDomain (k : ℕ) (j : Fin (k + 1)) :
    IsOpen {v : ProjectiveNormalTotalSpace k |
      normalPermutationBaseHomeomorph k (Equiv.swap 0 j) v.1.1 ∈
        Set.range (normalProjectiveChart k)} :=
  (isOpen_normalProjectiveChart_range k).preimage
    ((normalPermutationBaseHomeomorph k (Equiv.swap 0 j)).continuous.comp
      (continuous_fst.comp continuous_subtype_val))

#print axioms isOpen_normalCoordinateKernelDomain
/-- The specified coordinate kernel domains cover every vector of the original total space. -/
theorem normalCoordinateKernelDomain_cover (k : ℕ) :
    (⋃ j : Fin (k + 1), {v : ProjectiveNormalTotalSpace k |
      normalPermutationBaseHomeomorph k (Equiv.swap 0 j) v.1.1 ∈
        Set.range (normalProjectiveChart k)}) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  obtain ⟨j, hj⟩ := normalPermutationBase_chart_cover k v.1.1
  exact Set.mem_iUnion.mpr ⟨j, hj⟩

#print axioms normalCoordinateKernelDomain_cover
end HodgeLean.Foundations.Program.G32Native.EulerModel

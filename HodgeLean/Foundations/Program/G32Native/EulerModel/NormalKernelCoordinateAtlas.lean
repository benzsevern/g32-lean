import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalCoordinateKernelCharts
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # An explicit coordinate atlas on the original global kernel total space -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified product parameters in the original global kernel total space. -/
def normalCoordinateKernelParam (k : ℕ) (j : Fin (k + 1))
    (za : (Fin k → ℂ) × (Fin k → ℂ)) : ProjectiveNormalTotalSpace k :=
  ((normalCoordinateKernelChartHomeomorph k j).symm za).1

/-- Each specified kernel parameterization is an open embedding into the original total space. -/
theorem isOpenEmbedding_normalCoordinateKernelParam (k : ℕ) (j : Fin (k + 1)) :
    Topology.IsOpenEmbedding (normalCoordinateKernelParam k j) :=
  (isOpen_normalCoordinateKernelDomain k j).isOpenEmbedding_subtypeVal.comp
    (normalCoordinateKernelChartHomeomorph k j).symm.isOpenEmbedding

#print axioms normalCoordinateKernelParam
#print axioms isOpenEmbedding_normalCoordinateKernelParam
/-- The actual ambient kernel chart has the specified full product target. -/
def normalCoordinateKernelChart (k : ℕ) (j : Fin (k + 1)) :
    OpenPartialHomeomorph (ProjectiveNormalTotalSpace k)
      ((Fin k → ℂ) × (Fin k → ℂ)) :=
  ((isOpenEmbedding_normalCoordinateKernelParam k j).toOpenPartialHomeomorph
    (normalCoordinateKernelParam k j)).symm

#print axioms normalCoordinateKernelChart
/-- Each specified parameterization has exactly its original coordinate kernel domain as image. -/
theorem normalCoordinateKernelParam_range (k : ℕ) (j : Fin (k + 1)) :
    Set.range (normalCoordinateKernelParam k j) =
      {v : ProjectiveNormalTotalSpace k |
        normalPermutationBaseHomeomorph k (Equiv.swap 0 j) v.1.1 ∈
          Set.range (normalProjectiveChart k)} := by
  ext v
  constructor
  · rintro ⟨za, rfl⟩
    exact ((normalCoordinateKernelChartHomeomorph k j).symm za).2
  · intro hv
    refine ⟨normalCoordinateKernelChartHomeomorph k j ⟨v, hv⟩, ?_⟩
    exact congrArg Subtype.val
      ((normalCoordinateKernelChartHomeomorph k j).symm_apply_apply ⟨v, hv⟩)

#print axioms normalCoordinateKernelParam_range
/-- The actual ambient coordinate chart recovers every original product parameter exactly. -/
theorem normalCoordinateKernelChart_param (k : ℕ) (j : Fin (k + 1))
    (za : (Fin k → ℂ) × (Fin k → ℂ)) :
    normalCoordinateKernelChart k j (normalCoordinateKernelParam k j za) = za :=
  (isOpenEmbedding_normalCoordinateKernelParam k j).toOpenPartialHomeomorph_left_inv _

#print axioms normalCoordinateKernelChart_param
/-- The actual ambient chart source is exactly the image of its specified kernel parameterization. -/
theorem normalCoordinateKernelChart_source (k : ℕ) (j : Fin (k + 1)) :
    (normalCoordinateKernelChart k j).source = Set.range (normalCoordinateKernelParam k j) := by
  simp only [normalCoordinateKernelChart, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]

#print axioms normalCoordinateKernelChart_source
/-- Every vector of the original kernel total space lies in a specified ambient coordinate chart. -/
theorem normalCoordinateKernelChart_cover (k : ℕ) (v : ProjectiveNormalTotalSpace k) :
    ∃ j : Fin (k + 1), v ∈ (normalCoordinateKernelChart k j).source := by
  obtain ⟨j, hj⟩ := normalPermutationBase_chart_cover k v.1.1
  refine ⟨j, ?_⟩
  rw [normalCoordinateKernelChart_source, normalCoordinateKernelParam_range]
  exact hj

#print axioms normalCoordinateKernelChart_cover
/-- Every actual ambient coordinate chart flattens precisely the original zero-section support. -/
theorem normalCoordinateKernelChart_support (k : ℕ) (j : Fin (k + 1))
    (v : ProjectiveNormalTotalSpace k) (hv : v ∈ (normalCoordinateKernelChart k j).source) :
    v.1.2 = 0 ↔ (normalCoordinateKernelChart k j v).2 = 0 := by
  rw [normalCoordinateKernelChart_source] at hv
  obtain ⟨za, rfl⟩ := hv
  rw [normalCoordinateKernelChart_param]
  exact normalCoordinateKernelChart_vector_zero_iff k j za

#print axioms normalCoordinateKernelChart_support
end HodgeLean.Foundations.Program.G32Native.EulerModel

import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelCoordinateAtlas
import Mathlib.Geometry.Manifold.ChartedSpace

/-! # The explicit finite chart family on the original kernel total space -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual kernel total space as a charted space with exactly its specified coordinate charts. -/
def normalKernelChartedSpace (k : ℕ) :
    ChartedSpace ((Fin k → ℂ) × (Fin k → ℂ)) (ProjectiveNormalTotalSpace k) where
  atlas := Set.range (normalCoordinateKernelChart k)
  chartAt v := normalCoordinateKernelChart k
    (Classical.choose (normalCoordinateKernelChart_cover k v))
  mem_chart_source v := Classical.choose_spec (normalCoordinateKernelChart_cover k v)
  chart_mem_atlas v := ⟨Classical.choose (normalCoordinateKernelChart_cover k v), rfl⟩

#print axioms normalKernelChartedSpace
end HodgeLean.Foundations.Program.G32Native.EulerModel

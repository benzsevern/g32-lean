import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelChartedSpace
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelGlobalTopology

/-! # Local compactness of the original kernel total space -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The original kernel total space is locally compact in its specified topology. -/
theorem normalKernelTotalSpace_locallyCompact (k : ℕ) :
    LocallyCompactSpace (ProjectiveNormalTotalSpace k) := by
  letI : ChartedSpace ((Fin k → ℂ) × (Fin k → ℂ)) (ProjectiveNormalTotalSpace k) :=
    normalKernelChartedSpace k
  exact ChartedSpace.locallyCompactSpace ((Fin k → ℂ) × (Fin k → ℂ))
    (ProjectiveNormalTotalSpace k)

#print axioms normalKernelTotalSpace_locallyCompact
/-- The original global kernel total space is paracompact in the specified topology. -/
theorem normalKernelTotalSpace_paracompact (k : ℕ) :
    ParacompactSpace (ProjectiveNormalTotalSpace k) := by
  letI := normalKernelTotalSpace_t2Space k
  letI := normalKernelTotalSpace_secondCountable k
  letI := normalKernelTotalSpace_locallyCompact k
  infer_instance

#print axioms normalKernelTotalSpace_paracompact
end HodgeLean.Foundations.Program.G32Native.EulerModel

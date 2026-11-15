import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelCompactTopology

/-! # Hereditary paracompactness of the actual kernel total space -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Every original open subset of the actual kernel total space is paracompact. -/
theorem normalKernelTotalSpace_openParacompact (k : ℕ)
    (U : TopologicalSpace.Opens (ProjectiveNormalTotalSpace k)) : ParacompactSpace U := by
  letI := normalKernelTotalSpace_t2Space k
  letI := normalKernelTotalSpace_secondCountable k
  letI := normalKernelTotalSpace_locallyCompact k
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  infer_instance

#print axioms normalKernelTotalSpace_openParacompact
end HodgeLean.Foundations.Program.G32Native.EulerModel

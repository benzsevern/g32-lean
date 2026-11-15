import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalCoordinateKernelCharts

/-! # Global topology of the original projective evaluation-kernel total space -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The original kernel total space is Hausdorff in its specified subspace topology. -/
theorem normalKernelTotalSpace_t2Space (k : ℕ) : T2Space (ProjectiveNormalTotalSpace k) := by
  letI : T2Space (Projectivization ℂ (ℂ × (Fin k → ℂ))) :=
    (normalProjectiveSchemeHomeomorph k).isEmbedding.t2Space
  infer_instance

#print axioms normalKernelTotalSpace_t2Space
/-- The original total space is second countable because its specified finite coordinate cover has Euclidean product charts. -/
theorem normalKernelTotalSpace_secondCountable (k : ℕ) :
    SecondCountableTopology (ProjectiveNormalTotalSpace k) := by
  letI : ∀ j : Fin (k + 1), SecondCountableTopology (NormalCoordinateKernelDomain k j) :=
    fun j => (normalCoordinateKernelChartHomeomorph k j).isEmbedding.secondCountableTopology
  exact TopologicalSpace.secondCountableTopology_of_countable_cover
    (isOpen_normalCoordinateKernelDomain k) (normalCoordinateKernelDomain_cover k)

#print axioms normalKernelTotalSpace_secondCountable
end HodgeLean.Foundations.Program.G32Native.EulerModel

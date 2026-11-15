import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelTotalChart
import HodgeConjecture.Mathlib.Topology.Category.TopPair

/-! # The actual punctured kernel chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified product chart identifies the actual nonzero normal vectors as a topological pair. -/
def normalKernelTotalChartPairIso (k : ℕ) :
    TopPair.ofSubset (X := TopCat.of ((Fin k → ℂ) × (Fin k → ℂ)))
      {za | za.2 = 0}ᶜ ≅
    TopPair.ofSubset (X := TopCat.of (NormalKernelChartDomain k))
      {v | v.1.1.2 = 0}ᶜ :=
  TopPair.isoOfSubset (normalKernelTotalChartHomeomorph k)
    (fun za => not_congr (normalKernelTotalChart_vector_zero_iff k za))

#print axioms normalKernelTotalChartPairIso
end HodgeLean.Foundations.Program.G32Native.EulerModel

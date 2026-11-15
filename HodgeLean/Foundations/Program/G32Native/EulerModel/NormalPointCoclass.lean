import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalSignedAction
import HodgeLean.RealDefs.FundamentalClass.Chart

/-! # Signed normalization on the specified standard point coclass -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual normal section chart pulls the normalized point coclass back with coefficient `(-1)^k`. -/
theorem normal_section_normalizedPointCoclass (k : ℕ) :
    relativeCohomologyMap ℚ (2 * k) (normalChartPairMap k 1) (normalizedPointCoclass k) =
      (-1 : ℚ) ^ k • normalizedPointCoclass k := by
  exact normalChartPairMap_one_cohomology k (normalizedPointCoclass k)

#print axioms normal_section_normalizedPointCoclass
end HodgeLean.Foundations.Program.G32Native.EulerModel

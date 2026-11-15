import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateIdealGenerators

/-! # Regularity of every original coordinate hyperplane chart generator -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The specified original coordinate ratio is regular on its actual
chart section ring, including the chart where that ratio is one. -/
theorem paired_c3_coordinate_ideal_generator_regular (k : ℕ) (i j : Fin (k + 1)) :
    IsRegular ((paired_nativeHyperplaneChartEquiv k i).symm (ProjSpace.ratio ℂ k i j)) := by
  letI := paired_nativeAway_isDomain ℂ k i
  letI : IsDomain Γ(pairedC3Proj k, (paired_nativeHyperplaneChartOpen k i).1) :=
    (paired_nativeHyperplaneChartEquiv k i).isDomain_iff.mpr inferInstance
  apply isRegular_iff_ne_zero.mpr
  intro h
  apply paired_nativeRatio_ne_zero ℂ k i j
  have hh := congrArg (paired_nativeHyperplaneChartEquiv k i) h
  simpa only [RingEquiv.apply_symm_apply, map_zero] using hh

#print axioms paired_c3_coordinate_ideal_generator_regular
end HodgeLean.Foundations.Program.G32Native

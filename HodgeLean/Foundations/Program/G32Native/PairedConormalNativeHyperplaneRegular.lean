import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeHyperplaneGenerators

/-! # Regularity of the specified native hyperplane generators -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The specified native hyperplane chart generator is regular, including
the chart on which the generator is one. -/
theorem paired_nativeHyperplaneChart_regular (k : ℕ) (i : Fin (k + 1)) :
    IsRegular ((paired_nativeHyperplaneChartEquiv k i).symm (ProjSpace.ratio ℂ k i 0)) := by
  letI := paired_nativeAway_isDomain ℂ k i
  letI : IsDomain Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ),
      (paired_nativeHyperplaneChartOpen k i).1) :=
    (paired_nativeHyperplaneChartEquiv k i).isDomain_iff.mpr inferInstance
  apply isRegular_iff_ne_zero.mpr
  intro h
  apply paired_nativeRatio_ne_zero ℂ k i 0
  have hh := congrArg (paired_nativeHyperplaneChartEquiv k i) h
  simpa only [RingEquiv.apply_symm_apply, map_zero] using hh

end HodgeLean.Foundations.Program.G32Native

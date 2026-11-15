import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeHyperplaneFrames

/-! # Actual sections and coefficients of the native hyperplane ideal -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual ideal-module section determined by the original chart ratio. -/
def paired_nativeHyperplaneGeneratorSection (k : ℕ) (i : Fin (k + 1)) :
    Γ(Conormal.idealModule (paired_nativeHyperplaneIdeal k).subschemeι,
      (paired_nativeHyperplaneChartOpen k i).1) :=
  idealSection (paired_nativeHyperplaneIdeal k) (paired_nativeHyperplaneChartOpen k i)
    ((paired_nativeHyperplaneChartEquiv k i).symm (ProjSpace.ratio ℂ k i 0)) (by
      rw [paired_nativeHyperplaneChart_principal]
      exact Ideal.mem_span_singleton_self _)

/-- The actual ideal inclusion retains the chart generator with its original scale. -/
theorem paired_nativeHyperplaneGeneratorSection_inclusion (k : ℕ) (i : Fin (k + 1)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (paired_nativeHyperplaneIdeal k).subschemeι.toRingCatSheafHom)).val.app
        (Opposite.op (paired_nativeHyperplaneChartOpen k i).1) (paired_nativeHyperplaneGeneratorSection k i) =
      (paired_nativeHyperplaneChartEquiv k i).symm (ProjSpace.ratio ℂ k i 0) := by
  rw [← idealAffineSectionsEquiv_val]
  exact idealSection_coordinate _ _ _ _

end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateIdealGenerators
import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeHyperplaneRatios

/-! # Specified sections of every actual coordinate hyperplane ideal -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles

/-- The retained coordinate ratio as an actual section of the ideal kernel. -/
def pairedC3CoordinateIdealChartSection (k : ℕ) (i j : Fin (k + 1)) :
    Γ(Conormal.idealModule (pairedC3CoordinateHyperplaneIdeal k j).subschemeι,
      (paired_nativeHyperplaneChartOpen k i).1) :=
  idealSection (pairedC3CoordinateHyperplaneIdeal k j) (paired_nativeHyperplaneChartOpen k i)
    ((paired_nativeHyperplaneChartEquiv k i).symm (ProjSpace.ratio ℂ k i j)) (by
      rw [paired_c3_coordinate_ideal_principal]
      exact Ideal.mem_span_singleton_self _)

/-- Inclusion of the specified ideal section has the original ratio and scale. -/
theorem paired_c3_coordinate_ideal_chart_section_inclusion (k : ℕ) (i j : Fin (k + 1)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (pairedC3CoordinateHyperplaneIdeal k j).subschemeι.toRingCatSheafHom)).val.app
        (op (paired_nativeHyperplaneChartOpen k i).1) (pairedC3CoordinateIdealChartSection k i j) =
      (paired_nativeHyperplaneChartEquiv k i).symm (ProjSpace.ratio ℂ k i j) := by
  rw [← idealAffineSectionsEquiv_val]
  exact idealSection_coordinate _ _ _ _

/-- The same actual ideal section on the literal standard coordinate open. -/
def pairedC3CoordinateIdealStandardSection (k : ℕ) (i j : Fin (k + 1)) :
    Γ(Conormal.idealModule (pairedC3CoordinateHyperplaneIdeal k j).subschemeι,
      ProjSpace.standardOpen ℂ k i) :=
  (Conormal.idealModule (pairedC3CoordinateHyperplaneIdeal k j).subschemeι).presheaf.map
    (homOfLE (paired_nativeHyperplaneChartOpen_eq k i).ge).op
    (pairedC3CoordinateIdealChartSection k i j)

/-- The original ideal inclusion sends the standard section to the actual
homogeneous coordinate ratio. -/
theorem paired_c3_coordinate_ideal_standard_section_inclusion (k : ℕ) (i j : Fin (k + 1)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (pairedC3CoordinateHyperplaneIdeal k j).subschemeι.toRingCatSheafHom)).val.app
        (op (ProjSpace.standardOpen ℂ k i)) (pairedC3CoordinateIdealStandardSection k i j) =
      ProjSpace.coordinateRatioSection ℂ k i j := by
  unfold pairedC3CoordinateIdealStandardSection
  erw [PresheafOfModules.naturality_apply,
    paired_c3_coordinate_ideal_chart_section_inclusion,
    paired_nativeHyperplaneChartEquiv_symm]
  let X := pairedC3Proj k
  change X.presheaf.map (homOfLE (paired_nativeHyperplaneChartOpen_eq k i).ge).op
    (X.presheaf.map (homOfLE (paired_nativeHyperplaneChartOpen_eq k i).le).op
      (ProjSpace.coordinateRatioSection ℂ k i j)) = _
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  exact congrArg (fun f => f (ProjSpace.coordinateRatioSection ℂ k i j))
    (X.presheaf.map_id _)

#print axioms pairedC3CoordinateIdealChartSection
#print axioms paired_c3_coordinate_ideal_chart_section_inclusion
#print axioms pairedC3CoordinateIdealStandardSection
#print axioms paired_c3_coordinate_ideal_standard_section_inclusion
end HodgeLean.Foundations.Program.G32Native

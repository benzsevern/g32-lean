import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateHyperplaneIdeals
import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeHyperplaneGenerators

/-! # Actual chart generators of every coordinate hyperplane ideal -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual native coordinate ideal has the specified ratio as its
principal generator on every original affine chart image. -/
theorem paired_c3_coordinate_ideal_principal (k : ℕ) (i j : Fin (k + 1)) :
    (pairedC3CoordinateHyperplaneIdeal k j).ideal (paired_nativeHyperplaneChartOpen k i) =
      Ideal.span {(paired_nativeHyperplaneChartEquiv k i).symm (ProjSpace.ratio ℂ k i j)} := by
  let G := MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ
  have hc := paired_c3_coordinate_hyperplane_away k i j
  erw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    ← Ideal.map_comap_of_equiv
      ((Proj.awayι G (MvPolynomial.X i) (ProjSpace.X_mem_one ℂ k i) one_pos).appIso ⊤).commRingCatIsoToRingEquiv,
    Ideal.map_map] at hc
  change Ideal.map (paired_nativeHyperplaneChartEquiv k i).toRingHom
    ((pairedC3CoordinateHyperplaneIdeal k j).ideal (paired_nativeHyperplaneChartOpen k i)) = _ at hc
  have h := congrArg (Ideal.comap (paired_nativeHyperplaneChartEquiv k i).toRingHom) hc
  erw [Ideal.comap_map_of_bijective _ (paired_nativeHyperplaneChartEquiv k i).bijective] at h
  erw [← Ideal.map_comap_of_equiv (paired_nativeHyperplaneChartEquiv k i).symm,
    Ideal.map_span, Set.image_singleton] at h
  exact h

#print axioms paired_c3_coordinate_ideal_principal
end HodgeLean.Foundations.Program.G32Native

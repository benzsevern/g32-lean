import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeHyperplaneCharts
import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeRatioNonzero
import HodgeLean.Foundations.Curves.Picard.LineBundles.CartierFrames

/-! # Actual principal generators on native hyperplane chart images -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

variable (k : ℕ)
local notation "𝒢" => MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ

/-- The affine image of the specified native coordinate chart. -/
def paired_nativeHyperplaneChartOpen (i : Fin (k + 1)) : (Proj 𝒢).affineOpens :=
  ⟨Proj.awayι 𝒢 (MvPolynomial.X i) (ProjSpace.X_mem_one ℂ k i) one_pos ''ᵁ ⊤,
    (isAffineOpen_top _).image_of_isOpenImmersion _⟩

/-- The native chart image section ring retains the original away coordinate ring. -/
def paired_nativeHyperplaneChartEquiv (i : Fin (k + 1)) :
    Γ(Proj 𝒢, (paired_nativeHyperplaneChartOpen k i).1) ≃+*
      HomogeneousLocalization.Away 𝒢 (MvPolynomial.X i) :=
  ((Proj.awayι 𝒢 (MvPolynomial.X i) (ProjSpace.X_mem_one ℂ k i) one_pos).appIso ⊤).commRingCatIsoToRingEquiv.trans
      (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒢 (MvPolynomial.X i)))).commRingCatIsoToRingEquiv

/-- The original native coordinate ratio generates the actual hyperplane
ideal on its affine chart image. -/
theorem paired_nativeHyperplaneChart_principal (i : Fin (k + 1)) :
    (paired_nativeHyperplaneIdeal k).ideal (paired_nativeHyperplaneChartOpen k i) =
      Ideal.span {(paired_nativeHyperplaneChartEquiv k i).symm (ProjSpace.ratio ℂ k i 0)} := by
  have hc := paired_nativeHyperplaneIdeal_away k i
  erw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    ← Ideal.map_comap_of_equiv
      ((Proj.awayι 𝒢 (MvPolynomial.X i) (ProjSpace.X_mem_one ℂ k i) one_pos).appIso ⊤).commRingCatIsoToRingEquiv, Ideal.map_map] at hc
  change Ideal.map (paired_nativeHyperplaneChartEquiv k i).toRingHom
    ((paired_nativeHyperplaneIdeal k).ideal (paired_nativeHyperplaneChartOpen k i)) = _ at hc
  have h := congrArg (Ideal.comap (paired_nativeHyperplaneChartEquiv k i).toRingHom) hc
  erw [Ideal.comap_map_of_bijective _ (paired_nativeHyperplaneChartEquiv k i).bijective] at h
  erw [← Ideal.map_comap_of_equiv (paired_nativeHyperplaneChartEquiv k i).symm,
    Ideal.map_span, Set.image_singleton] at h
  exact h

end HodgeLean.Foundations.Program.G32Native

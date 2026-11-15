import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SliceBaseTopology
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ChartSliceSupport
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.EndpointSupports
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ReciprocalChartTopology

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Actual ratio charts on the point fibre determine its sphere coordinate and the opposite endpoint. -/
theorem affine_slice_base_support_homeomorph
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0)
    (X : Over (Spec ↧ℂ))
    (p : X ⟶ Over.mk (ComplexPoint.affineSpecStructureMap R))
    (j₁ : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v)) ⟶ X)
    (j₂ : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring v u)) ⟶ X)
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    (hj₁ : ∀ a, Point.map p (Point.map j₁ a) =
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) a)
    (hj₂ : ∀ a, Point.map p (Point.map j₂ a) =
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom v u) a)
    (hcover : ∀ x : X.left, (∃ a, j₁.left a = x) ∨ ∃ a, j₂.left a = x)
    (hintersection : ∀ y : Spec ↧(RegularPairChart.ring v u),
      (∃ a, j₁.left a = j₂.left y) ↔ RegularPairChart.ratio v u ∉ y.asIdeal)
    (D₁ D₂ : Set X.left)
    (hD₁a : j₁.left ⁻¹' D₁ = PrimeSpectrum.zeroLocus {RegularPairChart.ratio u v})
    (hD₁b : j₂.left ⁻¹' D₁ = ∅)
    (hD₂a : j₁.left ⁻¹' D₂ = ∅)
    (hD₂b : j₂.left ⁻¹' D₂ = PrimeSpectrum.zeroLocus {RegularPairChart.ratio v u})
    [T2Space {x : ComplexPoint X // Point.map p x = (ComplexPoint.affineSpecEquiv R).symm φ}]
    [CompactSpace {x : ComplexPoint X // Point.map p x = (ComplexPoint.affineSpecEquiv R).symm φ}] :
    ∃ e : {x : ComplexPoint X // Point.map p x = (ComplexPoint.affineSpecEquiv R).symm φ} ≃ₜ OnePoint ℂ,
      (∀ z : ℂ, e (affineChartSliceMap u v φ hu hv X p j₁ hj₁ z) = (z : OnePoint ℂ)) ∧
      e (affineChartSliceMap v u φ hv hu X p j₂ hj₂ 0) = ∞ ∧
      ∀ x, (x.val.left (IsLocalRing.closedPoint ℂ) ∈ D₁ ↔ e x = ((0 : ℂ) : OnePoint ℂ)) ∧
        (x.val.left (IsLocalRing.closedPoint ℂ) ∈ D₂ ↔ e x = ∞) := by
  obtain ⟨E, hfinite, hinfty⟩ := affine_slice_base_homeomorph u v φ hu hv X p
    j₁ j₂ hj₁ hj₂ hcover hintersection
  let a₁ := affineChartSliceMap u v φ hu hv X p j₁ hj₁
  let a₂ := affineChartSliceMap v u φ hv hu X p j₂ hj₂
  have h₁ := affine_slice_map_support_iff u v φ hu hv X p j₁ hj₁ D₁ hD₁a
  have h₄ := affine_slice_map_support_iff v u φ hv hu X p j₂ hj₂ D₂ hD₂b
  have h₂ (z : ℂ) : (a₂ z).val.left (IsLocalRing.closedPoint ℂ) ∉ D₁ := by
    intro hz
    change j₂.left (((affineChartPointFibreHomeomorph v u φ hv hu).symm z).val.left
      (IsLocalRing.closedPoint ℂ)) ∈ D₁ at hz
    change ((affineChartPointFibreHomeomorph v u φ hv hu).symm z).val.left
      (IsLocalRing.closedPoint ℂ) ∈ j₂.left ⁻¹' D₁ at hz
    rw [hD₁b] at hz
    exact hz
  have h₃ (z : ℂ) : (a₁ z).val.left (IsLocalRing.closedPoint ℂ) ∉ D₂ := by
    intro hz
    change j₁.left (((affineChartPointFibreHomeomorph u v φ hu hv).symm z).val.left
      (IsLocalRing.closedPoint ℂ)) ∈ D₂ at hz
    change ((affineChartPointFibreHomeomorph u v φ hu hv).symm z).val.left
      (IsLocalRing.closedPoint ℂ) ∈ j₁.left ⁻¹' D₂ at hz
    rw [hD₂a] at hz
    exact hz
  refine ⟨E, hfinite, hinfty, ?_⟩
  exact reciprocal_endpoint_supports a₁ a₂
    {x | x.val.left (IsLocalRing.closedPoint ℂ) ∈ D₁}
    {x | x.val.left (IsLocalRing.closedPoint ℂ) ∈ D₂}
    (affine_slice_charts_cover u v φ hu hv X p j₁ j₂ hj₁ hj₂ hcover)
    h₁ h₂ h₃ h₄ E.toEquiv (hfinite 0) hinfty

end AlgebraicGeometry.RamifiedNormalization.StageFour

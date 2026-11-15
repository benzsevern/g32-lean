import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SliceChartCover
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
theorem affine_slice_base_homeomorph
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
    [T2Space {x : ComplexPoint X // Point.map p x = (ComplexPoint.affineSpecEquiv R).symm φ}]
    [CompactSpace {x : ComplexPoint X // Point.map p x = (ComplexPoint.affineSpecEquiv R).symm φ}] :
    ∃ e : {x : ComplexPoint X // Point.map p x = (ComplexPoint.affineSpecEquiv R).symm φ} ≃ₜ OnePoint ℂ,
      (∀ z : ℂ, e (affineChartSliceMap u v φ hu hv X p j₁ hj₁ z) = (z : OnePoint ℂ)) ∧
      e (affineChartSliceMap v u φ hv hu X p j₂ hj₂ 0) = ∞ := by
  let a₁ := affineChartSliceMap u v φ hu hv X p j₁ hj₁
  let a₂ := affineChartSliceMap v u φ hv hu X p j₂ hj₂
  have ha₁ := isOpenEmbedding_affineChartSliceMap u v φ hu hv X p j₁ hj₁
  have hover (z : ℂ) : a₂ z ∈ Set.range a₁ ↔ z ≠ 0 :=
    affine_slice_chart_overlap u v φ hu hv X p j₁ j₂ hj₁ hj₂ hintersection z
  have hmiss : a₂ 0 ∉ Set.range a₁ := fun h => (hover 0).mp h rfl
  have hrange : Set.range a₁ = {a₂ 0}ᶜ := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩ hx
      exact hmiss ⟨z, hx⟩
    · intro hx
      rcases affine_slice_charts_cover u v φ hu hv X p j₁ j₂ hj₁ hj₂ hcover x with
        ⟨z, hz⟩ | ⟨z, hz⟩
      · exact ⟨z, hz⟩
      · have hz0 : z ≠ 0 := by
          intro hz0
          apply hx
          change x = a₂ 0
          rw [← hz, hz0]
        rw [← hz]
        exact (hover z).mpr hz0
  let H := OnePoint.equivOfIsEmbeddingOfRangeEq (a₂ 0) a₁ ha₁.isEmbedding hrange
  have hfinite (z : ℂ) : H (z : OnePoint ℂ) = a₁ z :=
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe _ _ _ _ z
  have hinfty : H ∞ = a₂ 0 :=
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty _ _ _ _
  refine ⟨H.symm, ?_, ?_⟩
  · intro z
    change H.symm (a₁ z) = (z : OnePoint ℂ)
    rw [← hfinite z, H.symm_apply_apply]
  · change H.symm (a₂ 0) = ∞
    rw [← hinfty, H.symm_apply_apply]

end AlgebraicGeometry.RamifiedNormalization.StageFour

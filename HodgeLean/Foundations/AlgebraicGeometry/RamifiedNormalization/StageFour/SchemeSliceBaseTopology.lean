import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SliceBaseTopology
import HodgeLean.Foundations.Program.SchoenTowerFibreTopology

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual scheme fibre product retains the assembled sphere coordinate of its ratio charts. -/
theorem affine_slice_scheme_base_homeomorph
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
    letI : IsSeparated (Over.mk (ComplexPoint.affineSpecStructureMap R)).hom := by
      change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
      infer_instance
    let Hf := HodgeLean.Foundations.Program.s2v_separatedPointFibreHomeomorph p
      ((ComplexPoint.affineSpecEquiv R).symm φ)
    ∃ e : ComplexPoint (CategoryTheory.Limits.pullback p
        ((ComplexPoint.affineSpecEquiv R).symm φ)) ≃ₜ OnePoint ℂ,
      (∀ z : ℂ, e (Hf.symm (affineChartSliceMap u v φ hu hv X p j₁ hj₁ z)) =
        (z : OnePoint ℂ)) ∧
      e (Hf.symm (affineChartSliceMap v u φ hv hu X p j₂ hj₂ 0)) = ∞ := by
  letI : IsSeparated (Over.mk (ComplexPoint.affineSpecStructureMap R)).hom := by
    change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
    infer_instance
  let Hf := HodgeLean.Foundations.Program.s2v_separatedPointFibreHomeomorph p
    ((ComplexPoint.affineSpecEquiv R).symm φ)
  obtain ⟨e, he, hinfty⟩ := affine_slice_base_homeomorph u v φ hu hv X p j₁ j₂
    hj₁ hj₂ hcover hintersection
  refine ⟨Hf.trans e, ?_, ?_⟩
  · intro z
    change e (Hf (Hf.symm (affineChartSliceMap u v φ hu hv X p j₁ hj₁ z))) = _
    rw [Hf.apply_symm_apply]
    exact he z
  · change e (Hf (Hf.symm (affineChartSliceMap v u φ hv hu X p j₂ hj₂ 0))) = _
    rw [Hf.apply_symm_apply]
    exact hinfty

end AlgebraicGeometry.RamifiedNormalization.StageFour

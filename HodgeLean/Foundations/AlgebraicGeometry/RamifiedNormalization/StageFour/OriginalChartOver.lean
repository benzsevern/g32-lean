import HodgeLean.Foundations.Program.SchoenCycleU1AffineChartNaturality
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.PointChartLifts

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The original affine coefficient square constructs the actual ratio chart over the complex base and lifts the specified centre point. -/
theorem original_chart_over
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (U : B.left.affineOpens)
    (u v : Γ(B.left, U))
    (j : Spec ↧(RegularPairChart.ring u v) ⟶ X.left)
    (hj : j ≫ p.left = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v)) ≫ U.2.fromSpec)
    (x : ComplexPoint B) (hx : x.left (IsLocalRing.closedPoint ℂ) ∈ U.1) :
    letI := s2e_step1_sectionAlgebra B U.1
    ∃ (c : Over.mk (ComplexPoint.affineSpecStructureMap Γ(B.left, U)) ⟶ B)
      (jO : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v)) ⟶ X)
      (φ : Γ(B.left, U) →ₐ[ℂ] ℂ),
      c.left = U.2.fromSpec ∧ IsOpenImmersion c.left ∧ jO.left = j ∧
      jO ≫ p = Over.homMk (Spec.map (CommRingCat.ofHom (regularPairCoefficientAlgHom u v).toRingHom))
        (ComplexPoint.specMap_comp_affineSpecStructureMap (regularPairCoefficientAlgHom u v)) ≫ c ∧
      Point.map c ((ComplexPoint.affineSpecEquiv Γ(B.left, U)).symm φ) = x := by
  letI := s2e_step1_sectionAlgebra B U.1
  let c := s2e_u1_fromSpecOver B U.1 U.2
  have hc : c.left = U.2.fromSpec := rfl
  haveI : IsOpenImmersion c.left := by rw [hc]; infer_instance
  let jO : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v)) ⟶ X :=
    Over.homMk j (by
      rw [← p.w, ← Category.assoc, hj, Category.assoc]
      change Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v)) ≫
        (c.left ≫ B.hom) = _
      rw [c.w]
      exact ComplexPoint.specMap_comp_affineSpecStructureMap (regularPairCoefficientAlgHom u v))
  have hpoint : x.left (IsLocalRing.closedPoint ℂ) ∈ Set.range c.left := by
    change x.left (IsLocalRing.closedPoint ℂ) ∈ Set.range U.2.fromSpec
    exact U.2.range_fromSpec.symm ▸ hx
  obtain ⟨xR, hxR⟩ := complex_point_lifts_open_chart c x hpoint
  refine ⟨c, jO, ComplexPoint.affineSpecEquiv Γ(B.left, U) xR, hc, inferInstance, rfl, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact hj
  · simpa only [Equiv.symm_apply_apply] using hxR

end AlgebraicGeometry.RamifiedNormalization.StageFour

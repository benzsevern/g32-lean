import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProjectiveLineChart

/-! # Projective chart maps under actual coefficient restriction -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- Restricting coefficients and the chart parameter commutes with the
actual projective-line chart morphism. No pointwise comparison is needed. -/
theorem pairedC3_projective_chart_restriction
    {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (i : Fin 2) (t : A) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (projectiveLineChart i t).left =
      (projectiveLineChart i (f t)).left := by
  have hf : f.toRingHom.comp (algebraMap ℂ A) = algebraMap ℂ B := by
    ext r
    exact f.commutes r
  have hs : Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      ComplexPoint.affineSpecStructureMap A = ComplexPoint.affineSpecStructureMap B := by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ B))
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hf)
  have hc : f.toRingHom.comp (projectiveLineChartCoordinateHom i t) =
      projectiveLineChartCoordinateHom i (f t) := by
    dsimp only [projectiveLineChartCoordinateHom]
    rw [← RingHom.comp_assoc, MvPolynomial.comp_eval₂Hom, hf]
    rfl
  have hcat : CommRingCat.ofHom (projectiveLineChartCoordinateHom i t) ≫
      CommRingCat.ofHom f.toRingHom =
        CommRingCat.ofHom (projectiveLineChartCoordinateHom i (f t)) :=
    CommRingCat.hom_ext hc
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ pullback.lift _ _ _ =
    pullback.lift _ _ _
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.lift_fst] using hs
  · simp only [Category.assoc, pullback.lift_snd]
    rw [← Spec.map_comp_assoc, hcat]

#print axioms pairedC3_projective_chart_restriction
end HodgeLean.Foundations.Program.G32Native

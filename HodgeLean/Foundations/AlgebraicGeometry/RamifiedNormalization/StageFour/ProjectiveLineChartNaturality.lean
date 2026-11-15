import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProjectiveLineChart

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Restriction of the chart parameter along a complex algebra map retains the actual projective-line morphism. -/
theorem projectiveLineChart_naturality
    {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (i : Fin 2) (t : A) :
    (Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap f) :
        Over.mk (ComplexPoint.affineSpecStructureMap B) ⟶
          Over.mk (ComplexPoint.affineSpecStructureMap A)) ≫ projectiveLineChart i t =
      projectiveLineChart i (f t) := by
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        ((projectiveLineChart i t).left ≫ Limits.pullback.fst _ _) =
      (projectiveLineChart i (f t)).left ≫ Limits.pullback.fst _ _
    dsimp only [projectiveLineChart, Over.homMk, CostructuredArrow.homMk, Over.Hom.left]
    rw [Limits.pullback.lift_fst, Limits.pullback.lift_fst]
    exact ComplexPoint.specMap_comp_affineSpecStructureMap f
  · change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        ((projectiveLineChart i t).left ≫ Limits.pullback.snd _ _) =
      (projectiveLineChart i (f t)).left ≫ Limits.pullback.snd _ _
    dsimp only [projectiveLineChart, Over.homMk, CostructuredArrow.homMk, Over.Hom.left]
    rw [Limits.pullback.lift_snd, Limits.pullback.lift_snd]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 1
    congr 1
    apply CommRingCat.hom_ext
    apply s2e_u1_projective_chart_ringHom_ext i
    intro j
    change f (projectiveLineChartCoordinateHom i t (chartCoordinate i j)) =
      projectiveLineChartCoordinateHom i (f t) (chartCoordinate i j)
    rw [projectiveLineChartCoordinateHom_coordinate, projectiveLineChartCoordinateHom_coordinate]
    split <;> simp only [map_one]

end AlgebraicGeometry.RamifiedNormalization.StageFour

import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProjectiveLineChart

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual standard chart morphism has the homogeneous coordinates of its ring-valued evaluation. -/
theorem projectiveLineChart_point
    {A : Type} [CommRing A] [Algebra ℂ A] (i : Fin 2) (t : A)
    (y : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap A))) :
    let ψ := (ComplexPoint.affineSpecEquiv A y).toRingHom.comp (projectiveLineChartCoordinateHom i t)
    Point.map (projectiveLineChart i t) y =
      vectorToComplexPoint (vectorOfAwayRingHom i ψ) (vectorOfAwayRingHom_ne_zero i ψ) := by
  let ψ := (ComplexPoint.affineSpecEquiv A y).toRingHom.comp (projectiveLineChartCoordinateHom i t)
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · exact (Over.w (Point.map (projectiveLineChart i t) y)).trans
      (Over.w (vectorToComplexPoint (vectorOfAwayRingHom i ψ) (vectorOfAwayRingHom_ne_zero i ψ))).symm
  · change y.left ≫ ((projectiveLineChart i t).left ≫ Limits.pullback.snd _ _) =
      vectorToProjectiveSpace (vectorOfAwayRingHom i ψ) (vectorOfAwayRingHom_ne_zero i ψ) ≫
        Limits.pullback.snd _ _
    rw [vectorToProjectiveSpace_toProj,
      chartIntegralProj_eq_chartIntegralProjAt _ _ i (by simp)]
    have hy : Spec.map (CommRingCat.ofHom (ComplexPoint.affineSpecEquiv A y).toRingHom) = y.left :=
      Spec.map_preimage y.left
    rw [← hy]
    change Spec.map (CommRingCat.ofHom (ComplexPoint.affineSpecEquiv A y).toRingHom) ≫
      ((Limits.pullback.lift (ComplexPoint.affineSpecStructureMap A)
        (Spec.map (CommRingCat.ofHom (projectiveLineChartCoordinateHom i t)) ≫
          Proj.awayι (UniversalGrading.{0} 1) (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X _ _) zero_lt_one) (Subsingleton.elim _ _)) ≫
          Limits.pullback.snd _ _) = chartIntegralProjAt (vectorOfAwayRingHom i ψ) i _
    dsimp only [chartIntegralProjAt]
    rw [Limits.pullback.lift_snd, ← Category.assoc, ← Spec.map_comp]
    have he : CommRingCat.ofHom (projectiveLineChartCoordinateHom i t) ≫
        CommRingCat.ofHom (ComplexPoint.affineSpecEquiv A y).toRingHom =
      CommRingCat.ofHom (awayCoordinateEvaluation (vectorOfAwayRingHom i ψ) i (by simp)) := by
      apply CommRingCat.hom_ext
      change ψ = awayCoordinateEvaluation (vectorOfAwayRingHom i ψ) i (by simp)
      exact (awayCoordinateEvaluation_vectorOfAwayRingHom i ψ).symm
    exact congrArg (fun q => Spec.map q ≫ Proj.awayι (UniversalGrading.{0} 1)
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ _) zero_lt_one) he

/-- In the finite standard chart, the actual line coordinate is the original parameter evaluation. -/
theorem projectiveLineChart_finite_coordinate
    {A : Type} [CommRing A] [Algebra ℂ A] (t : A)
    (y : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap A))) :
    lineCoordinate (Point.map (projectiveLineChart 1 t) y) =
      ((ComplexPoint.affineSpecEquiv A y t : ℂ) : OnePoint ℂ) := by
  have he : Point.map (projectiveLineChart 1 t) y =
      lineCoordinate.symm ((ComplexPoint.affineSpecEquiv A y t : ℂ) : OnePoint ℂ) := by
    change Point.map (projectiveLineChart 1 t) y =
      vectorToComplexPoint (![ComplexPoint.affineSpecEquiv A y t, 1] : CoordinateSpace 1) (by simp)
    rw [projectiveLineChart_point]
    congr 1
    funext j
    fin_cases j <;> simp [vectorOfAwayRingHom_apply, RingHom.comp_apply,
      projectiveLineChartCoordinateHom_coordinate]
  rw [he, lineCoordinate.apply_symm_apply]

end AlgebraicGeometry.RamifiedNormalization.StageFour

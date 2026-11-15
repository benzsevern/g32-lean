import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProjectiveLineChartPoints

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Reciprocal parameter evaluations define the same actual projective-line point in the two standard charts. -/
theorem projectiveLineChart_reciprocal_points
    {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (t : A) (s : B)
    (x : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap A)))
    (y : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap B)))
    (h : ComplexPoint.affineSpecEquiv A x t * ComplexPoint.affineSpecEquiv B y s = 1) :
    Point.map (projectiveLineChart 1 t) x = Point.map (projectiveLineChart 0 s) y := by
  let a := ComplexPoint.affineSpecEquiv A x t
  let b := ComplexPoint.affineSpecEquiv B y s
  let ψ₁ := (ComplexPoint.affineSpecEquiv A x).toRingHom.comp (projectiveLineChartCoordinateHom 1 t)
  let ψ₀ := (ComplexPoint.affineSpecEquiv B y).toRingHom.comp (projectiveLineChartCoordinateHom 0 s)
  let v₁ := vectorOfAwayRingHom 1 ψ₁
  let v₀ := vectorOfAwayRingHom 0 ψ₀
  have hv₁ (j : Fin 2) : v₁ j = if j = 1 then 1 else a := by
    change (ComplexPoint.affineSpecEquiv A x) (projectiveLineChartCoordinateHom 1 t (chartCoordinate 1 j)) = _
    rw [projectiveLineChartCoordinateHom_coordinate]
    split
    · exact map_one _
    · rfl
  have hv₀ (j : Fin 2) : v₀ j = if j = 0 then 1 else b := by
    change (ComplexPoint.affineSpecEquiv B y) (projectiveLineChartCoordinateHom 0 s (chartCoordinate 0 j)) = _
    rw [projectiveLineChartCoordinateHom_coordinate]
    split
    · exact map_one _
    · rfl
  have ha : a ≠ 0 := by
    intro ha
    have he : a * b = 1 := h
    rw [ha, zero_mul] at he
    exact zero_ne_one he
  have hscale : v₁ = a • v₀ := by
    funext j
    fin_cases j <;> simp [hv₁, hv₀, Pi.smul_apply, smul_eq_mul, show a * b = 1 from h]
  rw [projectiveLineChart_point, projectiveLineChart_point]
  change vectorToComplexPoint v₁ (vectorOfAwayRingHom_ne_zero 1 ψ₁) =
    vectorToComplexPoint v₀ (vectorOfAwayRingHom_ne_zero 0 ψ₀)
  simpa only [← hscale] using vectorToComplexPoint_smul v₀
    (vectorOfAwayRingHom_ne_zero 0 ψ₀) a ha

end AlgebraicGeometry.RamifiedNormalization.StageFour

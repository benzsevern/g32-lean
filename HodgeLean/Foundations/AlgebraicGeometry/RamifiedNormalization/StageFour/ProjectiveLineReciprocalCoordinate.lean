import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProjectiveLineReciprocalPoints

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry.ComplexProjectiveSpace
open scoped OnePoint
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual reciprocal chart takes its zero parameter to infinity and all other parameters to their finite inverses. -/
theorem projectiveLineChart_reciprocal_coordinate
    {A : Type} [CommRing A] [Algebra ℂ A] (s : A)
    (y : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap A))) :
    lineCoordinate (Point.map (projectiveLineChart 0 s) y) =
      if ComplexPoint.affineSpecEquiv A y s = 0 then ∞ else
        ((ComplexPoint.affineSpecEquiv A y s)⁻¹ : ℂ) := by
  let b := ComplexPoint.affineSpecEquiv A y s
  by_cases hb : b = 0
  · rw [if_pos hb]
    have he : Point.map (projectiveLineChart 0 s) y =
        lineCoordinate.symm (∞ : OnePoint ℂ) := by
      change Point.map (projectiveLineChart 0 s) y =
        vectorToComplexPoint (![1, 0] : CoordinateSpace 1) (by simp)
      rw [projectiveLineChart_point]
      congr 1
      funext j
      fin_cases j <;> simp [vectorOfAwayRingHom_apply, RingHom.comp_apply,
        projectiveLineChartCoordinateHom_coordinate, show ComplexPoint.affineSpecEquiv A y s = 0 from hb]
    rw [he, lineCoordinate.apply_symm_apply]
  · rw [if_neg hb]
    let x := (ComplexPoint.affineSpecEquiv ℂ).symm (AlgHom.id ℂ ℂ)
    have hx : ComplexPoint.affineSpecEquiv ℂ x b⁻¹ = b⁻¹ := by
      change ComplexPoint.affineSpecEquiv ℂ ((ComplexPoint.affineSpecEquiv ℂ).symm _) _ = _
      rw [Equiv.apply_symm_apply]
      rfl
    have he := projectiveLineChart_reciprocal_points b⁻¹ s x y (by rw [hx]; exact inv_mul_cancel₀ hb)
    rw [← he, projectiveLineChart_finite_coordinate, hx]

end AlgebraicGeometry.RamifiedNormalization.StageFour

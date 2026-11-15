import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveChartAlgebra

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The standard projective-line chart evaluation with its other coordinate equal to the specified ring element. -/
def projectiveLineChartCoordinateHom
    {A : Type} [CommRing A] [Algebra ℂ A] (i : Fin 2) (t : A) :
    HomogeneousLocalization.Away (UniversalGrading.{0} 1)
      (MvPolynomial.X i : UniversalRing.{0} 1) →+* A :=
  (MvPolynomial.eval₂Hom (algebraMap ℂ A) (fun _ : Fin 2 => t)).comp (chartAwayPolynomialHom i)

/-- The standard chart retains its unit homogeneous coordinate and the specified other coordinate. -/
theorem projectiveLineChartCoordinateHom_coordinate
    {A : Type} [CommRing A] [Algebra ℂ A] (i j : Fin 2) (t : A) :
    projectiveLineChartCoordinateHom i t (chartCoordinate i j) = if j = i then 1 else t := by
  simp only [projectiveLineChartCoordinateHom, RingHom.comp_apply,
    chartAwayPolynomialHom_chartCoordinate]
  by_cases h : j = i
  · simp only [if_pos h, map_one]
  · simp only [if_neg h, MvPolynomial.eval₂Hom_X']

end AlgebraicGeometry.RamifiedNormalization.StageFour

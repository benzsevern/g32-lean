import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProjectiveLineChartAlgebra
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A ring-valued chart parameter gives a morphism into the actual projective line over the complex base. -/
def projectiveLineChart
    {A : Type} [CommRing A] [Algebra ℂ A] (i : Fin 2) (t : A) :
    Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ projectiveLine :=
  Over.homMk
    (Limits.pullback.lift
      (ComplexPoint.affineSpecStructureMap A)
      (Spec.map (CommRingCat.ofHom (projectiveLineChartCoordinateHom i t)) ≫
        Proj.awayι (UniversalGrading.{0} 1) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X _ _) zero_lt_one)
      (Subsingleton.elim _ _)) (by exact Limits.pullback.lift_fst _ _ _)

end AlgebraicGeometry.RamifiedNormalization.StageFour

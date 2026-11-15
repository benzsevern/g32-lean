import HodgeLean.Foundations.Program.G32Native.BlowupCoordinateNormalization
import HodgeLean.Foundations.Program.SchoenTowerN2bHomogeneousEvaluation

/-! Projective coordinate maps on individual blow-up charts. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The map to fixed projective space given by the ratios of a finite list of ideal generators. -/
def g32l4_blowUp_chart_projectiveMap {R : Type} [CommRing R]
    (I : Ideal R) (m : ℕ) (g : Fin (m + 1) → I) (p : Fin (m + 1)) :
    Spec (.of (affineBlowUpAlgebra I (g p))) ⟶
      Proj (homogeneousSubmodule (Fin (m + 1)) (ULift.{0} ℤ)) :=
  Proj.fromOfGlobalSections _
    (eval₂Hom ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
      (fun k => g32l4_blowUp_coordinate I (g p) (g k)))
    (n2b_polynomial_evaluation_irrelevant _ _ p (g32l4_blowUp_coordinate_self I (g p)))

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.G32Native.BlowupProjectiveClosedBase
import HodgeLean.Foundations.Program.G32Native.PolynomialProjBlowupProjective
import HodgeLean.Foundations.Program.SchoenProjectivePolynomialEmbedding

/-! Native finite projective presentations for blow-ups over a projective complex base. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The blow-up over a projective complex base has a finite projective presentation. -/
theorem g32l4_native_blowUp_projective
    (B : Over (Spec ↧ℂ)) [IsProjective B.hom] (I : B.left.IdealSheafData) :
    IsProjective (I.blowUpπ ≫ B.hom) := by
  obtain ⟨n, j, hj, hs⟩ := s2_projective_polynomialEmbedding B.hom
  letI : IsClosedImmersion j := hj
  have hcoeff : CommRingCat.ofHom (ProjSpace.grad0Equiv ℂ n).toRingHom =
      (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) ℂ).symm.toCommRingCatIso.hom := by
    ext r
    rfl
  have hjbase : j ≫ ProjSpace.π ℂ n = B.hom := by
    simpa only [ProjSpace.π, hcoeff, Category.assoc] using hs
  letI : IsProjective ((I.map j).blowUpπ ≫ ProjSpace.π ℂ n) :=
    g32l4_polynomialProj_blowUp_projective n (I.map j)
  exact g32l4_blowUp_projective_of_closed_base j B.hom (ProjSpace.π ℂ n) hjbase I

end HodgeLean.Foundations.Program

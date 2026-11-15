import HodgeLean.Foundations.Program.SchoenPolynomialProjectiveSpace
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.Basic

/-! Native projective presentations of polynomial projective space. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coefficient morphism of polynomial projective space has its native projective presentation. -/
theorem g32l4_polynomialProj_isProjective (R : Type) [CommRing R] (n : ℕ) :
    IsProjective (ProjSpace.π R n) := by
  let e := s2_polynomialProjectiveSpaceIso R (Fin (n + 1))
  have hcoeff : CommRingCat.ofHom (ProjSpace.grad0Equiv R n).toRingHom =
      (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) R).symm.toCommRingCatIso.hom := by
    ext r
    rfl
  have hπ : e.hom ≫ ProjectiveSpace.toBase (Fin (n + 1)) (Spec (.of R)) =
      ProjSpace.π R n := by
    simpa only [ProjSpace.π, hcoeff] using
      s2_polynomialProjectiveSpaceIso_toBase R (Fin (n + 1))
  exact ⟨⟨⟨n, e.hom, hπ⟩⟩⟩

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenPolynomialProjectiveSpace

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A projective scheme over a coefficient spectrum embeds in the actual polynomial Proj over that ring. -/
theorem s2_projective_polynomialEmbedding {R : Type} [CommRing R]
    {X : Scheme.{0}} (s : X ⟶ Spec (.of R)) [IsProjective s] :
    ∃ (n : ℕ) (j : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R)),
      IsClosedImmersion j ∧
      j ≫ Proj.toSpecZero (homogeneousSubmodule (Fin (n + 1)) R) ≫
        Spec.map (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) R).symm.toCommRingCatIso.hom = s := by
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := s)
  haveI := P.isClosedImmersion
  let e := s2_polynomialProjectiveSpaceIso R (Fin (P.ambientDimension + 1))
  refine ⟨P.ambientDimension, P.immersion ≫ e.inv, inferInstance, ?_⟩
  rw [Category.assoc, ← s2_polynomialProjectiveSpaceIso_toBase R]
  change (P.immersion ≫ e.inv) ≫ e.hom ≫ _ = s
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact P.immersion_toBase

end HodgeLean.Foundations.Program

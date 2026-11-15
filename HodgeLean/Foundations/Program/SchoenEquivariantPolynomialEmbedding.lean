import HodgeLean.Foundations.Program.SchoenPolynomialSegreEmbedding
import HodgeLean.Foundations.Program.SchoenOrbitProductEmbedding

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every finite action on a projective complex scheme has an actual equivariant closed embedding in polynomial Proj over the complex field. -/
theorem s2_projective_equivariantPolynomialEmbedding (X : Over (Spec ↧ℂ))
    [IsProjective X.hom] (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) :
    ∃ (d n : ℕ) (e : Fin n ≃ G),
      ∃ j : X ⟶ Over.mk (Proj.toSpecZero (homogeneousSubmodule (Fin n → Fin (d + 1)) ℂ) ≫
        Spec.map (ProjectiveSpace.degreeZeroEquiv (Fin n → Fin (d + 1)) ℂ).symm.toCommRingCatIso.hom),
        IsClosedImmersion j.left ∧ ∀ g : G,
          (ρ g).asIso.hom.left ≫ j.left = j.left ≫ s2_segreCoordinateMap ℂ d n
            (e.trans ((Equiv.mulLeft g).trans e.symm)) := by
  obtain ⟨d, n, e, j, hj, he⟩ := s2_projective_equivariantProductEmbedding X G ρ
  letI := hj
  letI := s2_polynomialSegreMap_isClosedImmersion d n
  refine ⟨d, n, e, j ≫ s2_polynomialSegreMap d n, ?_, ?_⟩
  · change IsClosedImmersion (j.left ≫ (s2_polynomialSegreMap d n).left)
    exact IsClosedImmersion.comp _ _
  · intro g
    rw [Over.comp_left, ← Category.assoc, ← Over.comp_left, he g,
      Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg (fun f => j.left ≫ f) (s2_polynomialSegreMap_permute d n
      (e.trans ((Equiv.mulLeft g).trans e.symm)))

end HodgeLean.Foundations.Program

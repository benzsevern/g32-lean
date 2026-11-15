import HodgeLean.Foundations.Program.SchoenEquivariantPolynomialEmbedding
import HodgeLean.Foundations.Program.SchoenPolynomialProjAction
import HodgeLean.Foundations.Program.SchoenRegularPermutation

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite projective complex action has actual equivariant polynomial coordinates with additive-subgroup degree pieces and retained coefficient base. -/
theorem s2_projective_equivariantSubgroupCoordinates (X : Over (Spec ↧ℂ))
    [IsProjective X.hom] (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) :
    ∃ (d n : ℕ) (e : Fin n ≃ G),
      let 𝒢 := homogeneousSubmodule (Fin n → Fin (d + 1)) ℂ
      let 𝒜 := s2_submoduleGradedPieces 𝒢
      letI := s2_submoduleGradingAsSubgroups 𝒢
      letI := s2_polynomialPermutationAction ℂ d n (s2_regularPermutation e)
      ∃ j : X.left ⟶ Proj 𝒜, IsClosedImmersion j ∧
        j ≫ (s2_submoduleGradingProjIso 𝒢).hom ≫ Proj.toSpecZero 𝒢 ≫
          Spec.map (ProjectiveSpace.degreeZeroEquiv (Fin n → Fin (d + 1)) ℂ).symm.toCommRingCatIso.hom = X.hom ∧
        ∀ g : G, (ρ g).asIso.hom.left ≫ j = j ≫
          (s2_projAction 𝒜 (s2_polynomialPermutationAction_preserves_grading ℂ d n
            (s2_regularPermutation e)) g).asIso.hom := by
  obtain ⟨d, n, e, j, hj, he⟩ := s2_projective_equivariantPolynomialEmbedding X G ρ
  let 𝒢 := homogeneousSubmodule (Fin n → Fin (d + 1)) ℂ
  let 𝒜 := s2_submoduleGradedPieces 𝒢
  letI := s2_submoduleGradingAsSubgroups 𝒢
  letI := s2_polynomialPermutationAction ℂ d n (s2_regularPermutation e)
  let c := s2_submoduleGradingProjIso 𝒢
  haveI := hj
  refine ⟨d, n, e, j.left ≫ c.inv, ?_, ?_, ?_⟩
  · infer_instance
  · rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact Over.w j
  · intro g
    apply (cancel_mono c.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [s2_polynomialProjAction_comparison]
    dsimp only [c, 𝒢]
    rw [Iso.inv_hom_id_assoc]
    exact he g

end HodgeLean.Foundations.Program

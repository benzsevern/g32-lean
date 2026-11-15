import HodgeLean.Foundations.Program.SchoenClosedProjQuotientProjectivity
import HodgeLean.Foundations.Program.SchoenEquivariantSubgroupCoordinates
import HodgeLean.Foundations.Program.SchoenPolynomialSubgroupBase

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual glued quotient of a finite action on an integral projective complex scheme is projective over the complex field. -/
theorem s2_projectiveAction_gluedQuotient_projective (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [IsProjective X.hom]
    [IsAffineHom (pullback.diagonal (terminal.from X.left))] (G : Type) [Group G] [Finite G]
    (ρ : G →* Aut X)
    (hcover : ∀ x : X.left, ∃ U : s2_InvariantAffineOpen X.left G
      (((Over.forget (Spec ↧ℂ)).mapAut X).comp ρ), x ∈ U.val)
    (hs : ∀ g : G, ((((Over.forget (Spec ↧ℂ)).mapAut X).comp ρ) g).asIso.hom ≫ X.hom = X.hom) :
    IsProjective (s2_gluedQuotientStructure X.hom G
      (((Over.forget (Spec ↧ℂ)).mapAut X).comp ρ) hs hcover) := by
  haveI : IsAffine (terminal Scheme.{0}) :=
    IsAffine.of_isIso (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).inv
  haveI : IsSeparated (terminal.from X.left) := by
    rw [← terminal.comp_from X.hom]
    infer_instance
  letI := Fintype.ofFinite G
  let ρs := ((Over.forget (Spec ↧ℂ)).mapAut X).comp ρ
  obtain ⟨d, n, e, j, hj, hb, he⟩ := s2_projective_equivariantSubgroupCoordinates X G ρ
  let 𝒢 := homogeneousSubmodule (Fin n → Fin (d + 1)) ℂ
  let 𝒜 := s2_submoduleGradedPieces 𝒢
  letI := s2_submoduleGradingAsSubgroups 𝒢
  letI := s2_polynomialPermutationAction ℂ d n (s2_regularPermutation e)
  let hg := s2_polynomialPermutationAction_preserves_grading ℂ d n (s2_regularPermutation e)
  let hz := s2_polynomialPermutationAction_fixes_degreeZero ℂ d n (s2_regularPermutation e)
  have hk : ∀ m, ∀ k : ℂ, ∀ a ∈ 𝒜 m, k • a ∈ 𝒜 m := by
    intro m k a ha
    exact (𝒢 m).smul_mem k ha
  haveI : IsNoetherianRing (𝒜 0) := s2_polynomialSubgroup_degreeZero_noetherian ℂ _
  haveI : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin n → Fin (d + 1)) ℂ) :=
    s2_polynomialSubgroup_finiteType ℂ _
  haveI := hj
  have hb' : j ≫ Proj.toSpecZero 𝒜 ≫
      Spec.map (s2_polynomialSubgroupDegreeZeroEquiv ℂ (Fin n → Fin (d + 1))).symm.toCommRingCatIso.hom = X.hom := by
    rw [← s2_polynomialSubgroupProj_toCoefficient]
    exact hb
  exact s2_closedProjQuotient_projective 𝒜 hg hk hz
    (s2_polynomialSubgroupDegreeZeroEquiv ℂ _) X.left ρs hcover X.hom hs j he hb'

end HodgeLean.Foundations.Program

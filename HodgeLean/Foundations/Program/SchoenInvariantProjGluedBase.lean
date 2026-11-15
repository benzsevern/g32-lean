import HodgeLean.Foundations.Program.SchoenInvariantProjBase
import HodgeLean.Foundations.Program.SchoenInvariantProjGluedComparison
import HodgeLean.Foundations.Program.SchoenQuotientBase

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- The actual glued-to-Proj isomorphism respects the retained degree-zero structure morphism. -/
theorem s2_invariantProjGluedIso_over {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [IsDomain A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [IsIntegral (Proj 𝒜)]
    [IsAffineHom (pullback.diagonal (terminal.from (Proj 𝒜)))]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    (s2_invariantProjGluedIso 𝒜 hgrade hK).hom ≫
      Proj.toSpecZero (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) ≫
      Spec.map (CommRingCat.ofHom (s2_fixedDegreeZeroHom 𝒜 hgrade hzero)) =
    s2_gluedQuotientStructure (Proj.toSpecZero 𝒜) G (s2_projAction 𝒜 hgrade)
      (s2_projAction_toSpecZero 𝒜 hgrade hK hzero)
      (s2_proj_invariantAffineCover 𝒜 hgrade hK) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  haveI := s2_gluedQuotientMap_epi (Proj 𝒜) G (s2_projAction 𝒜 hgrade)
    (s2_proj_invariantAffineCover 𝒜 hgrade hK)
  apply (cancel_epi (s2_gluedQuotientMap (Proj 𝒜) G (s2_projAction 𝒜 hgrade)
    (s2_proj_invariantAffineCover 𝒜 hgrade hK))).mp
  change _ ≫ s2_invariantProjGluedComparison 𝒜 hgrade hK ≫ _ = _
  rw [← Category.assoc, s2_invariantProjGluedComparison_projection,
    s2_invariantProjMap_toSpecZero, s2_gluedQuotientStructure_fac]

end HodgeLean.Foundations.Program

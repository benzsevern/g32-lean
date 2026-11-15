import HodgeLean.Foundations.Program.SchoenInvariantProjProjective
import HodgeLean.Foundations.Program.SchoenInvariantProjGluedBase

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- The actual glued invariant quotient of a finite-type graded domain has a projective structure map. -/
theorem s2_gluedProjQuotient_projective {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [IsDomain A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [IsNoetherianRing (𝒜 0)]
    [Algebra.FiniteType (𝒜 0) A] [IsIntegral (Proj 𝒜)]
    [IsAffineHom (pullback.diagonal (terminal.from (Proj 𝒜)))]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a) :
    IsProjective (s2_gluedQuotientStructure (Proj.toSpecZero 𝒜) G (s2_projAction 𝒜 hgrade)
      (s2_projAction_toSpecZero 𝒜 hgrade hK hzero)
      (s2_proj_invariantAffineCover 𝒜 hgrade hK)) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  haveI := s2_invariantProj_projective 𝒜 hgrade hzero
  have h := s2_projective_precomp_iso (s2_invariantProjGluedIso 𝒜 hgrade hK).hom
    (Proj.toSpecZero (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) ≫
      Spec.map (CommRingCat.ofHom (s2_fixedDegreeZeroHom 𝒜 hgrade hzero)))
  rwa [s2_invariantProjGluedIso_over] at h

end HodgeLean.Foundations.Program

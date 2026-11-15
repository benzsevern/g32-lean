import HodgeLean.Foundations.Program.SchoenInvariantGradedFiniteType
import HodgeLean.Foundations.Program.SchoenPositiveGradedProjectivity
import HodgeLean.Foundations.Program.SchoenProjectiveBaseIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- The actual invariant Proj has a projective presentation over the retained ambient degree-zero ring. -/
theorem s2_invariantProj_projective {A G : Type} [CommRing A] [IsDomain A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [IsNoetherianRing (𝒜 0)]
    [Algebra.FiniteType (𝒜 0) A] [Group G] [Finite G] [MulSemiringAction G A]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    IsProjective (Proj.toSpecZero (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) ≫
      Spec.map (CommRingCat.ofHom (s2_fixedDegreeZeroHom 𝒜 hgrade hzero))) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  let ℬ := s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)
  haveI := s2_fixedGradedRing_finiteType 𝒜 hgrade hzero
  haveI : IsProjective (Proj.toSpecZero ℬ) := s2_projective_toSpecZero_of_finiteType ℬ
  haveI : IsIso (CommRingCat.ofHom (s2_fixedDegreeZeroHom 𝒜 hgrade hzero)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (s2_fixedDegreeZeroEquiv 𝒜 hgrade hzero).bijective
  exact s2_projective_comp_base_iso _ _

end HodgeLean.Foundations.Program

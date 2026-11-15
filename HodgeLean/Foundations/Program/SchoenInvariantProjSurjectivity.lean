import HodgeLean.Foundations.Program.SchoenFixedHomogeneousIntegrality
import HodgeLean.Foundations.Program.SchoenInvariantProjMap
import HodgeLean.Foundations.Program.SchoenProjRadicalCharts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual invariant Proj scheme morphism is surjective for a graded domain. -/
theorem s2_invariantProjMap_surjective {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [IsDomain A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    Surjective (s2_invariantProjMap 𝒜 hgrade hK) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  apply IsZariskiLocalAtTarget.of_openCover
    (Proj.affineOpenCover (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G))).openCover
  intro c
  have H := (S2RadicalProj.away_isPullback _ _
    (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G))
    (s2_fixedRing_irrelevant_le_radical 𝒜 hgrade hK)
    c.1.property c.2.val c.2.property).flip
  haveI : Surjective (Spec.map (CommRingCat.ofHom
      (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) c.2.val))) :=
    ⟨s2_fixedHomogeneousChart_surjective_all 𝒜 hgrade c.2.val c.2.property⟩
  change Surjective (pullback.snd (s2_invariantProjMap 𝒜 hgrade hK)
    (Proj.awayι _ c.2.val c.2.property c.1.property))
  change Surjective (pullback.snd (S2RadicalProj.map _ _
    (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G))
    (s2_fixedRing_irrelevant_le_radical 𝒜 hgrade hK))
    (Proj.awayι _ c.2.val c.2.property c.1.property))
  rw [← H.isoPullback_inv_snd]
  infer_instance

end HodgeLean.Foundations.Program

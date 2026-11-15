import HodgeLean.Foundations.Program.SchoenInvariantProjDescent
import HodgeLean.Foundations.Program.SchoenProjInvariantAffineCover
import HodgeLean.Foundations.Program.SchoenGlobalTargetDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

variable {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [IsDomain A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [IsIntegral (Proj 𝒜)]
    [IsAffineHom (pullback.diagonal (terminal.from (Proj 𝒜)))]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)

/-- The actual invariant Proj projection descends through the glued invariant scheme. -/
def s2_invariantProjGluedComparison :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    s2_invariantAffineGlued (Proj 𝒜) G (s2_projAction 𝒜 hgrade) ⟶
      Proj (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  exact (s2_gluedQuotientDesc_arbitrary (Proj 𝒜) G (s2_projAction 𝒜 hgrade)
    (s2_proj_invariantAffineCover 𝒜 hgrade hK) _ (s2_invariantProjMap 𝒜 hgrade hK)
    (s2_invariantProjMap_invariant 𝒜 hgrade hK)).choose

/-- The glued-to-Proj comparison preserves the actual projection from the source. -/
theorem s2_invariantProjGluedComparison_projection :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    s2_gluedQuotientMap (Proj 𝒜) G (s2_projAction 𝒜 hgrade)
      (s2_proj_invariantAffineCover 𝒜 hgrade hK) ≫
      s2_invariantProjGluedComparison 𝒜 hgrade hK = s2_invariantProjMap 𝒜 hgrade hK := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  exact (s2_gluedQuotientDesc_arbitrary (Proj 𝒜) G (s2_projAction 𝒜 hgrade)
    (s2_proj_invariantAffineCover 𝒜 hgrade hK) _ (s2_invariantProjMap 𝒜 hgrade hK)
    (s2_invariantProjMap_invariant 𝒜 hgrade hK)).choose_spec.1

/-- The glued quotient projection descends through the actual invariant Proj projection. -/
def s2_invariantProjGluedInverse :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    Proj (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) ⟶
      s2_invariantAffineGlued (Proj 𝒜) G (s2_projAction 𝒜 hgrade) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  exact (s2_invariantProjDesc 𝒜 hgrade hK
    (s2_gluedQuotientMap (Proj 𝒜) G (s2_projAction 𝒜 hgrade)
      (s2_proj_invariantAffineCover 𝒜 hgrade hK))
    (s2_gluedQuotientMap_invariant (Proj 𝒜) G (s2_projAction 𝒜 hgrade)
      (s2_proj_invariantAffineCover 𝒜 hgrade hK))).choose

/-- The Proj-to-glued comparison preserves the actual projection from the source. -/
theorem s2_invariantProjGluedInverse_projection :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    s2_invariantProjMap 𝒜 hgrade hK ≫ s2_invariantProjGluedInverse 𝒜 hgrade hK =
      s2_gluedQuotientMap (Proj 𝒜) G (s2_projAction 𝒜 hgrade)
        (s2_proj_invariantAffineCover 𝒜 hgrade hK) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  exact (s2_invariantProjDesc 𝒜 hgrade hK
    (s2_gluedQuotientMap (Proj 𝒜) G (s2_projAction 𝒜 hgrade)
      (s2_proj_invariantAffineCover 𝒜 hgrade hK))
    (s2_gluedQuotientMap_invariant (Proj 𝒜) G (s2_projAction 𝒜 hgrade)
      (s2_proj_invariantAffineCover 𝒜 hgrade hK))).choose_spec.1

/-- The actual invariant Proj is isomorphic to the quotient glued from invariant affine charts. -/
def s2_invariantProjGluedIso :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    s2_invariantAffineGlued (Proj 𝒜) G (s2_projAction 𝒜 hgrade) ≅
      Proj (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  haveI := s2_gluedQuotientMap_epi (Proj 𝒜) G (s2_projAction 𝒜 hgrade)
    (s2_proj_invariantAffineCover 𝒜 hgrade hK)
  haveI := s2_invariantProjMap_epi 𝒜 hgrade hK
  refine { hom := s2_invariantProjGluedComparison 𝒜 hgrade hK
           inv := s2_invariantProjGluedInverse 𝒜 hgrade hK
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · apply (cancel_epi (s2_gluedQuotientMap (Proj 𝒜) G (s2_projAction 𝒜 hgrade)
      (s2_proj_invariantAffineCover 𝒜 hgrade hK))).mp
    rw [← Category.assoc, s2_invariantProjGluedComparison_projection,
      s2_invariantProjGluedInverse_projection, Category.comp_id]
  · apply (cancel_epi (s2_invariantProjMap 𝒜 hgrade hK)).mp
    rw [← Category.assoc, s2_invariantProjGluedInverse_projection,
      s2_invariantProjGluedComparison_projection, Category.comp_id]

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenInvariantProjAction
import HodgeLean.Foundations.Program.SchoenProjRadicalComposition

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Every graded action homomorphism fixes the actual graded invariant-ring inclusion. -/
theorem s2_gradedActionHom_comp_fixedInclusion {A G : Type} [CommRing A] [Group G]
    [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n) (g : G) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    (s2_gradedActionHom 𝒜 hgrade g).comp
      (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) =
      s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  ext a
  exact a.property g

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual invariant Proj projection is invariant as a scheme morphism. -/
theorem s2_invariantProjMap_invariant {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n) (g : G) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    (s2_projAction 𝒜 hgrade g).asIso.hom ≫ s2_invariantProjMap 𝒜 hgrade hK =
      s2_invariantProjMap 𝒜 hgrade hK := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  let f := s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)
  let t := s2_gradedActionHom 𝒜 hgrade g⁻¹
  have he : t.comp f = f := s2_gradedActionHom_comp_fixedInclusion 𝒜 hgrade g⁻¹
  have hf := s2_fixedRing_irrelevant_le_radical 𝒜 hgrade hK
  have ht0 : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map t.toRingHom :=
    s2_gradedActionHom_irrelevant_le 𝒜 hgrade g⁻¹
  have ht : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map t.toRingHom).radical :=
    ht0.trans Ideal.le_radical
  have htf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      ((HomogeneousIdeal.irrelevant (s2_subringGradedPiece 𝒜
        (FixedPoints.subring A G))).toIdeal.map (t.comp f).toRingHom).radical := by
    rw [he]
    exact hf
  have hc := S2RadicalProj.map_comp _ _ _ f t hf ht htf
  simp only [he] at hc
  exact hc.symm

end HodgeLean.Foundations.Program

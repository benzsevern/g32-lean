import HodgeLean.Foundations.Program.SchoenInvariantProjInvariance
import HodgeLean.Foundations.Program.SchoenInvariantProjFiniteness
import HodgeLean.Foundations.Program.SchoenFixedDegreeZeroEquiv

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual invariant Proj projection respects the original pointwise fixed degree-zero base. -/
theorem s2_invariantProjMap_toSpecZero {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    s2_invariantProjMap 𝒜 hgrade hK ≫
      Proj.toSpecZero (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) ≫
      Spec.map (CommRingCat.ofHom (s2_fixedDegreeZeroHom 𝒜 hgrade hzero)) =
      Proj.toSpecZero 𝒜 := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  let ℬ := s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)
  let q := s2_invariantProjMap 𝒜 hgrade hK
  apply Scheme.Cover.hom_ext ((Proj.affineOpenCover ℬ).openCover.pullback₁ q)
  intro c
  change (i : {n : ℕ // 0 < n}) × ℬ i at c
  have H := (S2RadicalProj.away_isPullback ℬ 𝒜
    (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G))
    (s2_fixedRing_irrelevant_le_radical 𝒜 hgrade hK) c.1.property c.2.val c.2.property).flip
  apply (cancel_epi H.isoPullback.hom).mp
  change H.isoPullback.hom ≫ pullback.fst _ _ ≫ _ =
    H.isoPullback.hom ≫ pullback.fst _ _ ≫ _
  simp only [← Category.assoc, H.isoPullback_hom_fst]
  dsimp only [s2_invariantProjMap]
  rw [S2RadicalProj.awayι_comp_map ℬ 𝒜
    (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G))
    (s2_fixedRing_irrelevant_le_radical 𝒜 hgrade hK) c.1.property c.2.val c.2.property]
  dsimp only [ℬ]
  simp only [Category.assoc, Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero]
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (s2_fixedHomogeneousChartMap_coefficients 𝒜 hgrade hzero c.2.val)

/-- The actual Proj action is over degree zero when the action fixes degree zero pointwise. -/
theorem s2_projAction_toSpecZero {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a) (g : G) :
    (s2_projAction 𝒜 hgrade g).asIso.hom ≫ Proj.toSpecZero 𝒜 = Proj.toSpecZero 𝒜 := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  rw [← s2_invariantProjMap_toSpecZero 𝒜 hgrade hK hzero]
  rw [← Category.assoc, s2_invariantProjMap_invariant]

end HodgeLean.Foundations.Program

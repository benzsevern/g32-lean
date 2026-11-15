import HodgeLean.Foundations.Program.SchoenSpecFixedDescent
import HodgeLean.Foundations.Program.SchoenProjFixedCharts
import HodgeLean.Foundations.Program.SchoenFixedHomogeneousCharts
import HodgeLean.Foundations.Program.SchoenHomogeneousDomains

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization CategoryTheory
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An invariant morphism from Proj descends on each nonzero fixed homogeneous affine chart. -/
theorem s2_invariantProjChartDesc {A G : Type} [CommRing A] [IsDomain A]
    [Group G] [Finite G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    {T : Scheme.{0}} (f : Proj 𝒜 ⟶ T)
    (hf : ∀ g : G, (s2_projAction 𝒜 hgrade g).asIso.hom ≫ f = f)
    {n : ℕ} (hn : 0 < n) (a : FixedPoints.subring A G) (ha : a.val ∈ 𝒜 n)
    (hane : a.val ≠ 0) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    ∃ d : Spec (CommRingCat.of (Away (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) a)) ⟶ T,
      Spec.map (CommRingCat.ofHom
        (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a)) ≫ d =
      Proj.awayι 𝒜 a.val ha hn ≫ f := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  letI := s2_homogeneousAway_isDomain 𝒜 a.val hane
  have hinv (g : G) :
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G (Away 𝒜 a.val) g)) ≫
        (Proj.awayι 𝒜 a.val ha hn ≫ f) = Proj.awayι 𝒜 a.val ha hn ≫ f := by
    have H := s2_projAction_fixed_awayι 𝒜 hgrade g⁻¹ hn a ha
    simp only [inv_inv] at H
    rw [← Category.assoc, ← H, Category.assoc, hf]
  obtain ⟨d, hd, _⟩ := s2_specFixedQuotientDesc (Away 𝒜 a.val) G
    (Proj.awayι 𝒜 a.val ha hn ≫ f) hinv
  refine ⟨(s2_fixedHomogeneousChartIso 𝒜 hgrade a ha hane).inv ≫ d, ?_⟩
  rw [← s2_fixedHomogeneousChartIso_quotient 𝒜 hgrade a ha hane,
    Category.assoc, Iso.hom_inv_id_assoc, hd]

end HodgeLean.Foundations.Program

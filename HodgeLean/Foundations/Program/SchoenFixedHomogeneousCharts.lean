import HodgeLean.Foundations.Program.SchoenFixedHomogeneousLocalization
import Mathlib.AlgebraicGeometry.Spec

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- The actual invariant homogeneous affine chart is the spectrum of the localized fixed ring. -/
def s2_fixedHomogeneousChartIso {A G : Type} [CommRing A] [IsDomain A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) (hane : a.val ≠ 0) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    letI := s2_homogeneousAwayAction 𝒜 hgrade a
    Spec (CommRingCat.of (FixedPoints.subring (Away 𝒜 a.val) G)) ≅
      Spec (CommRingCat.of (Away (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) a)) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  exact Scheme.Spec.mapIso
    (s2_fixedHomogeneousLocalizationEquiv 𝒜 hgrade a ha hane).toCommRingCatIso.op

/-- The homogeneous chart identification preserves the actual affine quotient projection. -/
theorem s2_fixedHomogeneousChartIso_quotient {A G : Type} [CommRing A] [IsDomain A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) (hane : a.val ≠ 0) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    letI := s2_homogeneousAwayAction 𝒜 hgrade a
    Spec.map (CommRingCat.ofHom (FixedPoints.subring (Away 𝒜 a.val) G).subtype) ≫
      (s2_fixedHomogeneousChartIso 𝒜 hgrade a ha hane).hom =
    Spec.map (CommRingCat.ofHom
      (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a)) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext z
  rfl

end HodgeLean.Foundations.Program

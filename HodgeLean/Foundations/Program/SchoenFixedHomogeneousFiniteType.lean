import HodgeLean.Foundations.Program.SchoenFixedHomogeneousIntegrality
import HodgeLean.Foundations.Program.SchoenFixedDegreeZero

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The fixed-ring homogeneous chart map preserves the original degree-zero coefficients. -/
theorem s2_fixedHomogeneousChartMap_coefficients {A G : Type} [CommRing A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a)
    (a : FixedPoints.subring A G) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a).comp
      ((fromZeroRingHom (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G))
        (Submonoid.powers a)).comp (s2_fixedDegreeZeroHom 𝒜 hgrade hzero)) =
    fromZeroRingHom 𝒜 (Submonoid.powers a.val) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  apply RingHom.ext
  intro b
  apply HomogeneousLocalization.val_injective
  simp [Away.map, HomogeneousLocalization.map_mk, fromZeroRingHom,
    HomogeneousLocalization.val_mk, s2_fixedDegreeZeroHom, s2_subringGradedInclusion]

/-- Finite generation over pointwise fixed degree zero gives finite type for each chart map. -/
theorem s2_fixedHomogeneousChartMap_finiteType {A G : Type} [CommRing A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    [Algebra.FiniteType (𝒜 0) A]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a).FiniteType := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  have ht : (fromZeroRingHom 𝒜 (Submonoid.powers a.val)).FiniteType :=
    Away.finiteType a.val d ha
  rw [← s2_fixedHomogeneousChartMap_coefficients 𝒜 hgrade hzero a] at ht
  exact RingHom.FiniteType.of_comp_finiteType ht

/-- Actual invariant homogeneous chart maps are finite over pointwise fixed degree zero. -/
theorem s2_fixedHomogeneousChartMap_finite {A G : Type} [CommRing A] [IsDomain A]
    [Group G] [Finite G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    [Algebra.FiniteType (𝒜 0) A]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a).Finite := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  exact (s2_fixedHomogeneousLocalizationMap_integral_all 𝒜 hgrade a ha).to_finite
    (s2_fixedHomogeneousChartMap_finiteType 𝒜 hgrade hzero a ha)

end HodgeLean.Foundations.Program

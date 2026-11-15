import HodgeLean.Foundations.Program.SchoenHomogeneousLocalizationMaps
import HodgeLean.Foundations.Program.SchoenHomogeneousAwayAction
import HodgeLean.Foundations.Program.SchoenHomogeneousFractionCancellation
import HodgeLean.Foundations.Program.SchoenFixedRingGrading

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual homogeneous-localization map from the fixed ring has fixed image. -/
theorem s2_fixedHomogeneousLocalization_image_fixed {A G : Type} [CommRing A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    letI := s2_homogeneousAwayAction 𝒜 hgrade a
    ∀ z : Away (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) a,
      Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a z ∈
        FixedPoints.subring (Away 𝒜 a.val) G := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  intro z g
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective
    (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) ha z
  rw [Away.map_mk]
  change g • Away.mk 𝒜 ha n b.val hb = Away.mk 𝒜 ha n b.val hb
  rw [s2_homogeneousAwayAction_mk]
  simp only [b.property g]

/-- The actual homogeneous-localization map into the fixed subring of the chart ring. -/
def s2_fixedHomogeneousLocalizationMap {A G : Type} [CommRing A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    letI := s2_homogeneousAwayAction 𝒜 hgrade a
    Away (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) a →+*
      FixedPoints.subring (Away 𝒜 a.val) G := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  exact (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a).codRestrict _
    (s2_fixedHomogeneousLocalization_image_fixed 𝒜 hgrade a ha)

/-- A fixed homogeneous fraction with nonzero fixed denominator has a fixed numerator. -/
theorem s2_fixedHomogeneousFraction_numerator {A G : Type} [CommRing A] [IsDomain A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) (hane : a.val ≠ 0)
    (n : ℕ) (b : A) (hb : b ∈ 𝒜 (n • d)) :
    letI := s2_homogeneousAwayAction 𝒜 hgrade a
    Away.mk 𝒜 ha n b hb ∈ FixedPoints.subring (Away 𝒜 a.val) G → b ∈ FixedPoints.subring A G := by
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  intro hfixed g
  have he := hfixed g
  rw [s2_homogeneousAwayAction_mk] at he
  exact s2_homogeneousAway_mk_num_injective 𝒜 ha hane n (hgrade g (n • d) b hb) hb he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Homogeneous localization of the fixed ring surjects onto the actual chart invariants. -/
theorem s2_fixedHomogeneousLocalizationMap_surjective {A G : Type} [CommRing A] [IsDomain A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) (hane : a.val ≠ 0) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    letI := s2_homogeneousAwayAction 𝒜 hgrade a
    Function.Surjective (s2_fixedHomogeneousLocalizationMap 𝒜 hgrade a ha) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  intro z
  obtain ⟨n, b, hb, hbz⟩ := Away.mk_surjective 𝒜 ha z.val
  have hbFixed : b ∈ FixedPoints.subring A G :=
    s2_fixedHomogeneousFraction_numerator 𝒜 hgrade a ha hane n b hb (by
      rw [hbz]
      exact z.property)
  let bR : FixedPoints.subring A G := ⟨b, hbFixed⟩
  refine ⟨Away.mk (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) ha n bR hb, ?_⟩
  apply Subtype.ext
  change Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a
    (Away.mk (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) ha n bR hb) = z.val
  rw [Away.map_mk]
  exact hbz

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual fixed homogeneous-localization comparison is injective away from nonzero elements. -/
theorem s2_fixedHomogeneousLocalizationMap_injective {A G : Type} [CommRing A] [IsDomain A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) (hane : a.val ≠ 0) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    letI := s2_homogeneousAwayAction 𝒜 hgrade a
    Function.Injective (s2_fixedHomogeneousLocalizationMap 𝒜 hgrade a ha) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  let f := s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)
  have hMN : Submonoid.powers a ≤ (Submonoid.powers a.val).comap f := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, rfl⟩
  have hN : (0 : A) ∉ Submonoid.powers a.val := by
    rintro ⟨n, hn⟩
    exact pow_ne_zero n hane hn
  have hinj : Function.Injective (Away.map f a) :=
    s2_homogeneousLocalization_map_injective _ _ f (Submonoid.powers a)
      (Submonoid.powers a.val) hMN hN Subtype.val_injective
  intro x y hxy
  apply hinj
  exact congrArg (fun z : FixedPoints.subring (Away 𝒜 a.val) G => z.val) hxy

/-- Homogeneous localization commutes with the actual fixed subring away from a nonzero fixed element. -/
def s2_fixedHomogeneousLocalizationEquiv {A G : Type} [CommRing A] [IsDomain A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) (hane : a.val ≠ 0) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    letI := s2_homogeneousAwayAction 𝒜 hgrade a
    Away (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) a ≃+*
      FixedPoints.subring (Away 𝒜 a.val) G := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  exact RingEquiv.ofBijective (s2_fixedHomogeneousLocalizationMap 𝒜 hgrade a ha)
    ⟨s2_fixedHomogeneousLocalizationMap_injective 𝒜 hgrade a ha hane,
      s2_fixedHomogeneousLocalizationMap_surjective 𝒜 hgrade a ha hane⟩

end HodgeLean.Foundations.Program

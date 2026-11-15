import HodgeLean.Foundations.Program.SchoenFixedHomogeneousLocalization
import HodgeLean.Foundations.Program.SchoenInvariantRings

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- The actual homogeneous chart map from fixed elements is integral for a finite group. -/
theorem s2_fixedHomogeneousLocalizationMap_integral {A G : Type} [CommRing A] [IsDomain A]
    [Group G] [Finite G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) (hane : a.val ≠ 0) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a).IsIntegral := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  let L := Away 𝒜 a.val
  letI : Algebra.IsInvariant (FixedPoints.subring L G) L G :=
    ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have hi : (FixedPoints.subring L G).subtype.IsIntegral :=
    (Algebra.IsInvariant.isIntegral (FixedPoints.subring L G) L G).isIntegral
  have he := (s2_fixedHomogeneousLocalizationEquiv 𝒜 hgrade a ha hane).toRingHom
    |>.isIntegral_of_surjective (s2_fixedHomogeneousLocalizationEquiv 𝒜 hgrade a ha hane).surjective
  exact RingHom.IsIntegral.trans _ _ he hi

/-- The actual map on invariant homogeneous chart spectra is surjective. -/
theorem s2_fixedHomogeneousChart_surjective {A G : Type} [CommRing A] [IsDomain A]
    [Group G] [Finite G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) (hane : a.val ≠ 0) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    Function.Surjective (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a))) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  apply (s2_fixedHomogeneousLocalizationMap_integral 𝒜 hgrade a ha hane).comap_surjective
  intro x y hxy
  apply s2_fixedHomogeneousLocalizationMap_injective 𝒜 hgrade a ha hane
  exact Subtype.ext hxy

/-- Surjectivity of homogeneous invariant chart projections also includes the empty zero chart. -/
theorem s2_fixedHomogeneousChart_surjective_all {A G : Type} [CommRing A] [IsDomain A]
    [Group G] [Finite G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    Function.Surjective (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a))) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  by_cases hane : a.val = 0
  · have ha0 : a = 0 := Subtype.ext hane
    subst a
    haveI : Subsingleton (Away (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) 0) :=
      HomogeneousLocalization.subsingleton _ ⟨1, pow_one 0⟩
    change Function.Surjective (PrimeSpectrum.comap _)
    intro y
    exact (y.isPrime.one_notMem (Subsingleton.elim (1 : Away
      (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) 0) 0 ▸ y.asIdeal.zero_mem)).elim
  · exact s2_fixedHomogeneousChart_surjective 𝒜 hgrade a ha hane

/-- Integrality of homogeneous fixed-ring chart maps includes the empty zero chart. -/
theorem s2_fixedHomogeneousLocalizationMap_integral_all {A G : Type} [CommRing A] [IsDomain A]
    [Group G] [Finite G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a).IsIntegral := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  by_cases hane : a.val = 0
  · haveI : Subsingleton (Away 𝒜 a.val) :=
      HomogeneousLocalization.subsingleton _ ⟨1, by simpa using hane⟩
    have hsurj : Function.Surjective
        (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a) := by
      intro x
      refine ⟨0, ?_⟩
      change (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a) 0 =
        (x : Away 𝒜 a.val)
      exact @Subsingleton.elim (Away 𝒜 a.val) inferInstance _ _
    exact RingHom.isIntegral_of_surjective _ hsurj
  · exact s2_fixedHomogeneousLocalizationMap_integral 𝒜 hgrade a ha hane

end HodgeLean.Foundations.Program

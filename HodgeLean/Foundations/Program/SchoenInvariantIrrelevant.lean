import HodgeLean.Foundations.Program.SchoenHomogeneousPrimeAvoidance
import HodgeLean.Foundations.Program.SchoenProjRadicalComap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Positive-degree invariants generate an ideal whose radical contains the
ambient irrelevant ideal over an infinite field. -/
theorem s2_fixedRing_irrelevant_le_radical {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      ((HomogeneousIdeal.irrelevant (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G))).toIdeal.map
        (FixedPoints.subring A G).subtype).radical := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  rw [Ideal.radical_eq_sInf]
  apply le_sInf
  intro P hP
  letI := hP.2
  rw [HomogeneousIdeal.irrelevant_eq_span]
  apply Ideal.span_le.mpr
  intro a ha
  obtain ⟨d, ha⟩ := Set.mem_iUnion.mp ha
  obtain ⟨hd, ha⟩ := Set.mem_iUnion.mp ha
  by_contra hnot
  obtain ⟨b, hb, hbnot⟩ := s2_homogeneous_fixed_prime_avoidance 𝒜 hgrade hK P d ⟨a, ha, hnot⟩
  have hbI : b ∈ HomogeneousIdeal.irrelevant (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ (Nat.mul_pos Fintype.card_pos hd) hb
  exact hbnot (hP.1 (Ideal.mem_map_of_mem (FixedPoints.subring A G).subtype hbI))

/-- The actual fixed-ring inclusion induces a continuous map on Proj spectra. -/
def s2_invariantProjComap {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    C(ProjectiveSpectrum 𝒜,
      ProjectiveSpectrum (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G))) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  exact s2_projRadicalComap _ _ (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G))
    (s2_fixedRing_irrelevant_le_radical 𝒜 hgrade hK)

end HodgeLean.Foundations.Program

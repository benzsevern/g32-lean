import HodgeLean.Foundations.Program.SchoenFixedHomogeneousFiniteType
import HodgeLean.Foundations.Program.SchoenInvariantProjMap
import HodgeLean.Foundations.Program.SchoenProjRadicalFiniteness

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual invariant Proj morphism is finite over pointwise fixed degree zero. -/
theorem s2_invariantProjMap_finite {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [IsDomain A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    IsFinite (s2_invariantProjMap 𝒜 hgrade hK) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  apply S2RadicalProj.map_finite_of_away_finite
  intro n hn a ha
  exact s2_fixedHomogeneousChartMap_finite 𝒜 hgrade hzero a ha

end HodgeLean.Foundations.Program

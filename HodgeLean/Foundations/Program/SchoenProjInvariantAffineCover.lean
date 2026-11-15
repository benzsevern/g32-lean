import HodgeLean.Foundations.Program.SchoenProjBasicNeighborhoods
import HodgeLean.Foundations.Program.SchoenInvariantProjAction
import HodgeLean.Foundations.Program.SchoenInvariantAffineDiagram

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Fixed homogeneous basic opens give actual invariant affine neighborhoods on the source Proj scheme. -/
theorem s2_proj_invariantAffineCover {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n) (x : Proj 𝒜) :
    ∃ U : s2_InvariantAffineOpen (Proj 𝒜) G (s2_projAction 𝒜 hgrade), x ∈ U.val := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  obtain ⟨n, hn, a, ha, _, hxa⟩ := s2_proj_exists_homogeneous_basicOpen
    (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) (s2_invariantProjMap 𝒜 hgrade hK x)
  have hx : x ∈ Proj.basicOpen 𝒜 a.val := hxa
  exact ⟨⟨Proj.basicOpen 𝒜 a.val,
    Proj.isAffineOpen_basicOpen 𝒜 a.val ha hn, ⟨x, hx⟩,
    s2_projAction_fixedBasicOpen 𝒜 hgrade a⟩, hx⟩

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenProjAction
import HodgeLean.Foundations.Program.SchoenInvariantProjMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual invariant Proj morphism is constant on the induced source action's point orbits. -/
theorem s2_invariantProjMap_action_point {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)
    (g : G) (x : Proj 𝒜) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    s2_invariantProjMap 𝒜 hgrade hK ((s2_projAction 𝒜 hgrade g).asIso.hom x) =
      s2_invariantProjMap 𝒜 hgrade hK x := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  change s2_invariantProjComap 𝒜 hgrade hK
    (AlgebraicGeometry.ProjectiveSpectrum.comapFun
      (s2_gradedActionHom 𝒜 hgrade g⁻¹)
      (s2_gradedActionHom_irrelevant_le 𝒜 hgrade g⁻¹) x) =
    s2_invariantProjComap 𝒜 hgrade hK x
  ext b
  change (g⁻¹ • b.val ∈ x.asHomogeneousIdeal) ↔ (b.val ∈ x.asHomogeneousIdeal)
  rw [b.property g⁻¹]

end HodgeLean.Foundations.Program

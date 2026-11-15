import HodgeLean.Foundations.Program.SchoenProjRadicalStalkInjection
import HodgeLean.Foundations.Program.SchoenInvariantProjSurjectivity

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- The actual invariant Proj projection is injective on every source stalk. -/
theorem s2_invariantProjMap_stalkMap_injective {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [IsDomain A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n) (p : Proj 𝒜) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    Function.Injective ((s2_invariantProjMap 𝒜 hgrade hK).stalkMap p) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  exact s2_projRadicalMap_stalkMap_injective _ _
    (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G))
    (s2_fixedRing_irrelevant_le_radical 𝒜 hgrade hK) Subtype.val_injective p

/-- The actual invariant Proj projection is an epimorphism for arbitrary scheme targets. -/
theorem s2_invariantProjMap_epi {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [IsDomain A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    Epi (s2_invariantProjMap 𝒜 hgrade hK) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  apply CategoryTheory.Functor.epi_of_epi_map Scheme.forgetToLocallyRingedSpace
  apply CategoryTheory.Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono _
    (s2_invariantProjMap_surjective 𝒜 hgrade hK).surj
  intro p
  apply ConcreteCategory.mono_of_injective
  exact s2_invariantProjMap_stalkMap_injective 𝒜 hgrade hK p

end HodgeLean.Foundations.Program

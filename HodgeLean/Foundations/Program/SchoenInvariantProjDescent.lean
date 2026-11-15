import HodgeLean.Foundations.Program.SchoenInvariantProjLocalDescent
import HodgeLean.Foundations.Program.SchoenInvariantProjInvariance

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Invariant morphisms to arbitrary schemes descend uniquely through the actual invariant Proj projection. -/
theorem s2_invariantProjDesc {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [IsDomain A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)
    {T : Scheme.{0}} (f : Proj 𝒜 ⟶ T)
    (hf : ∀ g : G, (s2_projAction 𝒜 hgrade g).asIso.hom ≫ f = f) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    ∃! d : Proj (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) ⟶ T,
      s2_invariantProjMap 𝒜 hgrade hK ≫ d = f := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  choose W hW d hd using s2_invariantProj_localDescent 𝒜 hgrade hK f hf
  have hcover : TopologicalSpace.IsOpenCover W := by
    change (⨆ y, W y) = ⊤
    apply top_unique
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩
  haveI := s2_invariantProjMap_surjective 𝒜 hgrade hK
  obtain ⟨e, he⟩ := s2_descent_of_openCover (s2_invariantProjMap 𝒜 hgrade hK)
    (s2_invariantProjMap_stalkMap_injective 𝒜 hgrade hK) f W hcover d hd
  haveI := s2_invariantProjMap_epi 𝒜 hgrade hK
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact (cancel_epi (s2_invariantProjMap 𝒜 hgrade hK)).mp (he'.trans he.symm)

end HodgeLean.Foundations.Program

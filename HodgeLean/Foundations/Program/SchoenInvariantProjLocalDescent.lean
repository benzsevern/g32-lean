import HodgeLean.Foundations.Program.SchoenInvariantProjChartDescent
import HodgeLean.Foundations.Program.SchoenProjBasicNeighborhoods
import HodgeLean.Foundations.Program.SchoenDescentChartTransfer
import HodgeLean.Foundations.Program.SchoenInvariantProjStalks

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization CategoryTheory
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every target point has an open neighborhood on which an invariant source morphism descends. -/
theorem s2_invariantProj_localDescent {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [IsDomain A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)
    {T : Scheme.{0}} (f : Proj 𝒜 ⟶ T)
    (hf : ∀ g : G, (s2_projAction 𝒜 hgrade g).asIso.hom ≫ f = f) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    ∀ y : Proj (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)),
      ∃ W : (Proj (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G))).Opens,
        y ∈ W ∧ ∃ d : W.toScheme ⟶ T,
          (s2_invariantProjMap 𝒜 hgrade hK ∣_ W) ≫ d =
            (s2_invariantProjMap 𝒜 hgrade hK ⁻¹ᵁ W).ι ≫ f := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  intro y
  obtain ⟨n, hn, a, ha, hane, hya⟩ := s2_proj_exists_homogeneous_basicOpen
    (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) y
  have hane' : a.val ≠ 0 := fun h => hane (Subtype.ext h)
  obtain ⟨d, hd⟩ := s2_invariantProjChartDesc 𝒜 hgrade f hf hn a ha hane'
  let j := Proj.awayι 𝒜 a.val ha hn
  let i := Proj.awayι (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) a ha hn
  let p := Spec.map (CommRingCat.ofHom
    (Away.map (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G)) a))
  have hc : j ≫ s2_invariantProjMap 𝒜 hgrade hK = p ≫ i :=
    S2RadicalProj.awayι_comp_map
      (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) 𝒜
      (s2_subringGradedInclusion 𝒜 (FixedPoints.subring A G))
      (s2_fixedRing_irrelevant_le_radical 𝒜 hgrade hK) hn a ha
  have hr : s2_invariantProjMap 𝒜 hgrade hK ⁻¹' Set.range i = Set.range j := by
    change ((s2_invariantProjMap 𝒜 hgrade hK ⁻¹ᵁ i.opensRange) : Set _) = (j.opensRange : Set (Proj 𝒜))
    dsimp only [i, j]
    rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
    rfl
  refine ⟨i.opensRange, ?_, ?_⟩
  · simpa only [i, Proj.opensRange_awayι] using hya
  · exact s2_descent_chart_transfer j p (s2_invariantProjMap 𝒜 hgrade hK) i hc hr f d hd

end HodgeLean.Foundations.Program

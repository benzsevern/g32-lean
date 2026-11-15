import HodgeLean.Foundations.Program.G32Native.NormalizedThomPullback
import HodgeLean.Foundations.Program.G32Native.ZeroRankLocalDetection

/-! # From local product normalizations to the selected bundle Thom class -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Bundle
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleThom

/-- Local product normalizations on every linear chart identify a pulled-back Thom class in every rank. -/
theorem bundleThom_pullback_of_local_chart_normalization
    {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    {A : TopPair}
    (F : TopPair.ofSubset (X := i1_totalSpace k E) (i1_zeroSupport k E)ᶜ ⟶ A)
    (u : RelativeCohomology ℚ A (2 * k))
    (hnormalized : ∀ (e : Trivialization (Fin k → ℂ)
      (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B)) (he : e.IsLinear ℂ),
      letI := he
      ∀ b : e.baseSet, ∃ U : Opens e.baseSet, b ∈ U ∧
        relativeCohomologyMap ℚ (2 * k)
          (i1_productBaseMap k (Subtype.val : U → e.baseSet) continuous_subtype_val ≫
            (i1_chartPairProductIso k E e).inv ≫ i1_chartInclusion k E e ≫ F) u =
          relativeCohomologyMap ℚ (2 * k) (i1_productNormalProjection U k)
            (normalizedPointCoclass k)) :
    relativeCohomologyMap ℚ (2 * k) F u = i1_bundleThom k E := by
  apply bundleThom_pullback_of_chart_normalization k E F u
  intro e he
  letI := he
  apply i1_relativeCohomologyMap_iso_injective (i1_chartPairProductIso k E e).symm (2 * k)
  have hprojection : (i1_chartPairProductIso k E e).inv ≫ i1_chartNormal k E e =
      i1_productNormalProjection e.baseSet k := by
    rw [← i1_chartPairProductIso_comp_projection k E e, Iso.inv_hom_id_assoc]
  change relativeCohomologyMap ℚ (2 * k) (i1_chartPairProductIso k E e).inv
      (relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E e ≫ F) u) =
    relativeCohomologyMap ℚ (2 * k) (i1_chartPairProductIso k E e).inv
      (i1_chartOrientation k E e)
  unfold i1_chartOrientation
  conv_rhs => rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hprojection]
  apply productThomCoclass_ext_of_locally_eq_allRanks k
  intro b
  obtain ⟨U, hb, hU⟩ := hnormalized e he b
  refine ⟨U, hb, ?_⟩
  conv_rhs => rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_productBaseMap_comp_projection]
  simpa only [relativeCohomologyMap_comp, LinearMap.comp_apply] using hU

end HodgeLean.Foundations.BundleThom

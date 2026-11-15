import HodgeLean.Foundations.BundleResolution.ComplexBundleThomFibreDetectionHelpers

/-! # Detection using one selected linear frame at each point

The frame may vary pointwise; no continuity of that selection is needed.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Bundle AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom HodgeLean.RealDefs
namespace HodgeLean.Foundations.TubularEuler
open BundleResolution

theorem bundleCoclass_eq_of_selected_fibres
    {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {k : ℕ} (E : I1ComplexBundle B k)
    (α β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ) (2 * k))
    (h : ∀ x : B, ∃ e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) E.fibre),
      ∃ he : e.IsLinear ℂ, ∃ hx : x ∈ e.baseSet,
      letI := he
      relativeCohomologyMap ℚ (2 * k) (i1_complexBundleFibrePairMap E e x hx) α =
        relativeCohomologyMap ℚ (2 * k) (i1_complexBundleFibrePairMap E e x hx) β) :
    α = β := by
  obtain ⟨a, rfl⟩ := (i1_complexBundleThomMultiplication_bijective E 0).surjective α
  obtain ⟨b, rfl⟩ := (i1_complexBundleThomMultiplication_bijective E 0).surjective β
  apply congrArg (i1_complexBundleThomMultiplication E 0)
  apply i1_degreeZero_eq_of_point_pullbacks
  intro x
  obtain ⟨e, he, hx, hf⟩ := h x
  letI := he
  apply i1_normalPointCupMap_injective k
  rw [← i1_complexBundleThomMultiplication_fibre_zeroDegree E e x hx,
    ← i1_complexBundleThomMultiplication_fibre_zeroDegree E e x hx]
  exact hf

theorem bundleCoclass_eq_thom_of_selected_fibres
    {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {k : ℕ} (E : I1ComplexBundle B k)
    (α : RelativeCohomology ℚ
      (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ) (2 * k))
    (h : ∀ x : B, ∃ e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) E.fibre),
      ∃ he : e.IsLinear ℂ, ∃ hx : x ∈ e.baseSet,
      letI := he
      relativeCohomologyMap ℚ (2 * k) (i1_complexBundleFibrePairMap E e x hx) α =
        normalizedPointCoclass k) :
    α = i1_bundleThom k E.fibre := by
  apply bundleCoclass_eq_of_selected_fibres E
  intro x
  obtain ⟨e, he, hx, hnorm⟩ := h x
  letI := he
  exact ⟨e, he, hx, hnorm.trans (i1_complexBundleThom_fibre E e x hx).symm⟩

#print axioms bundleCoclass_eq_thom_of_selected_fibres
#print axioms bundleCoclass_eq_of_selected_fibres

end HodgeLean.Foundations.TubularEuler

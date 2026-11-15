import HodgeLean.Foundations.BundleResolution.ThomMultiplicationFibreHelpers
import HodgeLean.Foundations.BundleResolution.ChernThomMultiplicationIsoHelpers
import HodgeLean.Foundations.BundleResolution.DegreeZeroPointDetectionHelpers

/-! # Detection of actual top-normal-degree bundle classes on their fibres

The actual Thom multiplication isomorphism reduces detection to degree-zero
point restriction, without a contractibility hypothesis on the original base.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Bundle AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {k : ℕ} (E : I1ComplexBundle B k)

theorem i1_complexBundleThom_eq_of_fibre_eq
    (α β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ) (2 * k))
    (h : ∀ (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) E.fibre)) (he : e.IsLinear ℂ)
      (b : B) (hb : b ∈ e.baseSet),
      relativeCohomologyMap ℚ (2 * k) (i1_complexBundleFibrePairMap E e b hb) α =
        relativeCohomologyMap ℚ (2 * k) (i1_complexBundleFibrePairMap E e b hb) β) :
    α = β := by
  obtain ⟨a, rfl⟩ := (i1_complexBundleThomMultiplication_bijective E 0).surjective α
  obtain ⟨b, rfl⟩ := (i1_complexBundleThomMultiplication_bijective E 0).surjective β
  apply congrArg (i1_complexBundleThomMultiplication E 0)
  apply i1_degreeZero_eq_of_point_pullbacks
  intro x
  let e := trivializationAt (Fin k → ℂ) E.fibre x
  have he : e.IsLinear ℂ := inferInstance
  letI := he
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt (Fin k → ℂ) E.fibre x
  apply i1_normalPointCupMap_injective k
  rw [← i1_complexBundleThomMultiplication_fibre_zeroDegree E e x hx,
    ← i1_complexBundleThomMultiplication_fibre_zeroDegree E e x hx]
  exact h e he x hx

theorem i1_complexBundleThom_eq_of_fibre_normalized
    (α : RelativeCohomology ℚ
      (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ) (2 * k))
    (h : ∀ (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) E.fibre)) (he : e.IsLinear ℂ)
      (b : B) (hb : b ∈ e.baseSet),
      relativeCohomologyMap ℚ (2 * k) (i1_complexBundleFibrePairMap E e b hb) α =
        HodgeLean.RealDefs.normalizedPointCoclass k) :
    α = i1_bundleThom k E.fibre := by
  apply i1_complexBundleThom_eq_of_fibre_eq E
  intro e he b hb
  letI := he
  exact (h e he b hb).trans (i1_complexBundleThom_fibre E e b hb).symm

end HodgeLean.Foundations.BundleResolution

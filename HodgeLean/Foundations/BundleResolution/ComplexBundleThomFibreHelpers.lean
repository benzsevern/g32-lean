import HodgeLean.Foundations.BundleResolution.BundleThomNormalizationHelpers
import HodgeLean.Foundations.BundleThom.ThomChartFibreHelpers

/-! # Actual fibre normalization of independently selected complex bundle Thom classes

The original chart fibre and chart inclusion give a single actual pair map
retaining the prescribed complex point coclass.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Bundle AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] {k : ℕ} (E : I1ComplexBundle B k)
variable (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) E.fibre)) [e.IsLinear ℂ]
variable (b : B) (hb : b ∈ e.baseSet)

def i1_complexBundleFibrePairMap : puncturedPair ℂ k ⟶
    TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ :=
  i1_chartFibreInclusion k E.fibre e b hb ≫ i1_chartInclusion k E.fibre e

variable [CompactSpace B] [T2Space B]

theorem i1_complexBundleThom_fibre :
    relativeCohomologyMap ℚ (2 * k) (i1_complexBundleFibrePairMap E e b hb)
      (i1_bundleThom k E.fibre) = normalizedPointCoclass k := by
  rw [i1_complexBundleFibrePairMap, relativeCohomologyMap_comp, LinearMap.comp_apply,
    i1_complexBundleThom_chart_normalization, i1_chartOrientation_fibre]

end HodgeLean.Foundations.BundleResolution

import HodgeLean.Foundations.BundleResolution.ChernDefs
import HodgeLean.Foundations.BundleThom.Thom

/-! # Every-chart normalization of the selected actual bundle Thom class

The selected class retains the normalization in the original uniqueness theorem.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Bundle TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

theorem i1_complexBundleThom_chart_normalization
    {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {k : ℕ} (E : I1ComplexBundle B k)
    (e : Trivialization (Fin k → ℂ)
      (TotalSpace.proj : TotalSpace (Fin k → ℂ) E.fibre → B)) [he : e.IsLinear ℂ] :
    relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E.fibre e)
      (i1_bundleThom k E.fibre) = i1_chartOrientation k E.fibre e :=
  Classical.choose_spec (i1_bundleThom_exists_unique k E.fibre).exists e he

end HodgeLean.Foundations.BundleResolution

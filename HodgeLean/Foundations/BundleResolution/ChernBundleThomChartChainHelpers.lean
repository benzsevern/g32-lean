import HodgeLean.Foundations.BundleResolution.ChernBundleThomCocycleHelpers
import HodgeLean.Foundations.BundleResolution.ChernChartCapQuasiIsoHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeClassNaturalityHelpers

/-! # Actual chart cap for the selected global Thom cocycle

The representative is pulled back by the specified chart inclusion.
Its class is the existing chart orientation by global normalization.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Bundle TopologicalSpace HomologicalComplex AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {k : ℕ} (E : I1ComplexBundle B k)
variable (e : Trivialization (Fin k → ℂ)
  (TotalSpace.proj : TotalSpace (Fin k → ℂ) E.fibre → B)) [e.IsLinear ℂ]

theorem i1_bundleThomCocycle_chart_class :
    i1_relativeCocycleClass (i1_chartPair k E.fibre e) (2 * k)
      (i1_relativeCocyclePullback (i1_chartInclusion k E.fibre e) (2 * k)
        (i1_bundleThomCocycle E)) = i1_chartOrientation k E.fibre e := by
  rw [← i1_relativeCohomologyMap_class, i1_bundleThomCocycle_class]
  exact Classical.choose_spec (i1_bundleThom_exists_unique k E.fibre).exists e
    (inferInstance : e.IsLinear ℂ)

theorem i1_bundleThomCocycle_chart_evenCap_quasiIso :
    QuasiIso (i1_evenRelativeCapExtendedChainMap (i1_chartPair k E.fibre e) k
      (i1_relativeCocyclePullback (i1_chartInclusion k E.fibre e) (2 * k)
        (i1_bundleThomCocycle E)).val
      (i1_relativeCocyclePullback (i1_chartInclusion k E.fibre e) (2 * k)
        (i1_bundleThomCocycle E)).property) :=
  i1_chartOrientation_evenCap_quasiIso E e _ (i1_bundleThomCocycle_chart_class E e)

end HodgeLean.Foundations.BundleResolution

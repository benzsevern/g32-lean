import HodgeLean.Foundations.BundleResolution.ChernChartBaseProjectionHelpers
import HodgeLean.Foundations.BundleResolution.ChernChartThomCapHelpers
import HodgeLean.Foundations.BundleResolution.ChernEvenCapQuasiIsoHelpers
import HodgeLean.Foundations.BundleThom.ChartRelativeVanishingHelpers

/-! # Actual chart orientation cap on integer-extended chains

Projection to the base detects the cap map. Low relative homology and the
actual cap homology maps then detect every integer degree.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex Bundle TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] {k : ℕ} (E : I1ComplexBundle B k)
variable (e : Trivialization (Fin k → ℂ)
  (TotalSpace.proj : TotalSpace (Fin k → ℂ) E.fibre → B)) [e.IsLinear ℂ]

theorem i1_chartOrientation_cap_bijective (n : ℕ) :
    Function.Bijective (relativeCapCohomologyLinear ℚ (i1_chartPair k E.fibre e)
      (2 * k) n (i1_chartOrientation k E.fibre e)) := by
  haveI := i1_chartBaseProjection_quasiIso E e
  have hp : Function.Injective (homologyMap ℚ n (i1_chartBaseProjection E e)) :=
    (ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap (singularChainComplexMap ℚ (i1_chartBaseProjection E e)) n)).1
  have ht := i1_chartThomCapToBase_bijective E e n
  constructor
  · intro x y h
    apply ht.1
    exact congrArg (homologyMap ℚ n (i1_chartBaseProjection E e)) h
  · intro y
    obtain ⟨x, hx⟩ := ht.2 (homologyMap ℚ n (i1_chartBaseProjection E e) y)
    exact ⟨x, hp hx⟩

theorem i1_chartOrientation_evenCap_quasiIso
    (φ : RelativeCocycle ℚ (i1_chartPair k E.fibre e) (2 * k))
    (hφ : i1_relativeCocycleClass (i1_chartPair k E.fibre e) (2 * k) φ =
      i1_chartOrientation k E.fibre e) :
    QuasiIso (i1_evenRelativeCapExtendedChainMap (i1_chartPair k E.fibre e) k φ.val φ.property) := by
  apply i1_evenRelativeCapExtendedChainMap_quasiIso
  · intro n
    have h := i1_chartOrientation_cap_bijective E e n
    rw [← hφ, i1_relativeCapCohomologyLinear_class] at h
    exact h
  · intro r hr
    exact i1_chartRelativeHomology_isZero_of_lt k E.fibre e r hr

end HodgeLean.Foundations.BundleResolution

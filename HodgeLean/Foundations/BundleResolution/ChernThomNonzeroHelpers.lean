import HodgeLean.Foundations.BundleResolution.ChernDefs
import HodgeLean.Foundations.BundleThom.Thom
import HodgeLean.Foundations.BundleThom.ThomChartFibreHelpers

/-! # Nonzero normalized normal and bundle Thom classes

The prescribed normal coclass evaluates to one on the actual normal class.
Actual chart-fibre restriction detects the selected bundle Thom class.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory Bundle TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

theorem i1_normalizedPointCoclass_ne_zero (k : ℕ) : normalizedPointCoclass k ≠ 0 := by
  intro hz
  have h := normalizedRelativeCoclass_pairing_self (standardComplexLocalClass ℚ k)
    (standardComplexLocalClass_ne_zero_for_chart k)
  change relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ k) (2 * k)
    (normalizedPointCoclass k) (standardComplexLocalClass ℚ k) = 1 at h
  rw [hz, map_zero, LinearMap.zero_apply] at h
  exact zero_ne_one h

theorem i1_complexBundleThom_ne_zero {B : Type} [TopologicalSpace B]
    [CompactSpace B] [T2Space B] [Nonempty B] {k : ℕ} (E : I1ComplexBundle B k) :
    i1_bundleThom k E.fibre ≠ 0 := by
  let b : B := Classical.choice inferInstance
  let e := trivializationAt (Fin k → ℂ) E.fibre b
  haveI : e.IsLinear ℂ := by
    dsimp [e]
    infer_instance
  have hb : b ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  intro hu
  have hnorm : relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E.fibre e)
      (i1_bundleThom k E.fibre) = i1_chartOrientation k E.fibre e :=
    Classical.choose_spec (i1_bundleThom_exists_unique k E.fibre).exists e inferInstance
  rw [hu, map_zero] at hnorm
  have hf := i1_chartOrientation_fibre k E.fibre e b hb
  rw [← hnorm, map_zero] at hf
  exact i1_normalizedPointCoclass_ne_zero k hf.symm

end HodgeLean.Foundations.BundleResolution

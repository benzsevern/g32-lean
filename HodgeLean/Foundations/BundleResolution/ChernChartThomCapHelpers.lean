import HodgeLean.Foundations.BundleResolution.ChernChartThomMultiplicationHelpers

/-! # Actual chart cap maps to base homology

Cap with the specified chart orientation followed by the actual base
projection is dual to chart Thom multiplication.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Bundle TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] {k : ℕ} (E : I1ComplexBundle B k)
variable (e : Trivialization (Fin k → ℂ)
  (TotalSpace.proj : TotalSpace (Fin k → ℂ) E.fibre → B)) [e.IsLinear ℂ]

def i1_chartThomCapToBase (n : ℕ) :
    RelativeHomology ℚ (i1_chartPair k E.fibre e) (2 * k + n) →ₗ[ℚ]
      Homology ℚ (TopCat.of e.baseSet) n :=
  (homologyMap ℚ n (i1_chartBaseProjection E e)).comp
    (relativeCapCohomologyLinear ℚ (i1_chartPair k E.fibre e) (2 * k) n
      (i1_chartOrientation k E.fibre e))

theorem i1_chartThomCapToBase_pairing (n : ℕ)
    (α : Cohomology ℚ (TopCat.of e.baseSet) n)
    (z : RelativeHomology ℚ (i1_chartPair k E.fibre e) (2 * k + n)) :
    relativeCohomologyEquivDualHomology ℚ (i1_chartPair k E.fibre e) (2 * k + n)
      (i1_chartThomMultiplication E e n α) z =
    cohomologyEquivDualHomology ℚ (TopCat.of e.baseSet) n α
      (i1_chartThomCapToBase E e n z) := by
  simp only [i1_chartThomMultiplication, LinearMap.comp_apply,
    i1_relativeCup_pairing, cohomologyEquivDualHomology_cohomologyMap,
    LinearMap.dualMap_apply, i1_chartThomCapToBase]

theorem i1_chartThomCapToBase_bijective (n : ℕ) :
    Function.Bijective (i1_chartThomCapToBase E e n) := by
  apply LinearMap.dualMap_bijective_iff.mp
  let a := cohomologyEquivDualHomology ℚ (TopCat.of e.baseSet) n
  let b := relativeCohomologyEquivDualHomology ℚ
    (i1_chartPair k E.fibre e) (2 * k + n)
  have h : (i1_chartThomCapToBase E e n).dualMap =
      b.toLinearMap.comp ((i1_chartThomMultiplication E e n).comp a.symm.toLinearMap) := by
    ext α z
    have h := (i1_chartThomCapToBase_pairing E e n (a.symm α) z).symm
    simp only [show cohomologyEquivDualHomology ℚ (TopCat.of e.baseSet) n = a from rfl,
      LinearEquiv.apply_symm_apply] at h
    exact h
  rw [h]
  exact b.bijective.comp ((i1_chartThomMultiplication_bijective E e n).comp a.symm.bijective)

end HodgeLean.Foundations.BundleResolution

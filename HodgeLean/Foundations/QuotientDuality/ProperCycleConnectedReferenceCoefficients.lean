import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedLocalCoefficients

/-! # Original top classes compared with an actual nonvanishing reference class
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- On a connected chart-covered region, every original ordinary top class is a single rational multiple of the original local values of a nonvanishing ordinary reference class.
Source: properCycle_chart_local_scalar; IsLocallyConstant.exists_eq_const.
HC no distance; AV milestone no distance. -/
lemma properCycle_connected_reference_coefficients
    (X Y : TopCat.{0}) [T2Space X] [PreconnectedSpace Y] (j : Y ⟶ X) (d : ℕ)
    (hcharts : ∀ y : Y, ∃ e : OpenPartialHomeomorph X (Fin d → ℂ), j y ∈ e.source)
    (b : Homology ℚ X (2*d)) (hb : ∀ y : Y, localOrientation X (2*d) b (j y) ≠ 0)
    (c : Homology ℚ X (2*d)) :
    ∃ q : ℚ, ∀ y : Y, localOrientation X (2*d) c (j y) =
      q • localOrientation X (2*d) b (j y) := by
  classical
  have hex (y : Y) : ∃ q : ℚ,
      q • localOrientation X (2*d) b (j y) = localOrientation X (2*d) c (j y) := by
    obtain ⟨e, hy⟩ := hcharts y
    obtain ⟨U, hyU, hU, q, hq⟩ := properCycle_chart_local_scalar X d e c (j y) hy
    obtain ⟨V, hyV, hV, r, hr⟩ := properCycle_chart_local_scalar X d e b (j y) hy
    have hr0 : r ≠ 0 := by
      intro hz
      apply hb y
      exact (hr (j y) hyV).trans (by rw [hz, zero_smul])
    refine ⟨q/r, ?_⟩
    rw [hr (j y) hyV, smul_smul, div_mul_cancel₀ _ hr0]
    exact (hq (j y) hyU).symm
  let a : Y → ℚ := fun y => (hex y).choose
  have ha (y : Y) : a y • localOrientation X (2*d) b (j y) =
      localOrientation X (2*d) c (j y) := (hex y).choose_spec
  have hlc : IsLocallyConstant a := by
    apply (IsLocallyConstant.iff_exists_open a).mpr
    intro y
    obtain ⟨e, hy⟩ := hcharts y
    obtain ⟨U, hyU, hU, q, hq⟩ := properCycle_chart_local_scalar X d e c (j y) hy
    obtain ⟨V, hyV, hV, r, hr⟩ := properCycle_chart_local_scalar X d e b (j y) hy
    have hr0 : r ≠ 0 := by
      intro hz
      apply hb y
      exact (hr (j y) hyV).trans (by rw [hz, zero_smul])
    have hprod (z : Y) (hzU : j z ∈ U) (hzV : j z ∈ V) : a z * r = q := by
      apply smul_left_injective ℚ (localClassOfChart_ne_zero d e (j z) (hU hzU))
      dsimp only
      rw [mul_smul, ← hr (j z) hzV, ha z, hq (j z) hzU]
    refine ⟨j ⁻¹' ((U : Set X) ∩ V), (U.isOpen.inter V.isOpen).preimage j.hom.continuous,
      ⟨hyU, hyV⟩, ?_⟩
    rintro z ⟨hzU, hzV⟩
    exact mul_right_cancel₀ hr0 ((hprod z hzU hzV).trans (hprod y hyU hyV).symm)
  obtain ⟨q, hq⟩ := hlc.exists_eq_const
  refine ⟨q, ?_⟩
  intro y
  simpa only [hq, Function.const_apply] using (ha y).symm

end HodgeLean.Foundations.QuotientDuality

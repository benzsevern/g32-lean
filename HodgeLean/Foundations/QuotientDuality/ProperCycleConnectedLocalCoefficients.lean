import HodgeLean.Foundations.QuotientDuality.ProperCycleChartLocalScalar
import Mathlib.Topology.LocallyConstant.Basic

/-! # Original top class coefficients on a connected charted open region -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- A geometrically chart-coherent family of local generators on a connected region measures every original ordinary top class by a single rational coefficient.
Source: properCycle_chart_local_scalar; IsLocallyConstant.exists_eq_const.
HC no distance; AV milestone no distance. -/
theorem properCycle_connected_local_coefficients
    (X Y : TopCat.{0}) [T2Space X] [PreconnectedSpace Y] (j : Y ⟶ X) (d : ℕ)
    (μ : ∀ y : Y, orientationGroup X (2*d) (j y))
    (hgen : ∀ y : Y, Function.Bijective (LinearMap.toSpanSingleton ℚ _ (μ y)))
    (hcoh : ∀ y : Y, ∃ V : Opens Y, y ∈ V ∧
      ∃ e : OpenPartialHomeomorph X (Fin d → ℂ),
        ∃ hV : (V : Set Y) ⊆ j ⁻¹' e.source,
          ∀ (z : Y) (hz : z ∈ V), μ z = localClassOfChart d e (j z) (hV hz))
    (c : Homology ℚ X (2*d)) :
    ∃ q : ℚ, ∀ y : Y, localOrientation X (2*d) c (j y) = q • μ y := by
  classical
  let a : Y → ℚ := fun y => Classical.choose ((hgen y).surjective (localOrientation X (2*d) c (j y)))
  have ha (y : Y) : a y • μ y = localOrientation X (2*d) c (j y) :=
    Classical.choose_spec ((hgen y).surjective (localOrientation X (2*d) c (j y)))
  have hlc : IsLocallyConstant a := by
    apply (IsLocallyConstant.iff_exists_open a).mpr
    intro y
    obtain ⟨V, hyV, e, hV, hμ⟩ := hcoh y
    obtain ⟨W, hyW, hW, q, hq⟩ := properCycle_chart_local_scalar X d e c (j y) (hV hyV)
    have hs (z : Y) (hzV : z ∈ V) (hzW : j z ∈ W) : a z = q := by
      apply (hgen z).injective
      change a z • μ z = q • μ z
      rw [ha, hμ z hzV]
      exact hq (j z) hzW
    refine ⟨(V : Set Y) ∩ j ⁻¹' (W : Set X),
      V.isOpen.inter (W.isOpen.preimage j.hom.continuous), ⟨hyV, hyW⟩, ?_⟩
    rintro z ⟨hzV, hzW⟩
    exact (hs z hzV hzW).trans (hs y hyV hyW).symm
  obtain ⟨q, hq⟩ := hlc.exists_eq_const
  refine ⟨q, ?_⟩
  intro y
  simpa only [hq, Function.const_apply] using (ha y).symm

end HodgeLean.Foundations.QuotientDuality

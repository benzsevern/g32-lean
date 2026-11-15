import HodgeLean.Foundations.QuotientDuality.ProperCycleFiniteFibreChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalChartTransport

/-! # Original complex orientation transport on actual finite local sheets -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual finite-fibre point map preserves the original complex orientation for a chart pulled back along an actual local sheet.
Source: Hatcher, Algebraic Topology, section 3.3, complex orientations and local degree.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_sheet_chart_orientation
    {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) [DecidableEq (f ⁻¹' {y})]
    (x : f ⁻¹' {y}) (d : ℕ) (H : OpenPartialHomeomorph X Y)
    (hH : ∀ z : X, f z = H z) (hx : x.val ∈ H.source)
    (e : OpenPartialHomeomorph Y (Fin d → ℂ)) (he : e.source ⊆ H.target)
    (hy : y ∈ e.source) :
    properCycle_finite_fibre_point_pushforward f y hfinite (2 * d) x
      (localClassOfChart d (H.trans e) x.val
        (show x.val ∈ (H.trans e).source from ⟨hx, by
          change H x.val ∈ e.source
          rw [show H x.val = y from (hH x.val).symm.trans x.property]
          exact hy⟩)) =
      localClassOfChart d e y hy := by
  have hxy : H x.val = y := (hH x.val).symm.trans x.property
  have hxe : H x.val ∈ e.source := hxy.symm ▸ hy
  apply properCycle_finite_fibre_point_pushforward_chart f y hfinite x d
    (H.trans e) ⟨hx, hxe⟩ e hy
  · intro z hz hf
    apply H.injOn hz.1 hx
    exact ((hH z).symm.trans hf).trans hxy.symm
  · intro t
    rw [hH]
    simpa only [hxy] using properCycle_chart_model_local_transport d H e he x.val hx hxe t

end HodgeLean.Foundations.QuotientDuality

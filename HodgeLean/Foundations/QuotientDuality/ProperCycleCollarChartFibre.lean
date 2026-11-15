import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartPointValues

/-! # Literal retraction fibres detected by original tangential chart coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- In the original flattened chart, zero tangential coordinate of the actual collar point map detects precisely its literal retraction fibre.
Source: ProperCycleSupportCollar.chart_retraction_point_pair_value; OpenPartialHomeomorph.injOn.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_retraction_tangent_zero_iff
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : TopCat.{0})
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) (x : W) :
    ((TopPair.Hom.fst
      (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter)) x).1 = 0 ↔
      C.retraction ⟨x.val, hWN x.property⟩ = z := by
  rw [C.chart_retraction_point_pair_value E Y e W hWe hWN hR y hflat z hzW hcenter x]
  constructor
  · intro ht
    apply Subtype.ext
    apply e.injOn (hR x.val x.property) (hWe hzW)
    rw [hcenter]
    apply Prod.ext ht
    exact (hflat _ (hR x.val x.property)).mp (C.retraction ⟨x.val, hWN x.property⟩).property
  · intro he
    rw [he, hcenter]

end HodgeLean.Foundations.QuotientDuality

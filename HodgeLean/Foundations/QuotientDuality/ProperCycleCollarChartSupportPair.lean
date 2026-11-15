import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartTriad
import HodgeLean.Foundations.QuotientDuality.ProperCycleFlatSupportPointPair

/-! # The actual collar retraction into the original support chart point pair
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Restriction of the literal collar retraction maps its actual fibre complement into the original support-chart point pair.
Source: ProperCycleSupportCollar.retraction; TopPair.ofSubsetHom.
HC no distance; AV milestone no distance. -/
def ProperCycleSupportCollar.chart_support_point_pair
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    {E Y : Type} [TopologicalSpace E] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (z : S) (hzW : z.val ∈ W) :
    TopPair.ofSubset (X := TopCat.of W)
      ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) ⟶
      pointComplementPair (⟨z, hWe hzW⟩ : {s : S | s.val ∈ e.source}) := by
  let i : TopCat.of W ⟶ TopCat.of C.neighborhood :=
    TopCat.ofHom ⟨fun x => ⟨x.val, hWN x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let r : TopCat.of W ⟶ TopCat.of {s : S | s.val ∈ e.source} :=
    TopCat.ofHom ⟨fun x => ⟨C.retraction (i x), hR x.val x.property⟩,
      (C.retraction.hom.continuous.comp i.hom.continuous).subtype_mk _⟩
  exact TopPair.ofSubsetHom r (by
    intro x hx he
    exact hx (congrArg Subtype.val he))

end HodgeLean.Foundations.QuotientDuality

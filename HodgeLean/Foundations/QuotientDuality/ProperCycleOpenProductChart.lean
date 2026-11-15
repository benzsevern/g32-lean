import HodgeLean.Foundations.QuotientDuality.ProperCycleProductChartCohomology

/-! # Original partial charts from actual open neighborhood homeomorphisms
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual open-neighborhood homeomorphism gives a full-target partial chart with precisely that original neighborhood as source and its literal values on the neighborhood.
Source: IsOpenEmbedding.toOpenPartialHomeomorph; OpenPartialHomeomorph.trans.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_neighborhood_partial_chart
    (X : TopCat.{0}) (U : Opens X) [Nonempty U]
    (Z : Type) [TopologicalSpace Z] (e : U ≃ₜ Z) :
    ∃ b : OpenPartialHomeomorph X Z,
      b.source = (U : Set X) ∧ b.target = Set.univ ∧ ∀ u : U, b u.val = e u := by
  let i : U → X := Subtype.val
  have hi : IsOpenEmbedding i := U.isOpen.isOpenEmbedding_subtypeVal
  let a := hi.toOpenPartialHomeomorph i
  let b := a.symm.trans e.toOpenPartialHomeomorph
  refine ⟨b, ?_, ?_, ?_⟩
  · change a.target ∩ a.symm ⁻¹' Set.univ = (U : Set X)
    rw [Set.preimage_univ, Set.inter_univ]
    rw [show a.target = Set.range i from hi.toOpenPartialHomeomorph_target i]
    ext x
    simp only [i, Subtype.range_coe_subtype, Set.mem_setOf_eq]
    rfl
  · change Set.univ ∩ e.symm ⁻¹' a.source = Set.univ
    rw [show a.source = Set.univ from hi.toOpenPartialHomeomorph_source i,
      Set.preimage_univ, Set.inter_univ]
  · intro u
    change e (a.symm (a u)) = e u
    rw [a.left_inv (show u ∈ a.source from by
      rw [show a.source = Set.univ from hi.toOpenPartialHomeomorph_source i]
      trivial)]

end HodgeLean.Foundations.QuotientDuality

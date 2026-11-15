import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexOriginalCap
import Mathlib.Topology.Connected.Basic

/-! # Actual singular small chains on disjoint open subspaces -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- A singular simplex contained in the union of disjoint open subspaces lies in one of them, so their actual singular subcomplexes have the literal union.
Source: Hatcher, Algebraic Topology, section 2.2, small singular chains; Munkres, Topology, section 23, connected images.
HC no distance; AV milestone no distance. -/
lemma properCycle_disjoint_open_singular_union
    (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) :
    subsetSingularSubcomplex X (U ∪ V) = subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V := by
  ext n s
  change s ∈ (subsetSingularSubcomplex X (U ∪ V)).obj n ↔
    s ∈ (subsetSingularSubcomplex X U).obj n ∨ s ∈ (subsetSingularSubcomplex X V).obj n
  simp only [mem_subsetSingularSubcomplex_iff]
  constructor
  · intro hs
    have hr : IsPreconnected (Set.range (X.toSSetObjEquiv n s)) :=
      isPreconnected_range (X.toSSetObjEquiv n s).continuous
    have hc : Set.range (X.toSSetObjEquiv n s) ⊆ U ∪ V := by
      rintro _ ⟨t, rfl⟩
      exact hs t
    rcases hr.subset_or_subset hU hV hUV hc with h | h
    · exact Or.inl (fun t => h (Set.mem_range_self t))
    · exact Or.inr (fun t => h (Set.mem_range_self t))
  · rintro (h | h) t
    · exact Or.inl (h t)
    · exact Or.inr (h t)

end HodgeLean.Foundations.QuotientDuality

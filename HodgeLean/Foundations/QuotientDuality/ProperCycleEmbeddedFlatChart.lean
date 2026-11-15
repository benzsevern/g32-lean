import HodgeLean.Foundations.QuotientDuality.ProperCycleFlatSupportEmbedding

/-! # Actual local component charts inherited from flattened supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual embedded component that contains an open piece of a flattened support inherits the literal tangential chart on the preimage of that piece.
Source: properCycle_flat_support_chart_isOpenEmbedding; Topology.IsEmbedding.homeomorphOfSubsetRange.
HC no distance; AV milestone no distance. -/
lemma properCycle_embedded_flat_chart
    (X Z : TopCat.{0}) (S : Set X) {E Y : Type} [TopologicalSpace E] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (y : Y)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (f : Z ⟶ TopCat.of S) (hf : IsEmbedding f) (O : Opens (TopCat.of S))
    (hOr : (O : Set S) ⊆ Set.range f) (hOe : ∀ s ∈ O, s.val ∈ e.source)
    (z : Z) (hz : f z ∈ O) :
    ∃ c : OpenPartialHomeomorph Z E,
      c.source = f ⁻¹' (O : Set S) ∧
      ∀ u ∈ c.source, c u = (e (f u).val).1 := by
  let U : Opens Z := ⟨f ⁻¹' (O : Set S), O.isOpen.preimage hf.continuous⟩
  let H : U ≃ₜ O := hf.homeomorphOfSubsetRange hOr
  let g : O → {s : S | s.val ∈ e.source} := fun s => ⟨s.val, hOe s.val s.property⟩
  have hg : IsOpenEmbedding g := by
    refine ⟨(IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).mp IsEmbedding.subtypeVal, ?_⟩
    have hr : Set.range g = {s : {s : S | s.val ∈ e.source} | s.val ∈ O} := by
      ext s
      constructor
      · rintro ⟨u, rfl⟩
        exact u.property
      · intro hs
        exact ⟨⟨s.val, hs⟩, Subtype.ext rfl⟩
    rw [hr]
    exact O.isOpen.preimage continuous_subtype_val
  let t : U → E := fun u => (e (H u).val.val).1
  have ht : IsOpenEmbedding t :=
    (properCycle_flat_support_chart_isOpenEmbedding X S e y hflat).comp (hg.comp H.isOpenEmbedding)
  letI : Nonempty U := ⟨⟨z, hz⟩⟩
  let a := U.openPartialHomeomorphSubtypeCoe inferInstance
  let b := ht.toOpenPartialHomeomorph t
  refine ⟨a.symm.trans b, ?_, ?_⟩
  · change a.target ∩ a.symm ⁻¹' b.source = _
    simp only [b, IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]
    exact U.openPartialHomeomorphSubtypeCoe_target inferInstance
  · intro u hu
    have huU : u ∈ (U : Set Z) := by
      have hh := hu.1
      change u ∈ a.target at hh
      simpa only [a, Opens.openPartialHomeomorphSubtypeCoe_target] using hh
    have hi : (a.symm u).val = u := by
      have hh := a.right_inv (show u ∈ a.target by simpa only [a, Opens.openPartialHomeomorphSubtypeCoe_target] using huU)
      exact hh
    change t (a.symm u) = (e (f u).val).1
    change (e (f (a.symm u).val).val).1 = _
    rw [hi]

end HodgeLean.Foundations.QuotientDuality

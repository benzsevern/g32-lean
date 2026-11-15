import HodgeLean.Foundations.Program.SchoenTowerHardt6RbClosedSelectionSubcomplex

/-! Compatible relatively closed target marks determine actual source subcomplexes. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_closed_mark_subcomplex {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace F]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (A M : Set F) (h : K.space ≃ₜ A)
    (hclosed : IsClosed (Subtype.val ⁻¹' M : Set A))
    (S : Finset (Finset E)) (hS : (↑S : Set _) ⊆ K.faces)
    (hsel : A ∩ M = (fun x : K.space => (h x).val) ''
      {x : K.space | ∃ s ∈ S, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))}) :
    ∃ D : Geometry.SimplicialComplex ℝ E, D.faces.Finite ∧ D.faces ⊆ K.faces ∧
      (∀ x : K.space, (h x).val ∈ M ↔ x.val ∈ D.space) := by
  have hcompact : IsCompact K.space :=
    hK.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp hcompact
  let U : Set K.space := {x | (h x).val ∈ M}
  let C : Set E := Subtype.val '' U
  have hU : IsClosed U := hclosed.preimage h.continuous
  have hC : IsClosed C := (hU.isCompact.image continuous_subtype_val).isClosed
  have hsource : ∀ x ∈ K.space, x ∈ C ↔
      ∃ s ∈ S, x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set E)) := by
    intro x hxK
    let a : K.space := ⟨x, hxK⟩
    constructor
    · rintro ⟨u, hu, hux⟩
      have hua : u = a := Subtype.ext hux
      have haM : (h a).val ∈ M := hua ▸ hu
      have him : (h a).val ∈ (fun x : K.space => (h x).val) ''
          {x : K.space | ∃ s ∈ S, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))} :=
        hsel ▸ ⟨(h a).property, haM⟩
      obtain ⟨v, hv, hva⟩ := him
      have hva' : v = a := h.injective (Subtype.ext hva)
      change ∃ s ∈ S, a.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))
      exact hva' ▸ hv
    · intro hxS
      have him : (h a).val ∈ A ∩ M := hsel.symm ▸ Set.mem_image_of_mem _ hxS
      exact ⟨a, him.2, rfl⟩
  obtain ⟨D, hD, hDK, hspace, _⟩ := s2v_hardt6rb_closed_selection_subcomplex K hK C hC S hS hsource
  refine ⟨D, hD, hDK, ?_⟩
  intro x
  constructor
  · intro hxM
    rw [hspace]
    exact ⟨x.property, ⟨x, hxM, rfl⟩⟩
  · intro hxD
    have hxC : x.val ∈ C := ((Set.ext_iff.mp hspace x.val).mp hxD).2
    obtain ⟨y, hy, hyx⟩ := hxC
    have he : y = x := Subtype.ext hyx
    exact he ▸ hy

end HodgeLean.Foundations.Program

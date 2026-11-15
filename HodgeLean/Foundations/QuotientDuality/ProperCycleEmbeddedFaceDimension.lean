import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexChartDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodEmbedding

/-! # Actual chart dimensions on marks of embedded finite models -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular Topology TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- A complex chart on an actual marked subspace bounds every model face through a point in the ambient neighborhood image.
Source: Hatcher, Algebraic Topology, section 2.2, excision and local dimension;
Munkres, Elements of Algebraic Topology, section 2.
HC no distance; AV milestone no distance. -/
lemma properCycle_embedded_mark_face_card_le_of_complex_chart {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K L : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (X : TopCat.{0}) [T1Space X] (f : K.space → X) (hf : IsEmbedding f)
    (S : Set X) (hmark : ∀ z : K.space, f z ∈ S ↔ z.val ∈ L.space)
    (s : Finset E) (hs : s ∈ L.faces) (x : K.space)
    (hxs : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hnb : Set.range f ∈ 𝓝 (f x))
    (d : ℕ) (φ : OpenPartialHomeomorph S (Fin d → ℂ))
    (hφ : (⟨f x, (hmark x).mpr (L.convexHull_subset_space hs (intrinsicInterior_subset hxs))⟩ : S) ∈ φ.source) :
    s.card ≤ 2 * d + 1 := by
  have hspace : L.space ⊆ K.space := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hz
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨t, hLK ht, hzt⟩
  let T : Set K.space := {z | z.val ∈ L.space}
  let e : T ≃ₜ L.space :=
    { toFun := fun z => ⟨z.val.val, z.property⟩
      invFun := fun z => ⟨⟨z.val, hspace z.property⟩, z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  let y : T := ⟨x, L.convexHull_subset_space hs (intrinsicInterior_subset hxs)⟩
  let H := (properCycle_local_homology_homeomorph_iso
      (X := TopCat.of T) (Y := TopCat.of L.space) e y (2 * d)).symm ≪≫
    properCycle_marked_embedding_local_homology_iso (TopCat.of K.space) X f hf T S hmark y hnb (2 * d)
  let c := localClassOfChart d φ ⟨f x, (hmark x).mpr y.property⟩ hφ
  have hc : c ≠ 0 := localClassOfChart_ne_zero d φ _ hφ
  have hsource : H.inv c ≠ 0 := by
    intro hz
    have hh := congrArg H.hom hz
    rw [H.inv_hom_id_apply, map_zero] at hh
    exact hc hh
  have hL : L.faces.Finite := hK.subset hLK
  have hVL : ∀ a ∈ L.vertices, a ∈ V := fun a ha => hV a (hLK ha)
  exact properCycle_geometric_face_card_le_of_local_ne_zero L hL V hVL s hs (e y) hxs
    (2 * d) (H.inv c) hsource

end HodgeLean.Foundations.QuotientDuality

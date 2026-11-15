import HodgeLean.Foundations.QuotientDuality.ProperCycleProductDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexCofinalChart

/-! # Actual triangulation dimension bounds detected by local orientation groups -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- A nonzero actual local class bounds the vertex cardinality of its intrinsic open face.
Source: Hatcher, Algebraic Topology, section 2.2; Munkres, Elements of Algebraic Topology, section 2.
HC no distance; AV milestone no distance. -/
lemma properCycle_geometric_face_card_le_of_local_ne_zero {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (s : Finset E) (hs : s ∈ K.faces) (x : K.space)
    (hx : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (N : ℕ) (c : orientationGroup (TopCat.of K.space) N x) (hc : c ≠ 0) :
    s.card ≤ N + 1 := by
  obtain ⟨j, W, Y, y, e, _, hxW, hdim, _⟩ :=
    properCycle_geometric_face_cofinal_charts K hK V hV s hs x hx ⊤ trivial
  have hd := properCycle_chart_dimension_le_of_local_ne_zero (TopCat.of K.space) W
    (properCycle_log_tangent j) Y e ⟨x, hxW⟩ N c hc
  omega

/-- Nonzero local homology of the original space bounds every face of its actual finite triangulation.
Source: Hatcher, Algebraic Topology, section 2.2, local homology and invariance of dimension;
Munkres, Elements of Algebraic Topology, section 2, finite geometric complexes.
HC no distance; AV milestone no distance. -/
lemma properCycle_triangulation_face_card_bound {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (X : TopCat.{0}) (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (e : K.space ≃ₜ X) (N : ℕ)
    (hlocal : ∀ x : X, ∃ c : orientationGroup X N x, c ≠ 0) :
    ∀ s ∈ K.faces, s.card ≤ N + 1 := by
  intro s hs
  obtain ⟨a, ha⟩ := K.nonempty_of_mem_faces hs
  have hne : (convexHull ℝ (s : Set E)).Nonempty :=
    ⟨a, subset_convexHull ℝ _ ha⟩
  obtain ⟨x0, hx0⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (s : Set E)) hne
  let x : K.space := ⟨x0, K.convexHull_subset_space hs (intrinsicInterior_subset hx0)⟩
  obtain ⟨c, hc⟩ := hlocal (e x)
  let H := properCycle_local_homology_homeomorph_iso (X := TopCat.of K.space) (Y := X) e x N
  have hsource : H.inv c ≠ 0 := by
    intro hz
    have hh := congrArg H.hom hz
    rw [H.inv_hom_id_apply, map_zero] at hh
    exact hc hh
  exact properCycle_geometric_face_card_le_of_local_ne_zero K hK V hV s hs x hx0 N (H.inv c) hsource

/-- The frozen orientation-line bijectivity input gives a nonzero actual local class at every point.
Source: Hatcher, Algebraic Topology, section 3.3, generators of local homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_local_orientation_ne_zero
    (X : TopCat.{0}) (N : ℕ) (c : Homology ℚ X N) (x : X)
    (hlocal : Function.Bijective (orientationLine X N c x)) : localOrientation X N c x ≠ 0 := by
  intro hz
  have he : orientationLine X N c x 1 = orientationLine X N c x 0 := by
    change (1 : ℚ) • localOrientation X N c x = (0 : ℚ) • localOrientation X N c x
    rw [hz, smul_zero, smul_zero]
  exact one_ne_zero (hlocal.1 he)

/-- A specified actual orientation class bounds all faces of an actual finite triangulation.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3; Munkres, Elements of Algebraic Topology, section 2.
HC no distance; AV milestone no distance. -/
lemma properCycle_oriented_triangulation_face_card_bound {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (X : TopCat.{0}) (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V) (e : K.space ≃ₜ X)
    (N : ℕ) (c : Homology ℚ X N)
    (hlocal : ∀ x : X, Function.Bijective (orientationLine X N c x)) :
    ∀ s ∈ K.faces, s.card ≤ N + 1 := by
  apply properCycle_triangulation_face_card_bound X K hK V hV e N
  intro x
  exact ⟨localOrientation X N c x, properCycle_local_orientation_ne_zero X N c x (hlocal x)⟩

end HodgeLean.Foundations.QuotientDuality

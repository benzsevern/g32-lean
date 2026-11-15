import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveDimensionTriangulation

/-! # Original projective triangulations retaining dimension-bounded algebraic supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Topology TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- An original algebraic closed support has a marked finite projective triangulation whose support faces retain twice its intrinsic complex dimension as their real dimension bound.
Source: properCycle_projective_marked_triangulation; properCycle_reduced_mark_chart_cover; properCycle_embedded_mark_face_card_le_of_complex_chart.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_support_dimension_triangulation
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] [LocallyOfFiniteType X.hom]
    [NoetherianSpace X.left] (S : Closeds X.left) (d : ℕ) (hdim : topologicalKrullDim S ≤ d) :
    ∃ a : ℕ, ∃ K D : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)),
      K.faces.Finite ∧ D.faces.Finite ∧ D.faces ⊆ K.faces ∧
      ∃ h : K.space ≃ₜ ComplexPoint X,
        (∀ z : K.space, (h z).underlying ∈ S ↔ z.val ∈ D.space) ∧
        ∀ s ∈ D.faces, s.card ≤ 2*d+1 := by
  classical
  let l := (reducedSmoothStratification X.hom S).length
  let Z : Fin (l+1) → Over (Spec ↧ℂ) := fun j =>
    Over.mk (reducedClosedStructureMap X.hom (reducedSmoothClosedFiltration X.hom S j.val))
  let i : ∀ j, Z j ⟶ X := fun j =>
    properCycle_reduced_closed_map X (reducedSmoothClosedFiltration X.hom S j.val)
  letI (j : Fin (l+1)) : IsClosedImmersion (i j).left := by dsimp [i]; infer_instance
  obtain ⟨a, K, hK, h, hmarks⟩ := properCycle_projective_marked_triangulation X Z i
  letI : LinearOrder (EuclideanSpace ℝ (Fin a)) := IsWellOrder.linearOrder WellOrderingRel
  have hvfinite : K.vertices.Finite :=
    Set.Finite.preimage (fun _ _ _ _ he => Finset.singleton_injective he) hK
  let V := hvfinite.toFinset
  have hV : ∀ b ∈ K.vertices, b ∈ V := fun b hb => hvfinite.mem_toFinset.mpr hb
  have hrange (j : Fin (l+1)) : Set.range (Point.map (i j)) =
      Point.underlying ⁻¹' (reducedSmoothClosedFiltration X.hom S j.val : Set X.left) := by
    rw [range_map_of_closedImmersion]
    change {z : ComplexPoint X | z.underlying ∈ Set.range (reducedClosedSubschemeι _)} = _
    rw [range_reducedClosedSubschemeι]
    rfl
  let j0 : Fin (l+1) := ⟨0, by omega⟩
  obtain ⟨D, hD, hDK, hDmark⟩ := hmarks j0
  have hmark : ∀ z : K.space, (h z).underlying ∈ S ↔ z.val ∈ D.space := by
    intro z
    have hh := hDmark z
    rw [hrange j0] at hh
    exact hh
  refine ⟨a, K, D, hK, hD, hDK, h, hmark, ?_⟩
  intro s hs
  have hsK := hDK hs
  have hne : (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a)))).Nonempty :=
    (K.nonempty_of_mem_faces hsK).to_set.mono (subset_convexHull ℝ _)
  obtain ⟨x0, hx0⟩ := Set.Nonempty.intrinsicInterior
    (convex_convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a)))) hne
  let x : K.space := ⟨x0, K.convexHull_subset_space hsK (intrinsicInterior_subset hx0)⟩
  have hxD : x.val ∈ D.space := D.convexHull_subset_space hs (intrinsicInterior_subset hx0)
  obtain ⟨k, hk, m, hm, φ, hxS, hφ⟩ :=
    properCycle_reduced_mark_chart_cover X S d hdim (h x) ((hmark x).mpr hxD)
  let jk : Fin (l+1) := ⟨k, by change k < l at hk; omega⟩
  obtain ⟨L, _, hLK, hLmark⟩ := hmarks jk
  have hxL : x.val ∈ L.space := (hLmark x).mp hxS
  have hsL : s ∈ L.faces :=
    (s2v_hardt6rb_open_face_mem_subcomplex_iff K L hLK s hsK hx0).mp hxL
  have hnb : Set.range h ∈ 𝓝 (h x) := by rw [h.surjective.range_eq]; exact Filter.univ_mem
  have hc := properCycle_embedded_mark_face_card_le_of_complex_chart K L hK hLK V hV
    (TopCat.of (ComplexPoint X)) h h.isEmbedding _ hLmark s hsL x hx0 hnb m φ hφ
  omega

end HodgeLean.Foundations.QuotientDuality

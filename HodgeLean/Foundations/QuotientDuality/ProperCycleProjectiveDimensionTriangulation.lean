import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMarkedTriangulation
import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedMarkCharts
import HodgeLean.Foundations.QuotientDuality.ProperCycleEmbeddedFaceDimension
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceSubcomplex

/-! # Actual global projective triangulations bounded by intrinsic complex dimension -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Topology TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The original projective complex point space has a finite global triangulation with every actual face bounded by twice its intrinsic algebraic dimension.
Source: properCycle_projective_marked_triangulation; properCycle_reduced_mark_chart_cover; properCycle_embedded_mark_face_card_le_of_complex_chart.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_dimension_triangulation
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] [LocallyOfFiniteType X.hom]
    [NoetherianSpace X.left] (d : ℕ) (hdim : topologicalKrullDim X.left ≤ d) :
    ∃ a : ℕ, ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)),
      K.faces.Finite ∧ Nonempty (K.space ≃ₜ ComplexPoint X) ∧
        ∀ s ∈ K.faces, s.card ≤ 2*d+1 := by
  classical
  let S : Closeds X.left := ⊤
  have hdS : topologicalKrullDim S ≤ d :=
    (topologicalKrullDim_subspace_le X.left (S : Set X.left)).trans hdim
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
  refine ⟨a, K, hK, ⟨h⟩, ?_⟩
  intro s hs
  have hne : (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a)))).Nonempty :=
    (K.nonempty_of_mem_faces hs).to_set.mono (subset_convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a))))
  obtain ⟨x0, hx0⟩ := Set.Nonempty.intrinsicInterior
    (convex_convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a)))) hne
  let x : K.space := ⟨x0, K.convexHull_subset_space hs (intrinsicInterior_subset hx0)⟩
  obtain ⟨k, hk, m, hm, φ, hxS, hφ⟩ :=
    properCycle_reduced_mark_chart_cover X S d hdS (h x) (by trivial)
  let jk : Fin (l+1) := ⟨k, by change k < l at hk; omega⟩
  obtain ⟨L, _, hLK, hLmark⟩ := hmarks jk
  have hxL : x.val ∈ L.space := (hLmark x).mp hxS
  have hsL : s ∈ L.faces :=
    (s2v_hardt6rb_open_face_mem_subcomplex_iff K L hLK s hs hx0).mp hxL
  have hnb : Set.range h ∈ 𝓝 (h x) := by rw [h.surjective.range_eq]; exact Filter.univ_mem
  have hc := properCycle_embedded_mark_face_card_le_of_complex_chart K L hK hLK V hV
    (TopCat.of (ComplexPoint X)) h h.isEmbedding _ hLmark s hsL x hx0 hnb m φ hφ
  omega

end HodgeLean.Foundations.QuotientDuality

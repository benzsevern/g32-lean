import HodgeLean.Foundations.QuotientDuality.ProperCycleCofinalProductChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleFaceDimension
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicPositive

/-! # Cofinal actual product charts along finite geometric faces -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
open TopologicalSpace HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Each intrinsic interior face point has cofinal actual product charts of precisely its real face dimension.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric stars and geometric faces.
HC no distance; AV milestone no distance. -/
lemma properCycle_geometric_face_cofinal_charts {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (s : Finset E) (hs : s ∈ K.faces) (x : K.space)
    (hx : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (P : Opens K.space) (hxP : x ∈ P) :
    let T : Finset V := Finset.univ.filter (fun a => a.val ∈ s)
    ∃ (j : T) (W : Opens K.space) (Y : TopCat.{0}) (y : Y)
      (e : W ≃ₜ (properCycle_log_tangent j × Y)),
      W ≤ P ∧ x ∈ W ∧ Module.finrank ℝ (properCycle_log_tangent j) + 1 = s.card ∧
        ∀ z : W, z.val.val ∈ convexHull ℝ (s : Set E) ↔ (e z).2 = y := by
  classical
  dsimp only
  have hr : Set.range (fun i : s => (i.val : E)) = (s : Set E) := by
    ext z
    simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
  obtain ⟨u, hu⟩ := (s2v_hardt6rb_convexHull_range_weights _ x.val).mp
    (hr.symm ▸ intrinsicInterior_subset hx)
  have hpos : ∀ a : s, 0 < u.val a :=
    s2v_hardt6rb_intrinsicInterior_weights_pos (fun a : s => (a.val : E)) (K.indep hs) u
      (by rw [hu, hr]; exact hx)
  obtain ⟨j, U, Y, y, e, hxU, hmark⟩ :=
    properCycle_geometric_complex_face_chart K hK V hV s hs u hpos x hu
  obtain ⟨W, hWP, hxW, Z, z, f, hf⟩ :=
    properCycle_product_chart_cofinal (TopCat.of K.space)
      {a : K.space | a.val ∈ convexHull ℝ (s : Set E)} U
      (properCycle_log_tangent j) Y y e hmark ⟨x, hxU⟩
      (show x.val ∈ convexHull ℝ (s : Set E) from intrinsicInterior_subset hx) P hxP
  refine ⟨j, W, Z, z, f, hWP, hxW, ?_, hf⟩
  apply properCycle_selected_face_vector_finrank V s ?_ j
  intro a ha
  exact hV a (K.down_closed hs (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty _))

end HodgeLean.Foundations.QuotientDuality

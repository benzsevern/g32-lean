import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexCoordinates

/-! # Geometric faces detected by actual barycentric support -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual geometric face membership is equivalent to vanishing of every barycentric coordinate off that face.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates of geometric complexes.
HC no distance; AV milestone no distance. -/
lemma properCycle_complex_coordinates_face_iff {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) (V : Finset E)
    (W : C(K.space, stdSimplex ℝ V))
    (hrec : ∀ x : K.space, (∑ a : V, (W x).val a • a.val) = x.val)
    (hW : ∀ (s : Finset E) (hs : s ∈ K.faces) (w : stdSimplex ℝ s)
      (x : K.space), (∑ i, w.val i • i.val) = x.val →
      ∀ a : V, (W x).val a = if ha : a.val ∈ s then w.val ⟨a.val, ha⟩ else 0)
    (s : Finset E) (hs : s ∈ K.faces) (x : K.space) :
    x.val ∈ convexHull ℝ (s : Set E) ↔ ∀ a : V, a.val ∉ s → (W x).val a = 0 := by
  constructor
  · intro hx
    have hr : Set.range (fun i : s => (i.val : E)) = (s : Set E) := by
      ext z
      simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
    obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights _ x.val).mp (hr.symm ▸ hx)
    intro a ha
    rw [hW s hs w x hw a, dif_neg ha]
  · intro hx
    rw [← hrec x]
    apply s2v_hardt6rb_supported_convexHull (fun a : V => a.val) (W x) (s : Set E)
    intro a ha
    by_contra has
    exact ha (hx a has)

end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairBarycentricInverse
import HodgeLean.Foundations.QuotientDuality.ProperCycleBarycentricMarkedChart

/-! # Actual finite geometric complexes in their barycentric coordinate carriers -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
open HodgeLean.Foundations.Program
open Semialgebraic.CompatibleTriangulation.Helpers
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual geometric complex is homeomorphic to its carrier of simplex-supported barycentric weights.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates of a geometric complex.
HC no distance; AV milestone no distance. -/
def properCycle_complex_weight_homeomorph {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) (V : Finset E)
    (hV : ∀ a ∈ K.vertices, a ∈ V)
    (W : C(K.space, stdSimplex ℝ V))
    (hrec : ∀ x : K.space, (∑ a : V, (W x).val a • a.val) = x.val)
    (hW : ∀ (s : Finset E) (hs : s ∈ K.faces) (w : stdSimplex ℝ s)
      (x : K.space), (∑ i, w.val i • i.val) = x.val →
      ∀ a : V, (W x).val a = if ha : a.val ∈ s then w.val ⟨a.val, ha⟩ else 0) :
    K.space ≃ₜ {w : stdSimplex ℝ V | ∃ s ∈ K.faces, ∀ a : V, a.val ∉ s → w.val a = 0} := by
  classical
  have hsV (s : Finset E) (hs : s ∈ K.faces) : s ⊆ V := by
    intro a ha
    exact hV a (K.down_closed hs (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty _))
  have hcar (x : K.space) : ∃ s ∈ K.faces, ∀ a : V, a.val ∉ s → (W x).val a = 0 := by
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp x.property
    have hr : Set.range (fun i : s => (i.val : E)) = (s : Set E) := by
      ext z
      simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
    obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights _ x.val).mp (hr.symm ▸ hx)
    refine ⟨s, hs, fun a ha => ?_⟩
    rw [hW s hs w x hw a, dif_neg ha]
  have hex (u : {w : stdSimplex ℝ V |
      ∃ s ∈ K.faces, ∀ a : V, a.val ∉ s → w.val a = 0}) :
      ∃ x : K.space, x.val = (∑ a : V, u.val.val a • a.val) ∧ W x = u.val := by
    obtain ⟨s, hs, hu⟩ := u.property
    exact s2e_pair_barycentric_inverse_on_face K V W hW s hs (hsV s hs) u.val hu
  refine
    { toFun := fun x => ⟨W x, hcar x⟩
      invFun := fun u => (hex u).choose
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := W.continuous.subtype_mk _
      continuous_invFun := ?_ }
  · intro x
    apply Subtype.ext
    exact (hex ⟨W x, hcar x⟩).choose_spec.1.trans (hrec x)
  · intro u
    apply Subtype.ext
    exact (hex u).choose_spec.2
  · apply Continuous.subtype_mk
    have hc : Continuous (fun u : {w : stdSimplex ℝ V |
        ∃ s ∈ K.faces, ∀ a : V, a.val ∉ s → w.val a = 0} =>
        (∑ a : V, u.val.val a • a.val)) :=
      continuous_finsetSum Finset.univ (fun a _ =>
        ((continuous_apply a).comp (continuous_subtype_val.comp continuous_subtype_val)).smul
          continuous_const)
    exact hc.congr (fun u => (hex u).choose_spec.1.symm)


/-- Every finite geometric complex has actual barycentric carrier coordinates with the original face formulas.
Source: Munkres, Elements of Algebraic Topology, section 2, finite geometric complexes.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_complex_weight_coordinates {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V) :
    ∃ e : K.space ≃ₜ {w : stdSimplex ℝ V |
        ∃ s ∈ K.faces, ∀ a : V, a.val ∉ s → w.val a = 0},
      (∀ x : K.space, (∑ a : V, (e x).val.val a • a.val) = x.val) ∧
      ∀ (s : Finset E) (hs : s ∈ K.faces) (w : stdSimplex ℝ s)
        (x : K.space), (∑ i, w.val i • i.val) = x.val →
        ∀ a : V, (e x).val.val a = if ha : a.val ∈ s then w.val ⟨a.val, ha⟩ else 0 := by
  obtain ⟨W, hrec, hW⟩ := s2e_pair_barycentric_map K hK V hV
  exact ⟨properCycle_complex_weight_homeomorph K V hV W hrec hW, hrec, hW⟩

end HodgeLean.Foundations.QuotientDuality

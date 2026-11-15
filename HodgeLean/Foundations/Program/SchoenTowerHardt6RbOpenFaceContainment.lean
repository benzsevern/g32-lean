import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicSimplex
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-! Intrinsic open-face incidence recovers exact base-face containment. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_open_face_subset_of_mem_face {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (S T : Finset E)
    (hS : S ∈ K.faces) (hT : T ∈ K.faces) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (↑S : Set E)))
    (hxT : x ∈ convexHull ℝ (↑T : Set E)) : S ⊆ T := by
  classical
  have hrange : Set.range (fun i : S => (i.val : E)) = (↑S : Set E) := by
    ext y
    simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
  have hxR : x ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range (fun i : S => (i.val : E)))) := by
    rw [hrange]
    exact hx
  obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights (fun i : S => (i.val : E)) x).mp
    (intrinsicInterior_subset hxR)
  have hpos := s2v_hardt6rb_intrinsicInterior_weights_pos (fun i : S => i.val) (K.indep hS) w
    (hw.symm ▸ hxR)
  let I : Finset S := Finset.univ.filter (fun i => i.val ∈ T)
  have hI : (fun i : S => i.val) '' (↑I : Set S) = (↑(S ∩ T) : Set E) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact Finset.mem_inter.mpr ⟨i.property, (Finset.mem_filter.mp hi).2⟩
    · intro hy
      obtain ⟨hyS, hyT⟩ := Finset.mem_inter.mp hy
      exact ⟨⟨y, hyS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyT⟩, rfl⟩
  have hmem : (∑ i, w.val i • (i.val : E)) ∈ convexHull ℝ ((fun i : S => i.val) '' (↑I : Set S)) := by
    rw [hw, hI]
    simpa only [Finset.coe_inter] using K.inter_subset_convexHull hS hT ⟨intrinsicInterior_subset hx, hxT⟩
  have hsupport := s2v_hardt6rb_face_weight_support (fun i : S => i.val) (K.indep hS) I w.val w.property.2 hmem
  intro y hy
  by_contra hn
  have hi : (⟨y, hy⟩ : S) ∉ I := fun h => hn (Finset.mem_filter.mp h).2
  have hz := hsupport ⟨y, hy⟩ hi
  have hp := hpos ⟨y, hy⟩
  rw [hz] at hp
  exact lt_irrefl _ hp

end HodgeLean.Foundations.Program

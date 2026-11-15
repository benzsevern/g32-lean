import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexComplex

/-! Common-face intersections descend from maximal simplices to all their faces. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_subface_intersection {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S T s t : Finset E)
    (hS : AffineIndependent ℝ (fun x : S => (x : E)))
    (hT : AffineIndependent ℝ (fun x : T => (x : E)))
    (hs : s ⊆ S) (ht : t ⊆ T)
    (hST : convexHull ℝ (↑S : Set E) ∩ convexHull ℝ (↑T : Set E) ⊆
      convexHull ℝ ((↑S : Set E) ∩ ↑T)) :
    convexHull ℝ (↑s : Set E) ∩ convexHull ℝ (↑t : Set E) ⊆
      convexHull ℝ ((↑s : Set E) ∩ ↑t) := by
  classical
  rintro x ⟨hxs, hxt⟩
  have hxST := hST ⟨convexHull_mono (Finset.coe_subset.mpr hs) hxs,
    convexHull_mono (Finset.coe_subset.mpr ht) hxt⟩
  have hx : x ∈ convexHull ℝ (↑s : Set E) ∩
      convexHull ℝ (↑(S ∩ T) : Set E) := by
    exact ⟨hxs, by simpa only [Finset.coe_inter] using hxST⟩
  rw [← hS.convexHull_inter hs Finset.inter_subset_left] at hx
  have hxsT : x ∈ convexHull ℝ (↑(s ∩ T) : Set E) := by
    simpa only [← Finset.coe_inter, ← Finset.inter_assoc, Finset.inter_eq_left.mpr hs] using hx
  have hx' : x ∈ convexHull ℝ (↑(s ∩ T) : Set E) ∩ convexHull ℝ (↑t : Set E) :=
    ⟨hxsT, hxt⟩
  rw [← hT.convexHull_inter Finset.inter_subset_right ht] at hx'
  simpa only [← Finset.coe_inter, Finset.inter_assoc, Finset.inter_eq_right.mpr ht] using hx'

end HodgeLean.Foundations.Program

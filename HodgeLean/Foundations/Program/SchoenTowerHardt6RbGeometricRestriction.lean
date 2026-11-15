import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOrderedRestriction

/-! Restriction of a lifted simplex face over an actual geometric base face. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_geometric_prism_restriction {E : Type*}
    [AddCommGroup E] [Module ℝ E] [LinearOrder E]
    (s V : Finset E) (hs : AffineIndependent ℝ (fun i : s => i.val))
    (hV : V ⊆ s) (l u : E → ℝ) (j : s) (r : Finset (E × ℝ))
    (hr : (↑r : Set (E × ℝ)) ⊆
      (((fun i : s => (i.val, l i.val)) '' {i | j ≤ i}) ∪
        ((fun i : s => (i.val, u i.val)) '' {i | i ≤ j}))) :
    convexHull ℝ (↑r : Set (E × ℝ)) ∩
        Prod.fst ⁻¹' convexHull ℝ (↑V : Set E) =
      convexHull ℝ ((↑r : Set (E × ℝ)) ∩ Prod.fst ⁻¹' (↑V : Set E)) := by
  classical
  let I : Finset s := Finset.univ.filter (fun i => i.val ∈ V)
  have hI : (fun i : s => i.val) '' (↑I : Set s) = (↑V : Set E) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp hi).2
    · intro hx
      refine ⟨⟨x, hV hx⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have h := s2v_hardt6rb_ordered_prism_restriction (fun i : s => i.val) hs
    (fun i => l i.val) (fun i => u i.val) j I r hr
  rw [hI] at h
  exact h

end HodgeLean.Foundations.Program

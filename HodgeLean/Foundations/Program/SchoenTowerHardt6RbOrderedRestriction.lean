import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOrderedImages
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismSubface

/-! Base-face restriction independently of the chosen finite vertex enumeration. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ordered_prism_restriction {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [LinearOrder ι] [Fintype ι]
    (v : ι → E) (hv : AffineIndependent ℝ v)
    (l u : ι → ℝ) (j : ι) (I : Finset ι) (s : Finset (E × ℝ))
    (hs : (↑s : Set (E × ℝ)) ⊆
      (((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
        ((fun i => (v i, u i)) '' {i | i ≤ j}))) :
    convexHull ℝ (↑s : Set (E × ℝ)) ∩
        Prod.fst ⁻¹' convexHull ℝ (v '' (↑I : Set _)) =
      convexHull ℝ ((↑s : Set (E × ℝ)) ∩
        Prod.fst ⁻¹' (v '' (↑I : Set _))) := by
  classical
  letI : Nonempty ι := ⟨j⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (show Fintype.card ι ≠ 0 from ne_of_gt Fintype.card_pos)
  let e : Fin (m + 1) ≃o ι := Fintype.orderIsoFinOfCardEq ι hm
  let J : Finset (Fin (m + 1)) := I.preimage e e.injective.injOn
  have hI : (v ∘ e) '' (↑J : Set _) = v '' (↑I : Set _) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e i, Finset.mem_preimage.mp hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e.symm i, Finset.mem_preimage.mpr (by simpa using hi), by simp⟩
  have hstair : (↑s : Set (E × ℝ)) ⊆
      (((fun i => ((v ∘ e) i, (l ∘ e) i)) '' {i | e.symm j ≤ i}) ∪
        ((fun i => ((v ∘ e) i, (u ∘ e) i)) '' {i | i ≤ e.symm j})) := by
    change (↑s : Set (E × ℝ)) ⊆
      (((fun i => (v i, l i)) ∘ e) '' {i | e.symm j ≤ i}) ∪
      (((fun i => (v i, u i)) ∘ e) '' {i | i ≤ e.symm j})
    rw [(s2v_hardt6rb_ordered_images e (fun i => (v i, l i)) (e.symm j)).1,
      (s2v_hardt6rb_ordered_images e (fun i => (v i, u i)) (e.symm j)).2,
      e.apply_symm_apply]
    exact hs
  have h := s2v_hardt6rb_prism_subface_restriction (v ∘ e)
    (hv.comp_embedding e.toEquiv.toEmbedding) (l ∘ e) (u ∘ e) (e.symm j) J s hstair
  rw [hI] at h
  exact h

end HodgeLean.Foundations.Program

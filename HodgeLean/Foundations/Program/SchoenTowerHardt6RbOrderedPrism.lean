import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOrderedImages
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismComplex

/-! Staircase complexes indexed by any finite nonempty ordered vertex family. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ordered_prism_complex {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [LinearOrder ι] [Fintype ι] [Nonempty ι]
    (v : ι → E) (hv : AffineIndependent ℝ v)
    (l u : ι → ℝ) (hlu : ∀ i, l i ≤ u i) :
    ∃ K : Geometry.SimplicialComplex ℝ (E × ℝ), K.faces.Finite ∧
      (∀ s, s ∈ K.faces ↔ ∃ j : ι,
        (↑s : Set (E × ℝ)) ⊆
          (((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
            ((fun i => (v i, u i)) '' {i | i ≤ j})) ∧ s.Nonempty) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (show Fintype.card ι ≠ 0 from ne_of_gt Fintype.card_pos)
  let e : Fin (m + 1) ≃o ι := Fintype.orderIsoFinOfCardEq ι hm
  obtain ⟨K, hK, hfaces, _⟩ := s2v_hardt6rb_prism_complex
    (v ∘ e) (hv.comp_embedding e.toEquiv.toEmbedding) (l ∘ e) (u ∘ e)
    (fun i => hlu (e i))
  refine ⟨K, hK, ?_⟩
  intro s
  rw [hfaces]
  constructor
  · rintro ⟨j, hs, hne⟩
    refine ⟨e j, ?_, hne⟩
    have hlo := (s2v_hardt6rb_ordered_images e (fun i => (v i, l i)) j).1
    have hup := (s2v_hardt6rb_ordered_images e (fun i => (v i, u i)) j).2
    change (↑s : Set (E × ℝ)) ⊆
      (((fun i => (v i, l i)) ∘ e) '' {i | j ≤ i}) ∪
      (((fun i => (v i, u i)) ∘ e) '' {i | i ≤ j}) at hs
    rw [hlo, hup] at hs
    exact hs
  · rintro ⟨j, hs, hne⟩
    refine ⟨e.symm j, ?_, hne⟩
    have hlo := (s2v_hardt6rb_ordered_images e (fun i => (v i, l i)) (e.symm j)).1
    have hup := (s2v_hardt6rb_ordered_images e (fun i => (v i, u i)) (e.symm j)).2
    change (↑s : Set (E × ℝ)) ⊆
      (((fun i => (v i, l i)) ∘ e) '' {i | e.symm j ≤ i}) ∪
      (((fun i => (v i, u i)) ∘ e) '' {i | i ≤ e.symm j})
    rw [hlo, hup, e.apply_symm_apply]
    exact hs

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOrderedImages
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismCover

/-! Coverage of a band using the shared order on any finite vertex family. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ordered_prism_cover {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [LinearOrder ι] [Fintype ι] [Nonempty ι]
    (v : ι → E) (l u : ι → ℝ) (hlu : ∀ i, l i ≤ u i)
    (w : stdSimplex ℝ ι) (y : ℝ)
    (hylo : (∑ i, w.val i * l i) ≤ y) (hyhi : y ≤ ∑ i, w.val i * u i) :
    ∃ j : ι, (∑ i, w.val i • v i, y) ∈ convexHull ℝ
      (((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
        ((fun i => (v i, u i)) '' {i | i ≤ j})) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (show Fintype.card ι ≠ 0 from ne_of_gt Fintype.card_pos)
  let e : Fin (m + 1) ≃o ι := Fintype.orderIsoFinOfCardEq ι hm
  let w' : stdSimplex ℝ (Fin (m + 1)) :=
    ⟨(fun i => w.val (e i)), (fun i => w.property.1 (e i)),
      (e.toEquiv.sum_comp w.val).trans w.property.2⟩
  have hlo : (∑ i, w'.val i * (l ∘ e) i) ≤ y := by
    change (∑ i, w.val (e i) * l (e i)) ≤ y
    have heq : (∑ i, w.val (e i) * l (e i)) = ∑ i, w.val i * l i :=
      e.toEquiv.sum_comp (fun i => w.val i * l i)
    rw [heq]
    exact hylo
  have hup : y ≤ ∑ i, w'.val i * (u ∘ e) i := by
    change y ≤ ∑ i, w.val (e i) * u (e i)
    have heq : (∑ i, w.val (e i) * u (e i)) = ∑ i, w.val i * u i :=
      e.toEquiv.sum_comp (fun i => w.val i * u i)
    rw [heq]
    exact hyhi
  obtain ⟨j, hj⟩ := s2v_hardt6rb_prism_staircase_cover (v ∘ e) (l ∘ e) (u ∘ e)
    (fun i => hlu (e i)) w' hlo hup
  refine ⟨e j, ?_⟩
  change (∑ i, w.val (e i) • v (e i), y) ∈ convexHull ℝ
    ((((fun i => (v i, l i)) ∘ e) '' {i | j ≤ i}) ∪
      (((fun i => (v i, u i)) ∘ e) '' {i | i ≤ j})) at hj
  rw [(s2v_hardt6rb_ordered_images e (fun i => (v i, l i)) j).1,
    (s2v_hardt6rb_ordered_images e (fun i => (v i, u i)) j).2] at hj
  have heq : (∑ i, w.val (e i) • v (e i)) = ∑ i, w.val i • v i :=
    e.toEquiv.sum_comp (fun i => w.val i • v i)
  rw [heq] at hj
  exact hj

end HodgeLean.Foundations.Program

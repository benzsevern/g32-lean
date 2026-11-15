import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineSuspensionEquator

/-! # Actual half-space supports of the suspension face boundaries
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.QuotientDuality

/-- The upper half has its literal nonnegative first coordinate and the specified tangential weights. -/
theorem properCycle_affine_upper_face_formula (d : ℕ)
    (t : StdSimplex ℝ (Fin (d+2))) :
    properCycle_affine_suspension_split d
      (StdSimplex.map (Fin.castSucc (Fin.last (d+1))).succAbove t) =
      (t.weights 0, fun j => t.weights j.succ.castSucc - (1/2 : ℝ) * t.weights (Fin.last (d+1))) := by
  let v := StdSimplex.map (Fin.castSucc (Fin.last (d+1))).succAbove t
  have hn : v.weights (Fin.castSucc (Fin.last (d+1))) = 0 :=
    stdSimplex_map_succAbove_self_zero (d+1) _ t
  have hz : v.weights 0 = t.weights 0 := by
    have h := properCycle_affine_face_weight (d+1) (Fin.castSucc (Fin.last (d+1))) t 0
    have hi : (Fin.castSucc (Fin.last (d+1))).succAbove (0 : Fin (d+2)) = 0 :=
      Fin.succAbove_of_castSucc_lt _ _ (by change 0 < d+1; omega)
    simpa only [hi] using h
  have hr (j : Fin d) : v.weights j.succ.castSucc.castSucc = t.weights j.succ.castSucc := by
    have h := properCycle_affine_face_weight (d+1) (Fin.castSucc (Fin.last (d+1))) t j.succ.castSucc
    have hi : (Fin.castSucc (Fin.last (d+1))).succAbove j.succ.castSucc = j.succ.castSucc.castSucc :=
      Fin.succAbove_of_castSucc_lt _ _ (by change j.val + 1 < d+1; omega)
    simpa only [hi] using h
  have hm : v.weights (Fin.last (d+2)) = t.weights (Fin.last (d+1)) := by
    simpa only [Fin.succAbove_castSucc_self, Fin.succ_last] using
      properCycle_affine_face_weight (d+1) (Fin.castSucc (Fin.last (d+1))) t (Fin.last (d+1))
  change properCycle_affine_suspension_split d v = _
  apply Prod.ext
  · change v.weights 0 - v.weights _ = _
    rw [hz, hn, sub_zero]
  · funext j
    change v.weights _ - v.weights _ - (1/2 : ℝ) * v.weights _ = _
    rw [hr, hn, hm, sub_zero]

/-- Every upper-half boundary face except the common equator lies in the lower-half-ray complement. -/
theorem properCycle_affine_upper_boundary_lower_complement (d : ℕ)
    (t : StdSimplex ℝ (Fin (d+2))) (i : Fin (d+2)) (hi : i ≠ 0)
    (hw : t.weights i = 0) :
    ¬ ((properCycle_affine_suspension_split d
        (StdSimplex.map (Fin.castSucc (Fin.last (d+1))).succAbove t)).1 ≤ 0 ∧
      (properCycle_affine_suspension_split d
        (StdSimplex.map (Fin.castSucc (Fin.last (d+1))).succAbove t)).2 = 0) := by
  rw [properCycle_affine_upper_face_formula]
  rintro ⟨hle, hy⟩
  have hz : t.weights 0 = 0 := le_antisymm hle (t.weights_nonneg 0)
  have hr (j : Fin d) : t.weights j.succ.castSucc = (1/2 : ℝ) * t.weights (Fin.last (d+1)) :=
    sub_eq_zero.mp (congrFun hy j)
  have hm : t.weights (Fin.last (d+1)) = 0 := by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · revert hw hi
      refine Fin.cases ?_ (fun j => ?_) i
      · intro h _; exact (h rfl).elim
      · intro _ hj
        have h := hr j
        rw [hj] at h
        linarith
    · exact hw
  have hall (j : Fin (d+2)) : t.weights j = 0 := by
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact hz
      · exact (hr j).trans (by rw [hm, mul_zero])
    · exact hm
  have hzero : ∑ j, t.weights j = 0 := Finset.sum_eq_zero (fun j _ => hall j)
  exact zero_ne_one (hzero.symm.trans t.total_of_fintype)

/-- The lower half retains its literal negative first coordinate and the ordered tangential weights. -/
theorem properCycle_affine_lower_face_formula (d : ℕ)
    (t : StdSimplex ℝ (Fin (d+2))) :
    properCycle_affine_suspension_split d (StdSimplex.map (0 : Fin (d+3)).succAbove t) =
      (-t.weights (Fin.castSucc (Fin.last d)), fun j =>
        t.weights j.castSucc.castSucc - t.weights (Fin.castSucc (Fin.last d)) -
          (1/2 : ℝ) * t.weights (Fin.last (d+1))) := by
  let v := StdSimplex.map (0 : Fin (d+3)).succAbove t
  have hz : v.weights 0 = 0 := stdSimplex_map_succAbove_self_zero (d+1) 0 t
  have hw (i : Fin (d+2)) : v.weights i.succ = t.weights i :=
    properCycle_affine_face_weight (d+1) 0 t i
  change properCycle_affine_suspension_split d v = _
  apply Prod.ext
  · change v.weights 0 - v.weights (Fin.castSucc (Fin.last (d+1))) = _
    rw [hz]
    change 0 - v.weights (Fin.castSucc (Fin.last d)).succ = _
    rw [hw, zero_sub]
  · funext j
    change v.weights j.castSucc.castSucc.succ -
      v.weights (Fin.castSucc (Fin.last d)).succ - (1/2 : ℝ) * v.weights (Fin.last (d+1)).succ = _
    rw [hw, hw, hw]

/-- Every lower-half boundary face except the common equator lies in the upper-half-ray complement. -/
theorem properCycle_affine_lower_boundary_upper_complement (d : ℕ)
    (t : StdSimplex ℝ (Fin (d+2))) (i : Fin (d+2))
    (hi : i ≠ Fin.castSucc (Fin.last d)) (hw : t.weights i = 0) :
    ¬ (0 ≤ (properCycle_affine_suspension_split d (StdSimplex.map (0 : Fin (d+3)).succAbove t)).1 ∧
      (properCycle_affine_suspension_split d (StdSimplex.map (0 : Fin (d+3)).succAbove t)).2 = 0) := by
  rw [properCycle_affine_lower_face_formula]
  rintro ⟨hle, hy⟩
  have hn : t.weights (Fin.castSucc (Fin.last d)) = 0 :=
    le_antisymm (neg_nonneg.mp hle) (t.weights_nonneg _)
  have hr (j : Fin d) : t.weights j.castSucc.castSucc = (1/2 : ℝ) * t.weights (Fin.last (d+1)) := by
    have h := congrFun hy j
    change _ - _ - (1/2 : ℝ) * _ = 0 at h
    rw [hn, sub_zero] at h
    exact sub_eq_zero.mp h
  have hm : t.weights (Fin.last (d+1)) = 0 := by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have h := hr j
        rw [hw] at h
        linarith
      · exact (hi rfl).elim
    · exact hw
  have hall (j : Fin (d+2)) : t.weights j = 0 := by
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · exact (hr j).trans (by rw [hm, mul_zero])
      · exact hn
    · exact hm
  have hzero : ∑ j, t.weights j = 0 := Finset.sum_eq_zero (fun j _ => hall j)
  exact zero_ne_one (hzero.symm.trans t.total_of_fintype)

end HodgeLean.Foundations.QuotientDuality

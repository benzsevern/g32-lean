import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineBoundaryCycle

/-! # The affine simplex that splits across the real suspension equator

The added last vertex is the midpoint of the first and negative vertices.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.QuotientDuality

/-- The affine simplex with the extra equatorial midpoint vertex, in real product coordinates. -/
def properCycle_affine_suspension_split (d : ℕ)
    (t : StdSimplex ℝ (Fin (d+3))) : ℝ × (Fin d → ℝ) :=
  (t.weights 0 - t.weights (Fin.castSucc (Fin.last (d+1))),
    fun j => t.weights (Fin.castSucc (Fin.castSucc j.succ)) -
      t.weights (Fin.castSucc (Fin.last (d+1))) - (1/2 : ℝ) * t.weights (Fin.last (d+2)))

/-- Every side face other than the two halves and the original simplex misses the origin. -/
theorem properCycle_affine_suspension_side_face_ne_zero (d : ℕ)
    (t : StdSimplex ℝ (Fin (d+3))) (j : Fin d)
    (hj : t.weights (Fin.castSucc (Fin.castSucc j.succ)) = 0) :
    properCycle_affine_suspension_split d t ≠ 0 := by
  intro hz
  have hfirst : t.weights 0 = t.weights (Fin.castSucc (Fin.last (d+1))) :=
    sub_eq_zero.mp (congrArg Prod.fst hz)
  have hrest (k : Fin d) :
      t.weights (Fin.castSucc (Fin.castSucc k.succ)) -
        t.weights (Fin.castSucc (Fin.last (d+1))) -
          (1/2 : ℝ) * t.weights (Fin.last (d+2)) = 0 :=
    congrFun (congrArg Prod.snd hz) k
  have hneg : t.weights (Fin.castSucc (Fin.last (d+1))) = 0 := by
    have h := hrest j
    have hn := t.weights_nonneg (Fin.castSucc (Fin.last (d+1)))
    have hm := t.weights_nonneg (Fin.last (d+2))
    rw [hj] at h
    linarith
  have hmid : t.weights (Fin.last (d+2)) = 0 := by
    have h := hrest j
    rw [hj, hneg] at h
    linarith
  have hall (i : Fin (d+3)) : t.weights i = 0 := by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · refine Fin.cases ?_ (fun k => ?_) i
        · exact hfirst.trans hneg
        · have h := hrest k
          rw [hneg, hmid] at h
          simpa using h
      · exact hneg
    · exact hmid
  have hzero : ∑ i, t.weights i = 0 := Finset.sum_eq_zero (fun i _ => hall i)
  exact zero_ne_one (hzero.symm.trans t.total_of_fintype)

/-- The splitting simplex is an actual continuous singular simplex. -/
@[fun_prop] theorem properCycle_continuous_affine_suspension_split (d : ℕ) :
    Continuous (properCycle_affine_suspension_split d) := by
  apply Continuous.prodMk
  · exact (StdSimplex.continuous_weights_apply ℝ 0).sub
      (StdSimplex.continuous_weights_apply ℝ (Fin.castSucc (Fin.last (d+1))))
  · apply continuous_pi
    intro j
    exact ((StdSimplex.continuous_weights_apply ℝ (Fin.castSucc (Fin.castSucc j.succ))).sub
      (StdSimplex.continuous_weights_apply ℝ (Fin.castSucc (Fin.last (d+1))))).sub
      (continuous_const.mul (StdSimplex.continuous_weights_apply ℝ (Fin.last (d+2))))

/-- An injective face map retains the original weight at every surviving vertex. -/
theorem properCycle_affine_face_weight (n : ℕ) (i : Fin (n+2))
    (t : StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1)) :
    (StdSimplex.map i.succAbove t).weights (i.succAbove j) = t.weights j := by
  rw [StdSimplex.weights_map]
  exact Finsupp.mapDomain_apply_of_injective (Fin.succAbove_right_injective) _ _

/-- Omitting the added midpoint gives exactly the original standard affine simplex. -/
theorem properCycle_affine_suspension_original_face (d : ℕ)
    (t : StdSimplex ℝ (Fin (d+2))) :
    properCycle_affine_suspension_split d (StdSimplex.map (Fin.last (d+2)).succAbove t) =
      (standardAffineSimplex (d+1) t 0, fun j => standardAffineSimplex (d+1) t j.succ) := by
  have hw (j : Fin (d+2)) :
      (StdSimplex.map (Fin.last (d+2)).succAbove t).weights j.castSucc = t.weights j := by
    simpa only [Fin.succAbove_last] using properCycle_affine_face_weight (d+1) (Fin.last (d+2)) t j
  have hm := stdSimplex_map_succAbove_self_zero (d+1) (Fin.last (d+2)) t
  apply Prod.ext
  · change _ - _ = _
    rw [show (0 : Fin (d+3)) = Fin.castSucc (0 : Fin (d+2)) from rfl, hw, hw]
    rfl
  · funext j
    change _ - _ - (1/2 : ℝ) * _ = _
    rw [hw, hw, hm, mul_zero, sub_zero]
    rfl

/-- The common equatorial face is precisely the positive half-parameter affine simplex. -/
theorem properCycle_affine_suspension_equator (d : ℕ)
    (t : StdSimplex ℝ (Fin (d+1))) :
    properCycle_affine_suspension_split d
      (StdSimplex.map (Fin.castSucc (Fin.last (d+1))).succAbove
        (StdSimplex.map (0 : Fin (d+2)).succAbove t)) =
      (0, properCycle_scaled_affine_simplex d (1/2) t) := by
  let u := StdSimplex.map (0 : Fin (d+2)).succAbove t
  let v := StdSimplex.map (Fin.castSucc (Fin.last (d+1))).succAbove u
  have hu (i : Fin (d+1)) : u.weights i.succ = t.weights i :=
    properCycle_affine_face_weight d 0 t i
  have hzidx : (Fin.castSucc (Fin.last (d+1))).succAbove (0 : Fin (d+2)) = 0 :=
    Fin.succAbove_of_castSucc_lt _ _ (by change 0 < d+1; omega)
  have hvzero : v.weights 0 = 0 := by
    have h := properCycle_affine_face_weight (d+1) (Fin.castSucc (Fin.last (d+1))) u 0
    rw [hzidx] at h
    exact h.trans (stdSimplex_map_succAbove_self_zero d 0 t)
  have hvneg : v.weights (Fin.castSucc (Fin.last (d+1))) = 0 :=
    stdSimplex_map_succAbove_self_zero (d+1) _ u
  have hvrest (j : Fin d) : v.weights (Fin.castSucc (Fin.castSucc j.succ)) = t.weights j.castSucc := by
    have hi : (Fin.castSucc (Fin.last (d+1))).succAbove j.succ.castSucc =
        Fin.castSucc (Fin.castSucc j.succ) :=
      Fin.succAbove_of_castSucc_lt _ _ (by change j.val + 1 < d+1; omega)
    have h := properCycle_affine_face_weight (d+1) (Fin.castSucc (Fin.last (d+1))) u j.succ.castSucc
    rw [hi] at h
    exact h.trans (hu j.castSucc)
  have hvmid : v.weights (Fin.last (d+2)) = t.weights (Fin.last d) := by
    have h := properCycle_affine_face_weight (d+1) (Fin.castSucc (Fin.last (d+1))) u (Fin.last (d+1))
    simpa only [Fin.succAbove_castSucc_self, Fin.succ_last] using h.trans (hu (Fin.last d))
  change properCycle_affine_suspension_split d v = _
  apply Prod.ext
  · change v.weights 0 - v.weights _ = 0
    rw [hvzero, hvneg, sub_zero]
  · funext j
    change v.weights _ - v.weights _ - (1/2 : ℝ) * v.weights _ = _
    rw [hvrest, hvneg, hvmid, sub_zero]
    rfl

/-- The two distinguished faces lie on their specified sides of the real equator. -/
theorem properCycle_affine_suspension_half_faces (d : ℕ)
    (t : StdSimplex ℝ (Fin (d+2))) :
    (properCycle_affine_suspension_split d (StdSimplex.map (0 : Fin (d+3)).succAbove t)).1 ≤ 0 ∧
    0 ≤ (properCycle_affine_suspension_split d
      (StdSimplex.map (Fin.castSucc (Fin.last (d+1))).succAbove t)).1 := by
  constructor
  · change _ - _ ≤ 0
    rw [stdSimplex_map_succAbove_self_zero (d+1) 0 t, zero_sub]
    exact neg_nonpos.mpr (StdSimplex.weights_nonneg _)
  · change 0 ≤ _ - _
    rw [stdSimplex_map_succAbove_self_zero (d+1) (Fin.castSucc (Fin.last (d+1))) t, sub_zero]
    exact StdSimplex.weights_nonneg _

/-- On the original face, omitting any additional original vertex keeps the splitting simplex away from the origin. -/
theorem properCycle_affine_suspension_original_boundary_ne_zero (d : ℕ)
    (t : Convexity.StdSimplex ℝ (Fin (d+3))) (i : Fin (d+2))
    (hi : t.weights i.castSucc = 0) (hm : t.weights (Fin.last (d+2)) = 0) :
    properCycle_affine_suspension_split d t ≠ 0 := by
  intro hz
  have hfirst : t.weights 0 = t.weights (Fin.castSucc (Fin.last (d+1))) :=
    sub_eq_zero.mp (congrArg Prod.fst hz)
  have hrest (j : Fin d) :
      t.weights (Fin.castSucc (Fin.castSucc j.succ)) =
        t.weights (Fin.castSucc (Fin.last (d+1))) := by
    have h := congrFun (congrArg Prod.snd hz) j
    change _ - _ - (1/2 : ℝ) * _ = 0 at h
    rw [hm, mul_zero, sub_zero] at h
    exact sub_eq_zero.mp h
  have hn : t.weights (Fin.castSucc (Fin.last (d+1))) = 0 := by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · revert hi
      refine Fin.cases ?_ (fun j => ?_) i
      · intro h; exact hfirst.symm.trans h
      · intro h; exact (hrest j).symm.trans h
    · exact hi
  have hall (j : Fin (d+3)) : t.weights j = 0 := by
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · exact hfirst.trans hn
        · exact (hrest j).trans hn
      · exact hn
    · exact hm
  have hzero : ∑ j, t.weights j = 0 := Finset.sum_eq_zero (fun j _ => hall j)
  exact zero_ne_one (hzero.symm.trans t.total_of_fintype)

/-- Every irrelevant side face lies in the actual complement of the lower real half ray. -/
theorem properCycle_affine_suspension_side_face_lower_complement (d : ℕ)
    (t : StdSimplex ℝ (Fin (d+3))) (j : Fin d)
    (hj : t.weights (Fin.castSucc (Fin.castSucc j.succ)) = 0) :
    ¬ ((properCycle_affine_suspension_split d t).1 ≤ 0 ∧
      (properCycle_affine_suspension_split d t).2 = 0) := by
  rintro ⟨hle, hy⟩
  have h := congrFun hy j
  change _ - _ - (1/2 : ℝ) * _ = 0 at h
  rw [hj] at h
  have hn : t.weights (Fin.castSucc (Fin.last (d+1))) = 0 := by
    have ha := t.weights_nonneg (Fin.castSucc (Fin.last (d+1)))
    have hb := t.weights_nonneg (Fin.last (d+2))
    linarith
  have hge : 0 ≤ (properCycle_affine_suspension_split d t).1 := by
    change 0 ≤ t.weights 0 - t.weights _
    rw [hn, sub_zero]
    exact t.weights_nonneg 0
  exact properCycle_affine_suspension_side_face_ne_zero d t j hj
    (Prod.ext (le_antisymm hle hge) hy)

end HodgeLean.Foundations.QuotientDuality

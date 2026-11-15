import HodgeLean.Foundations.Program.SchoenTowerT11bBands

/-! Positive piecewise affine coordinates with a fixed boundary point.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Scale the upper half-line about a fixed boundary and retain the lower half-line pointwise.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compatible band-coordinate step. -/
def s2v_t11b_positiveKink (a c x : ℝ) : ℝ :=
  a + min (x - a) 0 + c * max (x - a) 0

/-- The half-line coordinate map fixes every point below its boundary.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compatible band-coordinate step. -/
theorem s2v_t11b_positiveKink_of_le (a c x : ℝ) (hx : x ≤ a) :
    s2v_t11b_positiveKink a c x = x := by
  have h := sub_nonpos.mpr hx
  simp only [s2v_t11b_positiveKink, min_eq_left h, max_eq_right h, mul_zero, add_zero]
  ring

/-- Above the boundary the coordinate map has its specified affine formula.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compatible band-coordinate step. -/
theorem s2v_t11b_positiveKink_of_ge (a c x : ℝ) (hx : a ≤ x) :
    s2v_t11b_positiveKink a c x = a + c * (x - a) := by
  have h := sub_nonneg.mpr hx
  simp only [s2v_t11b_positiveKink, min_eq_right h, max_eq_left h, add_zero]

/-- Positive slopes preserve strict order across the boundary and on both half-lines.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compatible band-coordinate step. -/
theorem s2v_t11b_positiveKink_strictMono (a c : ℝ) (hc : 0 < c) :
    StrictMono (s2v_t11b_positiveKink a c) := by
  intro x y hxy
  by_cases hy : y ≤ a
  · rw [s2v_t11b_positiveKink_of_le a c x (hxy.le.trans hy),
      s2v_t11b_positiveKink_of_le a c y hy]
    exact hxy
  · have hy' : a < y := lt_of_not_ge hy
    by_cases hx : x ≤ a
    · rw [s2v_t11b_positiveKink_of_le a c x hx,
        s2v_t11b_positiveKink_of_ge a c y hy'.le]
      nlinarith [mul_pos hc (sub_pos.mpr hy')]
    · rw [s2v_t11b_positiveKink_of_ge a c x (lt_of_not_ge hx).le,
        s2v_t11b_positiveKink_of_ge a c y hy'.le]
      nlinarith [mul_lt_mul_of_pos_left (sub_lt_sub_right hxy a) hc]

/-- Reciprocal positive slopes invert the half-line coordinate map.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compatible band-coordinate step. -/
theorem s2v_t11b_positiveKink_left_inv (a c : ℝ) (hc : 0 < c) (x : ℝ) :
    s2v_t11b_positiveKink a c⁻¹ (s2v_t11b_positiveKink a c x) = x := by
  by_cases hx : x ≤ a
  · rw [s2v_t11b_positiveKink_of_le a c x hx,
      s2v_t11b_positiveKink_of_le a c⁻¹ x hx]
  · have hax : a < x := lt_of_not_ge hx
    have hy : a ≤ a + c * (x - a) := by
      nlinarith [mul_pos hc (sub_pos.mpr hax)]
    rw [s2v_t11b_positiveKink_of_ge a c x hax.le,
      s2v_t11b_positiveKink_of_ge a c⁻¹ (a + c * (x - a)) hy]
    field_simp [ne_of_gt hc]
    <;> ring

/-- The affine boundary coordinates depend continuously on both the slope and point.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compatible band-coordinate step. -/
theorem s2v_t11b_positiveKink_continuous (a : ℝ) :
    Continuous (fun z : ℝ × ℝ => s2v_t11b_positiveKink a z.1 z.2) := by
  unfold s2v_t11b_positiveKink
  exact (continuous_const.add ((continuous_snd.sub continuous_const).min continuous_const)).add
    (continuous_fst.mul ((continuous_snd.sub continuous_const).max continuous_const))

end HodgeLean.Foundations.Program

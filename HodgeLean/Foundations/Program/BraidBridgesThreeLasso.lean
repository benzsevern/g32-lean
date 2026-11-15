import HodgeLean.Foundations.Program.BraidBridgesThreeFill

/-! # Regularity and continuity of the lasso traces

The pulled-back lassos `b65b_inverseNormalization ∘ b65b_lasso i` stay in the regular plane on
`[0, 1]` (the rational pieces of stage one cover the parameter interval) and are continuous
there, so they are based loops at the pulled-back base point.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Complex
namespace HodgeLean.Foundations.Program

theorem b65x_lasso_continuous_plane (i : Fin 13) : Continuous (b65b_lasso i) := by
  unfold b65b_lasso
  split_ifs with hi
  · unfold mr_outer; fun_prop
  · refine Continuous.if_le (by fun_prop) (Continuous.if_le (by fun_prop) (by fun_prop)
      continuous_id continuous_const ?_) continuous_id continuous_const ?_
    · intro s hs
      rw [hs]
      have : 2 * (Real.pi : ℂ) * I * (3 * ((2 / 3 : ℝ) : ℂ) - 1) = 2 * Real.pi * I := by
        push_cast; ring
      rw [this, Complex.exp_two_pi_mul_I]
      push_cast; ring
    · intro s hs
      rw [hs]
      simp only [show (1 / 3 : ℝ) ≤ 2 / 3 by norm_num, ↓reduceIte]
      have : 2 * (Real.pi : ℂ) * I * (3 * ((1 / 3 : ℝ) : ℂ) - 1) = 0 := by
        push_cast; ring
      rw [this, Complex.exp_zero]
      push_cast; ring

theorem b65x_lasso_zero (i : Fin 13) : b65b_lasso i 0 = mr_basePoint := by
  unfold b65b_lasso
  split_ifs with h0 h1
  · simp [mr_outer, mr_basePoint]
  · simp
  · norm_num at h1
  · norm_num at h1

theorem b65x_lasso_one (i : Fin 13) : b65b_lasso i 1 = mr_basePoint := by
  unfold b65b_lasso
  split_ifs with h0 h1 h2
  · simp only [mr_outer, mr_basePoint, Complex.ofReal_one, mul_one]
    rw [show -(2 * (Real.pi : ℂ) * I) = -(2 * Real.pi * I) from rfl, Complex.exp_neg,
      Complex.exp_two_pi_mul_I]
    simp
  · norm_num at h1
  · norm_num at h2
  · simp

/-- Every angle in `[-π/4, π/4]` is the arctangent of a parameter in `[-1, 1]`. -/
theorem b65x_arctan_onto {y : ℝ} (h1 : -(Real.pi / 4) ≤ y) (h2 : y ≤ Real.pi / 4) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1, Real.arctan t = y := by
  have hpi := Real.pi_pos
  refine ⟨Real.tan y, ⟨?_, ?_⟩, Real.arctan_tan (by linarith) (by linarith)⟩
  · rw [← Real.arctan_strictMono.le_iff_le, Real.arctan_tan (by linarith) (by linarith),
      Real.arctan_neg, Real.arctan_one]
    exact h1
  · rw [← Real.arctan_strictMono.le_iff_le, Real.arctan_tan (by linarith) (by linarith),
      Real.arctan_one]
    exact h2

/-- The pulled-back lassos are regular on the parameter interval. -/
theorem b65x_lasso_regular (i : Fin 13) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    b65b_inverseNormalization (b65b_lasso i s) ∈ b65s_regular := by
  obtain ⟨hs0, hs1⟩ := hs
  have hpi := Real.pi_pos
  have hreg := fun k t ht ↦ (b65x_piece_regular i k t ht).2
  by_cases hi : i = 0
  · subst hi
    by_cases hh : s ≤ 1 / 2
    · obtain ⟨t, ht, hat⟩ := b65x_arctan_onto (y := Real.pi * (1 / 4 - s))
        (by nlinarith) (by nlinarith)
      have hst : s = 1 / 4 - Real.arctan t / Real.pi := by
        rw [hat]; field_simp; ring
      rw [hst, (b65x_lasso_pieces.2.2 t ht).1]
      exact hreg 2 t (by simpa [b65x_dom] using ht)
    · obtain ⟨t, ht, hat⟩ := b65x_arctan_onto (y := Real.pi * (3 / 4 - s))
        (by nlinarith) (by nlinarith)
      have hst : s = 3 / 4 - Real.arctan t / Real.pi := by
        rw [hat]; field_simp; ring
      rw [hst, (b65x_lasso_pieces.2.2 t ht).2]
      exact hreg 1 t (by simpa [b65x_dom] using ht)
  · by_cases ha : s ≤ 1 / 3
    · have hst : s = (3 * s) / 3 := by ring
      rw [hst, (b65x_lasso_pieces.1 i hi (3 * s) ⟨by linarith, by linarith⟩).1]
      exact hreg 0 _ (by simp [b65x_dom]; constructor <;> linarith)
    by_cases hb : s ≤ 1 / 2
    · obtain ⟨t, ht, hat⟩ := b65x_arctan_onto (y := Real.pi * (3 * s - 5 / 4))
        (by nlinarith) (by nlinarith)
      have hst : s = (5 / 4 + Real.arctan t / Real.pi) / 3 := by
        rw [hat]; field_simp; ring
      rw [hst, (b65x_lasso_pieces.2.1 i hi t ht).1]
      exact hreg 1 t (by simpa [b65x_dom] using ht)
    by_cases hc : s ≤ 2 / 3
    · obtain ⟨t, ht, hat⟩ := b65x_arctan_onto (y := Real.pi * (3 * s - 7 / 4))
        (by nlinarith) (by nlinarith)
      have hst : s = (7 / 4 + Real.arctan t / Real.pi) / 3 := by
        rw [hat]; field_simp; ring
      rw [hst, (b65x_lasso_pieces.2.1 i hi t ht).2]
      exact hreg 2 t (by simpa [b65x_dom] using ht)
    · have hst : s = 1 - (3 - 3 * s) / 3 := by ring
      rw [hst, (b65x_lasso_pieces.1 i hi (3 - 3 * s) ⟨by linarith, by linarith⟩).2]
      exact hreg 0 _ (by simp [b65x_dom]; constructor <;> linarith)

theorem b65x_invN_denom {w : ℂ} (hw : b65b_inverseNormalization w ∈ b65s_regular) :
    ((b65b_boxCentre 6).1 : ℂ) - w * (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ))
      ≠ 0 := by
  intro h
  apply hw.1
  simp only [b65b_inverseNormalization]
  rw [h, div_zero]

/-- The pulled-back lassos are continuous on the parameter interval. -/
theorem b65x_lasso_continuous (i : Fin 13) :
    Continuous fun s : unitInterval ↦ b65b_inverseNormalization (b65b_lasso i s) := by
  unfold b65b_inverseNormalization
  have hl : Continuous fun s : unitInterval ↦ b65b_lasso i s :=
    (b65x_lasso_continuous_plane i).comp continuous_subtype_val
  refine Continuous.div continuous_const (by fun_prop) fun s ↦ ?_
  exact b65x_invN_denom (b65x_lasso_regular i s ⟨s.2.1, s.2.2⟩)

/-- The pulled-back base point. -/
def b65x_basePoint : b65s_regular :=
  ⟨b65b_inverseNormalization mr_basePoint, by
    simpa [b65x_lasso_zero] using b65x_lasso_regular 0 0 (by norm_num)⟩

/-- The pulled-back lasso with column index `i`, as a based loop of the regular plane. -/
def b65x_lassoPath (i : Fin 13) : Path b65x_basePoint b65x_basePoint where
  toFun s := ⟨b65b_inverseNormalization (b65b_lasso i s), b65x_lasso_regular i s ⟨s.2.1, s.2.2⟩⟩
  continuous_toFun := (b65x_lasso_continuous i).subtype_mk _
  source' := Subtype.ext (by simp [b65x_basePoint, b65x_lasso_zero])
  target' := Subtype.ext (by simp [b65x_basePoint, b65x_lasso_one])

theorem b65x_lassoPath_apply (i : Fin 13) (s : unitInterval) :
    (b65x_lassoPath i s).val = b65b_inverseNormalization (b65b_lasso i s) := rfl

end HodgeLean.Foundations.Program

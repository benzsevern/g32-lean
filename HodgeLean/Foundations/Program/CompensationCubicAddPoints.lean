import HodgeLean.Foundations.Program.CompensationCubicGroupDefs
import HodgeLean.Foundations.Program.CompensationCubicAddLaws

set_option maxHeartbeats 400000

namespace HodgeLean.Foundations.Program.CompensationCubic

open WeierstrassCurve.Affine

theorem cubic_nonsingular_iff {x y : ℂ} : W.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + 1 := by
  rw [← equation_iff_nonsingular, equation_iff]
  simp [W, HodgeLean.Foundations.Program.cp_W]

noncomputable def cubicHomCoords : W.toAffine.Point → Fin 3 → ℂ
  | .zero => ![0, 1, 0]
  | .some x y _ => ![x, y, 1]

example : cubicHomCoords 0 = ![0, 1, 0] := rfl

theorem cubicHomCoords_isCubicTriple (P : W.toAffine.Point) :
    (fun p : Fin 3 → ℂ => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) (cubicHomCoords P) := by
  cases P with
  | zero => simp [cubicHomCoords]
  | some x y h =>
    simp only [cubicHomCoords, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination cubic_nonsingular_iff.mp h

private theorem projPoint_nonsingular {s : Fin 3 → ℂ} (hs : (fun p : Fin 3 → ℂ => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s) (h : s 2 ≠ 0) :
    W.toAffine.Nonsingular (s 0 / s 2) (s 1 / s 2) := by
  rw [cubic_nonsingular_iff]
  change s 1 ^ 2 * s 2 = s 0 ^ 3 + s 2 ^ 3 at hs
  field_simp
  linear_combination hs

noncomputable def cubicProjPoint (s : Fin 3 → ℂ) (hs : (fun p : Fin 3 → ℂ => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s) : W.toAffine.Point :=
  if h : s 2 = 0 then 0 else .some _ _ (projPoint_nonsingular hs h)

example : cubicProjPoint ![0, 1, 0] (by simp []) = 0 := by
  simp [cubicProjPoint]

theorem cubicProjPoint_of_eq_zero {s : Fin 3 → ℂ} (hs : (fun p : Fin 3 → ℂ => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s) (h : s 2 = 0) :
    cubicProjPoint s hs = 0 := by
  simp [cubicProjPoint, h]

theorem cubicProjPoint_of_ne_zero {s : Fin 3 → ℂ} (hs : (fun p : Fin 3 → ℂ => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s) (h : s 2 ≠ 0) :
    cubicProjPoint s hs = .some _ _ (projPoint_nonsingular hs h) := by
  simp [cubicProjPoint, h]

theorem cubicProjPoint_eq_some {s : Fin 3 → ℂ} (hs : (fun p : Fin 3 → ℂ => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s) {x y : ℂ}
    {hxy : W.toAffine.Nonsingular x y} (h : s 2 ≠ 0) (hx : s 0 = x * s 2) (hy : s 1 = y * s 2) :
    cubicProjPoint s hs = .some x y hxy := by
  rw [cubicProjPoint_of_ne_zero hs h, Point.some.injEq]
  constructor
  · rw [hx, mul_div_cancel_right₀ _ h]
  · rw [hy, mul_div_cancel_right₀ _ h]

theorem cubicProjPoint_smul {s : Fin 3 → ℂ} (hs : (fun p : Fin 3 → ℂ => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s) {t : ℂ} (ht : t ≠ 0)
    (hts : (fun p : Fin 3 → ℂ => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) fun k ↦ t * s k) :
    cubicProjPoint (fun k ↦ t * s k) hts = cubicProjPoint s hs := by
  by_cases h : s 2 = 0
  · have hts0 : (fun k => t * s k) 2 = 0 := by
      change t * s 2 = 0
      rw [h, mul_zero]
    rw [cubicProjPoint_of_eq_zero (s := s) hs h,
      cubicProjPoint_of_eq_zero (s := fun k => t * s k) hts hts0]
  · rw [cubicProjPoint_of_ne_zero (s := s) hs h]
    exact cubicProjPoint_eq_some (s := fun k => t * s k) hts (mul_ne_zero ht h)
      (by field_simp) (by field_simp)


theorem cubicProjPoint_homCoords (P : W.toAffine.Point) :
    cubicProjPoint (cubicHomCoords P) (cubicHomCoords_isCubicTriple P) = P := by
  cases P with
  | zero => exact cubicProjPoint_of_eq_zero _ (by simp [cubicHomCoords])
  | some x y h =>
    exact cubicProjPoint_eq_some _ (by simp [cubicHomCoords]) (by simp [cubicHomCoords])
      (by simp [cubicHomCoords])

private theorem third_ne_zero {s : Fin 3 → ℂ} (hne : s 1 ≠ 0 ∨ s 2 ≠ 0) {b : ℂ}
    (hy : s 1 = b * s 2) : s 2 ≠ 0 := by
  intro h
  rcases hne with h1 | h2
  · exact h1 (by rw [hy, h, mul_zero])
  · exact h2 h

private theorem negY_eq (x y : ℂ) : W.toAffine.negY x y = -y := by
  simp [negY, W, HodgeLean.Foundations.Program.cp_W]

private theorem eq_of_sq_eq {x y₁ y₂ : ℂ} (h₁ : y₁ ^ 2 = x ^ 3 + 1) (h₂ : y₂ ^ 2 = x ^ 3 + 1)
    (hne : y₁ ≠ -y₂) : y₁ = y₂ := by
  have h : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination h₁ - h₂
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact (hne (eq_neg_of_add_eq_zero_left h)).elim

private theorem chord_addX {x₁ x₂ y₁ y₂ : ℂ} (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) =
      ((y₁ - y₂) ^ 2 - (x₁ + x₂) * (x₁ - x₂) ^ 2) / (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [slope_of_X_ne hx, addX]
  simp only [W, HodgeLean.Foundations.Program.cp_W]
  field_simp
  ring

private theorem chord_addY {x₁ x₂ y₁ y₂ : ℂ} (hx : x₁ ≠ x₂) :
    W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) =
      -((y₁ - y₂) * ((y₁ - y₂) ^ 2 - (x₁ + x₂) * (x₁ - x₂) ^ 2 - x₁ * (x₁ - x₂) ^ 2) +
        y₁ * (x₁ - x₂) ^ 3) / (x₁ - x₂) ^ 3 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [addY, negY_eq, negAddY, chord_addX hx, slope_of_X_ne hx]
  field_simp

private theorem tangent_addX {x y : ℂ} (hy : y ≠ 0) :
    W.toAffine.addX x x (W.toAffine.slope x x y y) =
      ((3 * x ^ 2) ^ 2 - 2 * x * (2 * y) ^ 2) / (2 * y) ^ 2 := by
  have hne : y ≠ W.toAffine.negY x y := by
    rw [negY_eq]
    intro h
    exact hy (by linear_combination h / 2)
  rw [slope_of_Y_ne rfl hne, addX, negY_eq]
  simp only [W, HodgeLean.Foundations.Program.cp_W]
  field_simp
  ring

private theorem tangent_addY {x y : ℂ} (hy : y ≠ 0) :
    W.toAffine.addY x x y (W.toAffine.slope x x y y) =
      -((3 * x ^ 2) * ((3 * x ^ 2) ^ 2 - 2 * x * (2 * y) ^ 2 - x * (2 * y) ^ 2) +
        y * (2 * y) ^ 3) / (2 * y) ^ 3 := by
  have hne : y ≠ W.toAffine.negY x y := by
    rw [negY_eq]
    intro h
    exact hy (by linear_combination h / 2)
  rw [addY, negY_eq, negAddY, tangent_addX hy, slope_of_Y_ne rfl hne, negY_eq]
  simp only [W, HodgeLean.Foundations.Program.cp_W]
  field_simp
  ring

private theorem zero_add' (Q : W.toAffine.Point) : Point.zero + Q = Q := zero_add Q

private theorem add_zero' (P : W.toAffine.Point) : P + Point.zero = P := add_zero P

theorem cubicLawZ_correct (P Q : W.toAffine.Point)
    (h : cubicLawZ (cubicHomCoords P) (cubicHomCoords Q) 1 ≠ 0 ∨
      cubicLawZ (cubicHomCoords P) (cubicHomCoords Q) 2 ≠ 0) :
    cubicProjPoint (cubicLawZ (cubicHomCoords P) (cubicHomCoords Q))
      (cubicLawZ_isCubicTriple (cubicHomCoords_isCubicTriple P)
        (cubicHomCoords_isCubicTriple Q)) = P + Q := by
  cases P with
  | zero =>
    cases Q with
    | zero =>
      simp [cubicLawZ, cubicHomCoords] at h
    | some x y hq =>
      rw [zero_add']
      apply cubicProjPoint_eq_some <;> simp [cubicLawZ, cubicHomCoords]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      rw [add_zero']
      apply cubicProjPoint_eq_some <;> simp [cubicLawZ, cubicHomCoords]
    | some x₂ y₂ h₂ =>
      have e₁ := cubic_nonsingular_iff.mp h₁
      have e₂ := cubic_nonsingular_iff.mp h₂
      by_cases hx : x₁ = x₂
      · subst hx
        by_cases hy : y₁ = -y₂
        · subst hy
          rw [Point.add_of_Y_eq rfl (negY_eq _ _).symm]
          apply cubicProjPoint_of_eq_zero
          simp [cubicLawZ, cubicHomCoords]
          ring
        · obtain rfl := eq_of_sq_eq e₁ e₂ hy
          exfalso
          simp [cubicLawZ, cubicHomCoords] at h
          ring_nf at h
          simp at h
      · rw [Point.add_of_X_ne hx]
        have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
        have hs2 : cubicLawZ (cubicHomCoords (.some x₁ y₁ h₁)) (cubicHomCoords (.some x₂ y₂ h₂)) 2
            = -(x₁ - x₂) ^ 3 := by
          simp [cubicLawZ, cubicHomCoords]
          linear_combination e₂ - e₁
        apply cubicProjPoint_eq_some
        · rw [hs2]
          exact neg_ne_zero.mpr (pow_ne_zero 3 hd)
        · rw [chord_addX hx, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hd)]
          simp [cubicLawZ, cubicHomCoords]
          linear_combination (-3*x₁ ^ 2*x₂ + 6*x₁*x₂ ^ 2 - 2*x₂ ^ 3 + y₁ ^ 2 - 2*y₁*y₂ + 1) * e₁ +
            (2*x₁ ^ 3 - 6*x₁ ^ 2*x₂ + 3*x₁*x₂ ^ 2 + 2*y₁*y₂ - y₂ ^ 2 - 1) * e₂
        · rw [chord_addY hx, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 3 hd)]
          simp [cubicLawZ, cubicHomCoords]
          linear_combination (3*x₁ ^ 2*x₂*y₁ - 3*x₁ ^ 2*x₂*y₂ - 6*x₁*x₂ ^ 2*y₁ + 6*x₁*x₂ ^ 2*y₂ + 2*x₂ ^ 3*y₁ - y₁ ^ 3 + 3*y₁ ^ 2*y₂ - 2*y₁*y₂ ^ 2 - y₁ - 2*y₂ ^ 3 + 3*y₂) * e₁ +
            (-2*x₁ ^ 3*y₁ + 6*x₁ ^ 2*x₂*y₁ - 6*x₁ ^ 2*x₂*y₂ - 3*x₁*x₂ ^ 2*y₁ + 3*x₁*x₂ ^ 2*y₂ + 3*y₁*y₂ ^ 2 + y₁ - y₂ ^ 3 - 3*y₂) * e₂
theorem cubicLawY_correct (P Q : W.toAffine.Point)
    (h : cubicLawY (cubicHomCoords P) (cubicHomCoords Q) 1 ≠ 0 ∨
      cubicLawY (cubicHomCoords P) (cubicHomCoords Q) 2 ≠ 0) :
    cubicProjPoint (cubicLawY (cubicHomCoords P) (cubicHomCoords Q))
      (cubicLawY_isCubicTriple (cubicHomCoords_isCubicTriple P)
        (cubicHomCoords_isCubicTriple Q)) = P + Q := by
  cases P with
  | zero =>
    cases Q with
    | zero =>
      rw [zero_add']
      apply cubicProjPoint_of_eq_zero
      simp [cubicLawY, cubicHomCoords]
    | some x y hq =>
      rw [zero_add']
      have hy : y ≠ 0 := by
        rintro rfl
        simp [cubicLawY, cubicHomCoords] at h
      apply cubicProjPoint_eq_some <;> simp [cubicLawY, cubicHomCoords, hy]
      ring
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      rw [add_zero']
      have hy : y₁ ≠ 0 := by
        rintro rfl
        simp [cubicLawY, cubicHomCoords] at h
      apply cubicProjPoint_eq_some <;> simp [cubicLawY, cubicHomCoords, hy]
      ring
    | some x₂ y₂ h₂ =>
      have e₁ := cubic_nonsingular_iff.mp h₁
      have e₂ := cubic_nonsingular_iff.mp h₂
      by_cases hx : x₁ = x₂
      · subst hx
        by_cases hy : y₁ = -y₂
        · subst hy
          rw [Point.add_of_Y_eq rfl (negY_eq _ _).symm]
          apply cubicProjPoint_of_eq_zero
          simp [cubicLawY, cubicHomCoords]
          ring
        · obtain rfl := eq_of_sq_eq e₁ e₂ hy
          have hy0 : y₁ ≠ 0 := by
            rintro rfl
            exact hy (by simp)
          have hne : y₁ ≠ W.toAffine.negY x₁ y₁ := by
            rw [negY_eq]
            exact hy
          rw [Point.add_self_of_Y_ne hne]
          have hd : (2 * y₁) ≠ 0 := mul_ne_zero two_ne_zero hy0
          have hY : cubicLawY (cubicHomCoords (.some x₁ y₁ h₁))
              (cubicHomCoords (.some x₁ y₁ h₂)) 1 =
              W.toAffine.addY x₁ x₁ y₁ (W.toAffine.slope x₁ x₁ y₁ y₁) *
                cubicLawY (cubicHomCoords (.some x₁ y₁ h₁))
                  (cubicHomCoords (.some x₁ y₁ h₂)) 2 := by
            rw [tangent_addY hy0, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 3 hd)]
            simp [cubicLawY, cubicHomCoords]
            linear_combination (-162*x₁ ^ 6*y₁ + 24*y₁ ^ 5 + 72*y₁ ^ 3) * e₁
          apply cubicProjPoint_eq_some _ (third_ne_zero h hY) _ hY
          rw [tangent_addX hy0, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hd)]
          simp [cubicLawY, cubicHomCoords]
          linear_combination (54*x₁ ^ 4*y₁ + 24*x₁*y₁ ^ 3) * e₁
      · rw [Point.add_of_X_ne hx]
        have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
        have hY : cubicLawY (cubicHomCoords (.some x₁ y₁ h₁))
            (cubicHomCoords (.some x₂ y₂ h₂)) 1 =
            W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) *
              cubicLawY (cubicHomCoords (.some x₁ y₁ h₁))
                (cubicHomCoords (.some x₂ y₂ h₂)) 2 := by
          rw [chord_addY hx, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 3 hd)]
          simp [cubicLawY, cubicHomCoords]
          linear_combination (9*x₁ ^ 2*x₂ ^ 4 + 3*x₁ ^ 2*x₂*y₁*y₂ - 15*x₁ ^ 2*x₂*y₂ ^ 2 - 6*x₁*x₂ ^ 5 + 3*x₁*x₂ ^ 2*y₁ ^ 2 - 6*x₁*x₂ ^ 2*y₁*y₂ + 15*x₁*x₂ ^ 2*y₂ ^ 2 + 12*x₁*x₂ ^ 2 - 2*x₂ ^ 3*y₁*y₂ - 2*x₂ ^ 3*y₂ ^ 2 - 6*x₂ ^ 3 + y₁ ^ 3*y₂ - 2*y₁ ^ 2*y₂ ^ 2 + 3*y₁ ^ 2 - 5*y₁*y₂ + 2*y₂ ^ 4 - 2*y₂ ^ 2 + 3) * e₁ +
            (-9*x₁ ^ 5*x₂ + 6*x₁ ^ 4*x₂ ^ 2 + 2*x₁ ^ 3*y₁*y₂ + 2*x₁ ^ 3*y₂ ^ 2 + 6*x₁ ^ 3 + 6*x₁ ^ 2*x₂*y₁*y₂ - 3*x₁ ^ 2*x₂*y₂ ^ 2 - 27*x₁ ^ 2*x₂ - 3*x₁*x₂ ^ 2*y₁*y₂ + 15*x₁*x₂ ^ 2 - y₁*y₂ ^ 3 + 5*y₁*y₂ - y₂ ^ 2 - 3) * e₂
        apply cubicProjPoint_eq_some _ (third_ne_zero h hY) _ hY
        rw [chord_addX hx, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hd)]
        simp [cubicLawY, cubicHomCoords]
        linear_combination (-3*x₁ ^ 2*x₂*y₂ - 3*x₁*x₂ ^ 2*y₁ + 3*x₁*x₂ ^ 2*y₂ + 2*x₂ ^ 3*y₂ - y₁ ^ 2*y₂ + y₁*y₂ ^ 2 - 3*y₁ + y₂ ^ 3 + 2*y₂) * e₁ +
          (3*x₁ ^ 3*y₁ + x₁ ^ 3*y₂ + 3*x₁ ^ 2*x₂*y₁ - 3*x₁ ^ 2*x₂*y₂ - 3*x₁*x₂ ^ 2*y₁ - y₁*y₂ ^ 2 + 3*y₁ - 2*y₂) * e₂
theorem cubicLaw_exists_ne (P Q : W.toAffine.Point) :
    cubicLawZ (cubicHomCoords P) (cubicHomCoords Q) 1 ≠ 0 ∨
      cubicLawZ (cubicHomCoords P) (cubicHomCoords Q) 2 ≠ 0 ∨
      cubicLawY (cubicHomCoords P) (cubicHomCoords Q) 1 ≠ 0 ∨
      cubicLawY (cubicHomCoords P) (cubicHomCoords Q) 2 ≠ 0 := by
  cases P with
  | zero =>
    cases Q with
    | zero => simp [cubicLawY, cubicHomCoords]
    | some x y hq => simp [cubicLawZ, cubicHomCoords]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => simp [cubicLawZ, cubicHomCoords]
    | some x₂ y₂ h₂ =>
      have e₁ := cubic_nonsingular_iff.mp h₁
      have e₂ := cubic_nonsingular_iff.mp h₂
      by_cases hx : x₁ = x₂
      · subst hx
        by_cases hy : y₁ = -y₂
        · subst hy
          by_cases hy0 : y₂ = 0
          · subst hy0
            right; right; left
            simp only [cubicLawY, cubicHomCoords, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
            have hx3 : x₁ ^ 3 = -1 := by linear_combination -e₂
            intro h0
            have : (27 : ℂ) = 0 := by linear_combination -h0 + 18 * hx3
            norm_num at this
          · left
            simp only [cubicLawZ, cubicHomCoords, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
            intro h0
            have : 8 * y₂ ^ 3 = 0 := by linear_combination -h0 + (6 * y₂) * e₂
            exact hy0 (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp
              ((mul_eq_zero.mp this).resolve_left (by norm_num)))
        · obtain rfl := eq_of_sq_eq e₁ e₂ hy
          have hy0 : y₁ ≠ 0 := by
            rintro rfl
            exact hy (by simp)
          right; right; right
          simp only [cubicLawY, cubicHomCoords, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
          intro h0
          have : 8 * y₁ ^ 3 = 0 := by linear_combination h0 + (6 * y₁) * e₁
          exact hy0 (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp
            ((mul_eq_zero.mp this).resolve_left (by norm_num)))
      · right; left
        simp only [cubicLawZ, cubicHomCoords, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        intro h0
        have : (x₁ - x₂) ^ 3 = 0 := by linear_combination -h0 + e₂ - e₁
        exact hx (sub_eq_zero.mp (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp this))

end HodgeLean.Foundations.Program.CompensationCubic

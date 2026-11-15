import HodgeLean.Foundations.Curves.CubicGroupDefs
import HodgeLean.Foundations.Curves.CubicAddLaws

/-! # The two addition laws compute Mathlib's group law

Homogeneous coordinates of Mathlib's points of `W`, and the check that each of `cubicLawZ` and
`cubicLawY` gives the sum whenever its value is not the zero triple.
Relation to the goal: HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Foundations.Curves

open WeierstrassCurve.Affine

theorem cubic_nonsingular_iff {x y : ℂ} : W.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + x := by
  rw [← equation_iff_nonsingular, equation_iff]
  simp [W, WeierstrassCurve.ofJ1728]

/-- Homogeneous coordinates `[X:Y:Z]` of a point of `W`: `[0:1:0]` for zero, `[x:y:1]` otherwise.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1. -/
noncomputable def cubicHomCoords : W.toAffine.Point → Fin 3 → ℂ
  | .zero => ![0, 1, 0]
  | .some x y _ => ![x, y, 1]

example : cubicHomCoords 0 = ![0, 1, 0] := rfl

theorem cubicHomCoords_isCubicTriple (P : W.toAffine.Point) :
    IsCubicTriple (cubicHomCoords P) := by
  cases P with
  | zero => simp [IsCubicTriple, cubicHomCoords]
  | some x y h =>
    simp only [IsCubicTriple, cubicHomCoords, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination cubic_nonsingular_iff.mp h

private theorem projPoint_nonsingular {s : Fin 3 → ℂ} (hs : IsCubicTriple s) (h : s 2 ≠ 0) :
    W.toAffine.Nonsingular (s 0 / s 2) (s 1 / s 2) := by
  rw [cubic_nonsingular_iff]
  unfold IsCubicTriple at hs
  field_simp
  linear_combination hs

/-- The point of `W` with homogeneous coordinates `s`: zero when `s 2 = 0`.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1. -/
noncomputable def cubicProjPoint (s : Fin 3 → ℂ) (hs : IsCubicTriple s) : W.toAffine.Point :=
  if h : s 2 = 0 then 0 else .some _ _ (projPoint_nonsingular hs h)

example : cubicProjPoint ![0, 1, 0] (by simp [IsCubicTriple]) = 0 := by
  simp [cubicProjPoint]

theorem cubicProjPoint_of_eq_zero {s : Fin 3 → ℂ} (hs : IsCubicTriple s) (h : s 2 = 0) :
    cubicProjPoint s hs = 0 := by
  simp [cubicProjPoint, h]

theorem cubicProjPoint_of_ne_zero {s : Fin 3 → ℂ} (hs : IsCubicTriple s) (h : s 2 ≠ 0) :
    cubicProjPoint s hs = .some _ _ (projPoint_nonsingular hs h) := by
  simp [cubicProjPoint, h]

theorem cubicProjPoint_eq_some {s : Fin 3 → ℂ} (hs : IsCubicTriple s) {x y : ℂ}
    {hxy : W.toAffine.Nonsingular x y} (h : s 2 ≠ 0) (hx : s 0 = x * s 2) (hy : s 1 = y * s 2) :
    cubicProjPoint s hs = .some x y hxy := by
  rw [cubicProjPoint_of_ne_zero hs h, Point.some.injEq]
  constructor
  · rw [hx, mul_div_cancel_right₀ _ h]
  · rw [hy, mul_div_cancel_right₀ _ h]

theorem cubicProjPoint_smul {s : Fin 3 → ℂ} (hs : IsCubicTriple s) {t : ℂ} (ht : t ≠ 0)
    (hts : IsCubicTriple fun k ↦ t * s k) :
    cubicProjPoint (fun k ↦ t * s k) hts = cubicProjPoint s hs := by
  by_cases h : s 2 = 0
  · rw [cubicProjPoint_of_eq_zero hs h, cubicProjPoint_of_eq_zero hts (by simp [h])]
  · rw [cubicProjPoint_of_ne_zero hs h]
    exact cubicProjPoint_eq_some hts (mul_ne_zero ht h)
      (by field_simp) (by field_simp)

theorem cubicProjPoint_homCoords (P : W.toAffine.Point) :
    cubicProjPoint (cubicHomCoords P) (cubicHomCoords_isCubicTriple P) = P := by
  cases P with
  | zero => exact cubicProjPoint_of_eq_zero _ (by simp [cubicHomCoords])
  | some x y h =>
    exact cubicProjPoint_eq_some _ (by simp [cubicHomCoords]) (by simp [cubicHomCoords])
      (by simp [cubicHomCoords])

/-- If `s 1 = b * s 2` and `s` has a nonzero entry among the last two, then `s 2 ≠ 0`. -/
private theorem third_ne_zero {s : Fin 3 → ℂ} (hne : s 1 ≠ 0 ∨ s 2 ≠ 0) {b : ℂ}
    (hy : s 1 = b * s 2) : s 2 ≠ 0 := by
  intro h
  rcases hne with h1 | h2
  · exact h1 (by rw [hy, h, mul_zero])
  · exact h2 h

private theorem negY_eq (x y : ℂ) : W.toAffine.negY x y = -y := by
  simp [negY, W, WeierstrassCurve.ofJ1728]

private theorem eq_of_sq_eq {x y₁ y₂ : ℂ} (h₁ : y₁ ^ 2 = x ^ 3 + x) (h₂ : y₂ ^ 2 = x ^ 3 + x)
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
  simp only [W, WeierstrassCurve.ofJ1728]
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
      ((3 * x ^ 2 + 1) ^ 2 - 2 * x * (2 * y) ^ 2) / (2 * y) ^ 2 := by
  have hne : y ≠ W.toAffine.negY x y := by
    rw [negY_eq]
    intro h
    exact hy (by linear_combination h / 2)
  rw [slope_of_Y_ne rfl hne, addX, negY_eq]
  simp only [W, WeierstrassCurve.ofJ1728]
  field_simp
  ring

private theorem tangent_addY {x y : ℂ} (hy : y ≠ 0) :
    W.toAffine.addY x x y (W.toAffine.slope x x y y) =
      -((3 * x ^ 2 + 1) * ((3 * x ^ 2 + 1) ^ 2 - 2 * x * (2 * y) ^ 2 - x * (2 * y) ^ 2) +
        y * (2 * y) ^ 3) / (2 * y) ^ 3 := by
  have hne : y ≠ W.toAffine.negY x y := by
    rw [negY_eq]
    intro h
    exact hy (by linear_combination h / 2)
  rw [addY, negY_eq, negAddY, tangent_addX hy, slope_of_Y_ne rfl hne, negY_eq]
  simp only [W, WeierstrassCurve.ofJ1728]
  field_simp
  ring

private theorem zero_add' (Q : W.toAffine.Point) : Point.zero + Q = Q := zero_add Q

private theorem add_zero' (P : W.toAffine.Point) : P + Point.zero = P := add_zero P

/-- `cubicLawZ` computes the sum whenever its value is not the zero triple. -/
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
          linear_combination
            (-3*x₁^2*x₂ + 6*x₁*x₂^2 - 2*x₂^3 + x₂ + y₁^2 - 2*y₁*y₂) * e₁ +
            (2*x₁^3 - 6*x₁^2*x₂ + 3*x₁*x₂^2 - x₁ + 2*y₁*y₂ - y₂^2) * e₂
        · rw [chord_addY hx, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 3 hd)]
          simp [cubicLawZ, cubicHomCoords]
          linear_combination
            (3*x₁^2*x₂*y₁ - 3*x₁^2*x₂*y₂ - 6*x₁*x₂^2*y₁ + 6*x₁*x₂^2*y₂ + 2*x₂^3*y₁ - x₂*y₁ +
              3*x₂*y₂ - y₁^3 + 3*y₁^2*y₂ - 2*y₁*y₂^2 - 2*y₂^3) * e₁ +
            (-2*x₁^3*y₁ + 6*x₁^2*x₂*y₁ - 6*x₁^2*x₂*y₂ - 3*x₁*x₂^2*y₁ + 3*x₁*x₂^2*y₂ + x₁*y₁ -
              3*x₁*y₂ + 3*y₁*y₂^2 - y₂^3) * e₂

/-- `cubicLawY` computes the sum whenever its value is not the zero triple. -/
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
            linear_combination
              (-162*x₁^6*y₁ - 162*x₁^4*y₁ - 54*x₁^2*y₁ + 48*x₁*y₁^3 + 24*y₁^5 - 6*y₁) * e₁
          apply cubicProjPoint_eq_some _ (third_ne_zero h hY) _ hY
          rw [tangent_addX hy0, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hd)]
          simp [cubicLawY, cubicHomCoords]
          linear_combination (54*x₁^4*y₁ + 36*x₁^2*y₁ + 24*x₁*y₁^3 + 6*y₁) * e₁
      · rw [Point.add_of_X_ne hx]
        have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
        have hY : cubicLawY (cubicHomCoords (.some x₁ y₁ h₁))
            (cubicHomCoords (.some x₂ y₂ h₂)) 1 =
            W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) *
              cubicLawY (cubicHomCoords (.some x₁ y₁ h₁))
                (cubicHomCoords (.some x₂ y₂ h₂)) 2 := by
          rw [chord_addY hx, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 3 hd)]
          simp [cubicLawY, cubicHomCoords]
          linear_combination
            (9*x₁^2*x₂^4 + 6*x₁^2*x₂^2 + 3*x₁^2*x₂*y₁*y₂ - 15*x₁^2*x₂*y₂^2 + x₁^2 -
              6*x₁*x₂^5 + 4*x₁*x₂^3 + 3*x₁*x₂^2*y₁^2 - 6*x₁*x₂^2*y₁*y₂ + 15*x₁*x₂^2*y₂^2 +
              2*x₁*x₂ + x₁*y₁^2 - 5*x₁*y₂^2 - 4*x₂^4 - 2*x₂^3*y₁*y₂ - 2*x₂^3*y₂^2 +
              2*x₂*y₁^2 - 5*x₂*y₁*y₂ + 3*x₂*y₂^2 + y₁^3*y₂ - 2*y₁^2*y₂^2 + 2*y₂^4) * e₁ +
            (-9*x₁^5*x₂ + 6*x₁^4*x₂^2 - x₁^4 - 14*x₁^3*x₂ + 2*x₁^3*y₁*y₂ + 2*x₁^3*y₂^2 +
              9*x₁^2*x₂^2 + 6*x₁^2*x₂*y₁*y₂ - 3*x₁^2*x₂*y₂^2 - 5*x₁^2 - 3*x₁*x₂^2*y₁*y₂ +
              3*x₁*x₂ + 5*x₁*y₁*y₂ - x₂^2 - x₂*y₂^2 - y₁*y₂^3) * e₂
        apply cubicProjPoint_eq_some _ (third_ne_zero h hY) _ hY
        rw [chord_addX hx, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hd)]
        simp [cubicLawY, cubicHomCoords]
        linear_combination
          (-3*x₁^2*x₂*y₂ - 3*x₁*x₂^2*y₁ + 3*x₁*x₂^2*y₂ - x₁*y₁ - x₁*y₂ + 2*x₂^3*y₂ - 2*x₂*y₁ +
            3*x₂*y₂ - y₁^2*y₂ + y₁*y₂^2 + y₂^3) * e₁ +
          (3*x₁^3*y₁ + x₁^3*y₂ + 3*x₁^2*x₂*y₁ - 3*x₁^2*x₂*y₂ - 3*x₁*x₂^2*y₁ + 4*x₁*y₁ -
            x₁*y₂ - x₂*y₁ - x₂*y₂ - y₁*y₂^2) * e₂

/-- At every pair of points, one of the two laws has a nonzero entry among its last two. -/
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
            have hc : x₁ * (x₁ ^ 2 + 1) = 0 := by linear_combination -e₂
            intro h0
            rcases mul_eq_zero.mp hc with h | h
            · subst h
              norm_num at h0
            · have h' : x₁ ^ 2 = -1 := by linear_combination h
              have : (8 : ℂ) = 0 := by linear_combination h0 + (9 - 3 * x₁ ^ 2) * h'
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

end HodgeLean.Foundations.Curves

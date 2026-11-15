import HodgeLean.Foundations.Program.PrymParabolicIntersectionPlaneLift

set_option linter.unusedSectionVars false

noncomputable section
open Set Complex
namespace HodgeLean.Foundations.Program

/-- A continuous path of the standard `2`-simplex from continuous weight functions.
Source: Mathlib `Convexity.StdSimplex`; `hg5_pt`. -/
def hga_simplexPath (W : unitInterval → Fin 3 → ℝ) (hW : ∀ j, Continuous fun x ↦ W x j)
    (hnn : ∀ x j, 0 ≤ W x j) (hs : ∀ x, W x 0 + W x 1 + W x 2 = 1) :
    C(unitInterval, Convexity.StdSimplex ℝ (Fin 3)) :=
  ⟨fun x ↦ hg5_pt (W x 0) (W x 1) (W x 2) (hnn x 0) (hnn x 1) (hnn x 2) (hs x), by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).continuous_iff]
    apply continuous_pi
    intro j
    fin_cases j <;> simpa using hW _⟩

theorem hga_simplexPath_weights (W : unitInterval → Fin 3 → ℝ)
    (hW : ∀ j, Continuous fun x ↦ W x j) (hnn : ∀ x j, 0 ≤ W x j)
    (hs : ∀ x, W x 0 + W x 1 + W x 2 = 1) (x : unitInterval) (j : Fin 3) :
    (hga_simplexPath W hW hnn hs x).weights j = W x j := by
  fin_cases j <;> simp [hga_simplexPath]

/-! ## Rays in a wedge triangle -/

/-- The wedge triangle as an affine map on the half `a₀ ≥ a₂`. -/
theorem hga_wedge_upper (u v : ℝ) (a : Convexity.StdSimplex ℝ (Fin 3))
    (h : a.weights 2 ≤ a.weights 0) :
    hg5_wedge u v a = ((-11 / 2 + (u + 11 / 2) * (1 - (a.weights 0 - a.weights 2)) +
      (v - u) * a.weights 1 : ℝ) : ℂ) + ((10 * (a.weights 0 - a.weights 2) : ℝ) : ℂ) * I := by
  change ((-11 / 2 + (u + 11 / 2) * (1 - |a.weights 0 - a.weights 2|) + (v - u) * a.weights 1 : ℝ) :
    ℂ) + _ = _
  rw [abs_of_nonneg (by linarith)]

/-- The wedge triangle as an affine map on the half `a₀ ≤ a₂`. -/
theorem hga_wedge_lower (u v : ℝ) (a : Convexity.StdSimplex ℝ (Fin 3))
    (h : a.weights 0 ≤ a.weights 2) :
    hg5_wedge u v a = ((-11 / 2 + (u + 11 / 2) * (1 - (a.weights 2 - a.weights 0)) +
      (v - u) * a.weights 1 : ℝ) : ℂ) + ((10 * (a.weights 0 - a.weights 2) : ℝ) : ℂ) * I := by
  change ((-11 / 2 + (u + 11 / 2) * (1 - |a.weights 0 - a.weights 2|) + (v - u) * a.weights 1 : ℝ) :
    ℂ) + _ = _
  rw [abs_of_nonpos (by linarith), neg_sub]

/-- Bounds for the coefficients of the wedge rays. -/
theorem hga_ray_coeff_bound (b c : ℝ) (_hb : |b| ≤ 7) (_hc : |c| ≤ 7) (hcb : 1 / 2 ≤ |c - b|)
    (p : ℝ) (hp : |p| ≤ 15) : |p / (c - b)| ≤ 30 := by
  rw [abs_div, div_le_iff₀ (by linarith)]
  linarith

theorem hga_abs_mul_le_of (x y X Y : ℝ) (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- The ray weights `(1/2 + x A₀, 1/2 + x A₁, x A₂)` at the midpoint of the face `a₂ = 0` of the
wedge `(u, p)`, with `b = u + 11/2`, `c = p + 11/2`.
Source: inverse of the affine wedge on the half `a₀ ≥ a₂`. -/
def hga_rayE (b c x : ℝ) : Fin 3 → ℝ :=
  ![1 / 2 + x * ((c / 10 - (10 + b * c / 10) / (c - b)) / 2),
    1 / 2 + x * ((10 + b * c / 10) / (c - b)),
    x * (-(10 + c ^ 2 / 10) / (2 * (c - b)))]

/-- The ray weights `(x B₀, 1/2 + x B₁, 1/2 + x B₂)` at the midpoint of the face `a₀ = 0`.
Source: inverse of the affine wedge on the half `a₀ ≤ a₂`. -/
def hga_rayH (b c x : ℝ) : Fin 3 → ℝ :=
  ![x * (-(10 + c ^ 2 / 10) / (2 * (c - b))),
    1 / 2 + x * ((10 + b * c / 10) / (c - b)),
    1 / 2 + x * ((c / 10 - (10 + b * c / 10) / (c - b)) / 2)]

/-- The ray weights `(3/4 + x F₀, x F₁, 1/4 + x F₂)` at the quarter point of the face `a₁ = 0`.
Source: inverse of the affine wedge on the half `a₀ ≥ a₂`. -/
def hga_rayF (b c x : ℝ) : Fin 3 → ℝ :=
  ![3 / 4 + x * ((b / 10 - (10 + b ^ 2 / 10) / (c - b)) / 2),
    x * ((10 + b ^ 2 / 10) / (c - b)),
    1 / 4 - x * ((b / 10 + (10 + b ^ 2 / 10) / (c - b)) / 2)]

theorem hga_rayE_0 (b c x : ℝ) :
    hga_rayE b c x 0 = 1 / 2 + x * ((c / 10 - (10 + b * c / 10) / (c - b)) / 2) := rfl
theorem hga_rayE_1 (b c x : ℝ) : hga_rayE b c x 1 = 1 / 2 + x * ((10 + b * c / 10) / (c - b)) :=
  rfl
theorem hga_rayE_2 (b c x : ℝ) : hga_rayE b c x 2 = x * (-(10 + c ^ 2 / 10) / (2 * (c - b))) :=
  rfl
theorem hga_rayH_0 (b c x : ℝ) : hga_rayH b c x 0 = x * (-(10 + c ^ 2 / 10) / (2 * (c - b))) :=
  rfl
theorem hga_rayH_1 (b c x : ℝ) : hga_rayH b c x 1 = 1 / 2 + x * ((10 + b * c / 10) / (c - b)) :=
  rfl
theorem hga_rayH_2 (b c x : ℝ) :
    hga_rayH b c x 2 = 1 / 2 + x * ((c / 10 - (10 + b * c / 10) / (c - b)) / 2) := rfl
theorem hga_rayF_0 (b c x : ℝ) :
    hga_rayF b c x 0 = 3 / 4 + x * ((b / 10 - (10 + b ^ 2 / 10) / (c - b)) / 2) := rfl
theorem hga_rayF_1 (b c x : ℝ) : hga_rayF b c x 1 = x * ((10 + b ^ 2 / 10) / (c - b)) := rfl
theorem hga_rayF_2 (b c x : ℝ) :
    hga_rayF b c x 2 = 1 / 4 - x * ((b / 10 + (10 + b ^ 2 / 10) / (c - b)) / 2) := rfl

theorem hga_rayE_sum (b c x : ℝ) (hcb : c - b ≠ 0) :
    hga_rayE b c x 0 + hga_rayE b c x 1 + hga_rayE b c x 2 = 1 := by
  rw [hga_rayE_0, hga_rayE_1, hga_rayE_2]
  field_simp
  ring

theorem hga_rayH_sum (b c x : ℝ) (hcb : c - b ≠ 0) :
    hga_rayH b c x 0 + hga_rayH b c x 1 + hga_rayH b c x 2 = 1 := by
  rw [hga_rayH_0, hga_rayH_1, hga_rayH_2]
  field_simp
  ring

theorem hga_rayF_sum (b c x : ℝ) :
    hga_rayF b c x 0 + hga_rayF b c x 1 + hga_rayF b c x 2 = 1 := by
  rw [hga_rayF_0, hga_rayF_1, hga_rayF_2]
  ring

/-- Positivity of the wedge ray weights for small steps on the correct side. -/
theorem hga_rayE_pos (b c x : ℝ) (hb : |b| ≤ 7) (hc : |c| ≤ 7) (hcb : 1 / 2 ≤ |c - b|)
    (hx : |x| ≤ 1 / 1000) (hside : x * (c - b) ≤ 0) (j : Fin 3) :
    0 ≤ hga_rayE b c x j ∧ (x ≠ 0 → 0 < hga_rayE b c x j) := by
  have hcb0 : c - b ≠ 0 := fun h ↦ by rw [h, abs_zero] at hcb; norm_num at hcb
  have hp1 : |10 + b * c / 10| ≤ 15 := by
    have := hga_abs_mul_le_of b c 7 7 hb hc
    rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2]
  have hA1 := hga_ray_coeff_bound b c hb hc hcb _ hp1
  have hA1' := hga_abs_mul_le_of x _ _ _ hx hA1
  have hc10 : |c / 10| ≤ 1 := by rw [abs_div]; rw [abs_of_pos (by norm_num : (0 : ℝ) < 10)]; linarith
  have hA0 : |(c / 10 - (10 + b * c / 10) / (c - b)) / 2| ≤ 16 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := abs_sub (c / 10) ((10 + b * c / 10) / (c - b))
    linarith
  have hA0' := hga_abs_mul_le_of x _ _ _ hx hA0
  fin_cases j
  · rw [Fin.zero_eta, hga_rayE_0]
    constructor <;> [skip; intro _] <;> linarith [neg_abs_le (x * ((c / 10 - (10 + b * c / 10) /
      (c - b)) / 2))]
  · rw [Fin.mk_one, hga_rayE_1]
    constructor <;> [skip; intro _] <;> linarith [neg_abs_le (x * ((10 + b * c / 10) / (c - b)))]
  · rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, hga_rayE_2]
    have hq : 0 < 10 + c ^ 2 / 10 := by positivity
    have key : x * (-(10 + c ^ 2 / 10) / (2 * (c - b))) =
        -(x * (c - b)) * (10 + c ^ 2 / 10) / (2 * (c - b) ^ 2) := by
      field_simp
    rw [key]
    have hsq : 0 < 2 * (c - b) ^ 2 := by positivity
    constructor
    · apply div_nonneg _ hsq.le
      exact mul_nonneg (by linarith) hq.le
    · intro hx0
      apply div_pos _ hsq
      apply mul_pos _ hq
      rcases lt_or_eq_of_le hside with h | h
      · linarith
      · exact absurd (mul_eq_zero.mp h) (by tauto)

theorem hga_rayH_pos (b c x : ℝ) (hb : |b| ≤ 7) (hc : |c| ≤ 7) (hcb : 1 / 2 ≤ |c - b|)
    (hx : |x| ≤ 1 / 1000) (hside : x * (c - b) ≤ 0) (j : Fin 3) :
    0 ≤ hga_rayH b c x j ∧ (x ≠ 0 → 0 < hga_rayH b c x j) := by
  have h0 := hga_rayE_pos b c x hb hc hcb hx hside 2
  have h1 := hga_rayE_pos b c x hb hc hcb hx hside 1
  have h2 := hga_rayE_pos b c x hb hc hcb hx hside 0
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

theorem hga_rayF_pos (b c x : ℝ) (hb : |b| ≤ 7) (hc : |c| ≤ 7) (hcb : 1 / 2 ≤ |c - b|)
    (hx : |x| ≤ 1 / 1000) (hside : 0 ≤ x * (c - b)) (j : Fin 3) :
    0 ≤ hga_rayF b c x j ∧ (x ≠ 0 → 0 < hga_rayF b c x j) := by
  have hcb0 : c - b ≠ 0 := fun h ↦ by rw [h, abs_zero] at hcb; norm_num at hcb
  have hp1 : |10 + b ^ 2 / 10| ≤ 15 := by
    have hb2 : b ^ 2 ≤ 49 := by nlinarith [abs_nonneg b, sq_abs b]
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hF1 := hga_ray_coeff_bound b c hb hc hcb _ hp1
  have hb10 : |b / 10| ≤ 1 := by rw [abs_div]; rw [abs_of_pos (by norm_num : (0 : ℝ) < 10)]; linarith
  have hF0 : |(b / 10 - (10 + b ^ 2 / 10) / (c - b)) / 2| ≤ 16 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := abs_sub (b / 10) ((10 + b ^ 2 / 10) / (c - b))
    linarith
  have hF2 : |(b / 10 + (10 + b ^ 2 / 10) / (c - b)) / 2| ≤ 16 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := abs_add_le (b / 10) ((10 + b ^ 2 / 10) / (c - b))
    linarith
  have hF0' := hga_abs_mul_le_of x _ _ _ hx hF0
  have hF2' := hga_abs_mul_le_of x _ _ _ hx hF2
  fin_cases j
  · rw [Fin.zero_eta, hga_rayF_0]
    constructor <;> [skip; intro _] <;> linarith [neg_abs_le (x * ((b / 10 - (10 + b ^ 2 / 10) /
      (c - b)) / 2))]
  · rw [Fin.mk_one, hga_rayF_1]
    have hq : 0 < 10 + b ^ 2 / 10 := by positivity
    have key : x * ((10 + b ^ 2 / 10) / (c - b)) = (x * (c - b)) * (10 + b ^ 2 / 10) / (c - b) ^ 2 := by
      field_simp
    rw [key]
    have hsq : 0 < (c - b) ^ 2 := by positivity
    constructor
    · exact div_nonneg (mul_nonneg hside hq.le) hsq.le
    · intro hx0
      apply div_pos _ hsq
      apply mul_pos _ hq
      rcases lt_or_eq_of_le hside with h | h
      · exact h
      · exact absurd (mul_eq_zero.mp h.symm) (by tauto)
  · rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, hga_rayF_2]
    constructor <;> [skip; intro _] <;> linarith [le_abs_self (x * ((b / 10 + (10 + b ^ 2 / 10) /
      (c - b)) / 2))]

theorem hga_rayE_img (b c x : ℝ) (hcb : c - b ≠ 0) (a : Convexity.StdSimplex ℝ (Fin 3))
    (ha : ∀ j, a.weights j = hga_rayE b c x j) (hsmall : 0 ≤ 1 / 2 + x * (c / 10)) :
    hg5_wedge (b - 11 / 2) (c - 11 / 2) a =
      ((-11 / 2 + c / 2 + 10 * x : ℝ) : ℂ) + ((5 + c * x : ℝ) : ℂ) * I := by
  have hd : a.weights 0 - a.weights 2 = 1 / 2 + x * (c / 10) := by
    rw [ha, ha, hga_rayE_0, hga_rayE_2]
    field_simp
    ring
  rw [hga_wedge_upper _ _ a (by linarith), hd, ha 1, hga_rayE_1]
  congr 2
  · field_simp
    ring
  · ring

theorem hga_rayH_img (b c x : ℝ) (hcb : c - b ≠ 0) (a : Convexity.StdSimplex ℝ (Fin 3))
    (ha : ∀ j, a.weights j = hga_rayH b c x j) (hsmall : 0 ≤ 1 / 2 + x * (c / 10)) :
    hg5_wedge (b - 11 / 2) (c - 11 / 2) a =
      ((-11 / 2 + c / 2 + 10 * x : ℝ) : ℂ) + ((-5 - c * x : ℝ) : ℂ) * I := by
  have hd : a.weights 2 - a.weights 0 = 1 / 2 + x * (c / 10) := by
    rw [ha, ha, hga_rayH_0, hga_rayH_2]
    field_simp
    ring
  rw [hga_wedge_lower _ _ a (by linarith), hd, ha 1, hga_rayH_1]
  have hd' : a.weights 0 - a.weights 2 = -(1 / 2 + x * (c / 10)) := by linarith
  rw [hd']
  congr 2
  · field_simp
    ring
  · ring

theorem hga_rayF_img (b c x : ℝ) (hcb : c - b ≠ 0) (a : Convexity.StdSimplex ℝ (Fin 3))
    (ha : ∀ j, a.weights j = hga_rayF b c x j) (hsmall : 0 ≤ 1 / 2 + x * (b / 10)) :
    hg5_wedge (b - 11 / 2) (c - 11 / 2) a =
      ((-11 / 2 + b / 2 + 10 * x : ℝ) : ℂ) + ((5 + b * x : ℝ) : ℂ) * I := by
  have hd : a.weights 0 - a.weights 2 = 1 / 2 + x * (b / 10) := by
    rw [ha, ha, hga_rayF_0, hga_rayF_2]
    ring
  rw [hga_wedge_upper _ _ a (by linarith), hd, ha 1, hga_rayF_1]
  congr 2
  · field_simp
    ring
  · ring

/-! ## Rays in a cone triangle -/

theorem hga_cone_value_aux (k m d S : ℝ) (hS : S ≠ 0) :
    (-11 / 2 : ℂ) + (((k * m : ℝ) : ℂ) + ((10 * d : ℝ) : ℂ) * I) / ((S ^ 2 : ℝ) : ℂ) =
      ((-11 / 2 + k * m / S ^ 2 : ℝ) : ℂ) + ((10 * d / S ^ 2 : ℝ) : ℂ) * I := by
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS
  push_cast
  field_simp
  ring

/-- The value of a cone triangle at a point off its apex, in the plane coordinate.
Source: `hg5_cone`, `hg5_chartInv_ne`. -/
theorem hga_cone_value (k : ℝ) (a : Convexity.StdSimplex ℝ (Fin 3))
    (hS : 0 < a.weights 0 + a.weights 2) (hd : a.weights 0 - a.weights 2 ≠ 0) :
    hg5_chartInv (hg5_coneFun k a) =
      (((-11 / 2 + k * min (a.weights 0) (a.weights 2) / (a.weights 0 + a.weights 2) ^ 2 : ℝ) : ℂ) +
        ((10 * (a.weights 0 - a.weights 2) / (a.weights 0 + a.weights 2) ^ 2 : ℝ) : ℂ) * I :
          OnePoint ℂ) := by
  set S := a.weights 0 + a.weights 2
  set d := a.weights 0 - a.weights 2
  set m := min (a.weights 0) (a.weights 2)
  have hden : ((k * m : ℝ) : ℂ) + ((10 * d : ℝ) : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hd this
  have hS2 : ((S ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : S ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  have hne : hg5_coneFun k a ≠ 0 := by
    unfold hg5_coneFun
    exact div_ne_zero hS2 hden
  rw [hg5_chartInv_ne hne]
  congr 1
  unfold hg5_coneFun
  rw [inv_div, mr_centre]
  exact hga_cone_value_aux k m d S hS.ne'

/-- The plane radius parameter `S = a₀ + a₂` along the rays at the face `a₂ = 0` or `a₀ = 0` of a
cone. Source: inverse of the cone `hg5_coneFun`. -/
def hga_coneS (k x : ℝ) : ℝ := 1 / (2 - 2 * x / k)

/-- Ray weights at the midpoint of the face `a₂ = 0` of a cone.
Source: inverse of `hg5_coneFun` along a horizontal segment. -/
def hga_coneRayE (k x : ℝ) : Fin 3 → ℝ :=
  ![(hga_coneS k x + 2 * hga_coneS k x ^ 2) / 2, 1 - hga_coneS k x,
    (hga_coneS k x - 2 * hga_coneS k x ^ 2) / 2]

/-- Ray weights at the midpoint of the face `a₀ = 0` of a cone.
Source: inverse of `hg5_coneFun` along a horizontal segment. -/
def hga_coneRayH (k x : ℝ) : Fin 3 → ℝ :=
  ![(hga_coneS k x - 2 * hga_coneS k x ^ 2) / 2, 1 - hga_coneS k x,
    (hga_coneS k x + 2 * hga_coneS k x ^ 2) / 2]

theorem hga_coneRayE_sum (k x : ℝ) :
    hga_coneRayE k x 0 + hga_coneRayE k x 1 + hga_coneRayE k x 2 = 1 := by
  simp only [hga_coneRayE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem hga_coneRayH_sum (k x : ℝ) :
    hga_coneRayH k x 0 + hga_coneRayH k x 1 + hga_coneRayH k x 2 = 1 := by
  simp only [hga_coneRayH, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem hga_coneS_pos (k x : ℝ) (hk : |k| = 14) (hx : |x| ≤ 1 / 1000) :
    0 < hga_coneS k x ∧ hga_coneS k x < 1 := by
  have hk0 : k ≠ 0 := by intro h; rw [h, abs_zero] at hk; norm_num at hk
  have h1 : |2 * x / k| ≤ 1 / 7000 := by
    rw [abs_div, abs_mul, hk, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_iff₀ (by norm_num)]; linarith
  have hL : 1 < 2 - 2 * x / k := by linarith [le_abs_self (2 * x / k)]
  unfold hga_coneS
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; exact hL

theorem hga_coneS_half (k x : ℝ) (hk : |k| = 14) (hx : |x| ≤ 1 / 1000) (hside : x * k ≤ 0) :
    2 * hga_coneS k x ≤ 1 ∧ (x ≠ 0 → 2 * hga_coneS k x < 1) := by
  have hk0 : k ≠ 0 := by intro h; rw [h, abs_zero] at hk; norm_num at hk
  have hxk : x / k ≤ 0 := by
    have : x / k = x * k / k ^ 2 := by field_simp
    rw [this]
    exact div_nonpos_of_nonpos_of_nonneg hside (sq_nonneg k)
  have hL : 2 ≤ 2 - 2 * x / k := by
    have : 2 * x / k = 2 * (x / k) := by ring
    linarith
  have hpos : 0 < 2 - 2 * x / k := by linarith
  unfold hga_coneS
  constructor
  · rw [mul_one_div, div_le_one hpos]; exact hL
  · intro hx0
    have hxk' : x / k < 0 := by
      rcases lt_or_eq_of_le hxk with h | h
      · exact h
      · exfalso; exact hx0 ((div_eq_zero_iff.mp h).resolve_right hk0)
    rw [mul_one_div, div_lt_one hpos]
    have : 2 * x / k = 2 * (x / k) := by ring
    linarith

theorem hga_coneRayE_pos (k x : ℝ) (hk : |k| = 14) (hx : |x| ≤ 1 / 1000) (hside : x * k ≤ 0)
    (j : Fin 3) : 0 ≤ hga_coneRayE k x j ∧ (x ≠ 0 → 0 < hga_coneRayE k x j) := by
  obtain ⟨hS0, hS1⟩ := hga_coneS_pos k x hk hx
  obtain ⟨hh, hh'⟩ := hga_coneS_half k x hk hx hside
  fin_cases j
  · simp only [hga_coneRayE, Fin.zero_eta, Matrix.cons_val_zero]
    constructor <;> [skip; intro _] <;> positivity
  · simp only [hga_coneRayE, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    constructor <;> [skip; intro _] <;> linarith
  · simp only [hga_coneRayE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    have e : (hga_coneS k x - 2 * hga_coneS k x ^ 2) / 2 =
        hga_coneS k x * (1 - 2 * hga_coneS k x) / 2 := by ring
    rw [e]
    constructor
    · apply div_nonneg (mul_nonneg hS0.le (by linarith)) (by norm_num)
    · intro hx0
      have := hh' hx0
      apply div_pos (mul_pos hS0 (by linarith)) (by norm_num)

theorem hga_coneRayH_pos (k x : ℝ) (hk : |k| = 14) (hx : |x| ≤ 1 / 1000) (hside : x * k ≤ 0)
    (j : Fin 3) : 0 ≤ hga_coneRayH k x j ∧ (x ≠ 0 → 0 < hga_coneRayH k x j) := by
  have h0 := hga_coneRayE_pos k x hk hx hside 2
  have h1 := hga_coneRayE_pos k x hk hx hside 1
  have h2 := hga_coneRayE_pos k x hk hx hside 0
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

theorem hga_coneRayE_img (k x : ℝ) (hk : |k| = 14) (hx : |x| ≤ 1 / 1000)
    (a : Convexity.StdSimplex ℝ (Fin 3)) (ha : ∀ j, a.weights j = hga_coneRayE k x j) :
    hg5_chartInv (hg5_coneFun k a) =
      ((((-11 / 2 - x : ℝ) : ℂ) + ((20 : ℝ) : ℂ) * I : ℂ) : OnePoint ℂ) := by
  have hk0 : k ≠ 0 := by intro h; rw [h, abs_zero] at hk; norm_num at hk
  obtain ⟨hS0, hS1⟩ := hga_coneS_pos k x hk hx
  set S := hga_coneS k x with hSdef
  have hw0 : a.weights 0 = (S + 2 * S ^ 2) / 2 := ha 0
  have hw2 : a.weights 2 = (S - 2 * S ^ 2) / 2 := ha 2
  have hsum : a.weights 0 + a.weights 2 = S := by rw [hw0, hw2]; ring
  have hdiff : a.weights 0 - a.weights 2 = 2 * S ^ 2 := by rw [hw0, hw2]; ring
  have hmin : min (a.weights 0) (a.weights 2) = (S - 2 * S ^ 2) / 2 := by
    rw [min_eq_right (by rw [hw0, hw2]; nlinarith), hw2]
  rw [hga_cone_value k a (by rw [hsum]; exact hS0) (by rw [hdiff]; positivity), hsum, hdiff, hmin]
  have hkx : k - x ≠ 0 := by
    intro h
    have : k = x := by linarith
    rw [this] at hk
    linarith
  have e1 : -11 / 2 + k * ((S - 2 * S ^ 2) / 2) / S ^ 2 = -11 / 2 - x := by
    rw [hSdef, hga_coneS]
    field_simp
    ring
  have e2 : 10 * (2 * S ^ 2) / S ^ 2 = 20 := by
    field_simp
    ring
  rw [e1, e2]

theorem hga_coneRayH_img (k x : ℝ) (hk : |k| = 14) (hx : |x| ≤ 1 / 1000)
    (a : Convexity.StdSimplex ℝ (Fin 3)) (ha : ∀ j, a.weights j = hga_coneRayH k x j) :
    hg5_chartInv (hg5_coneFun k a) =
      ((((-11 / 2 - x : ℝ) : ℂ) + ((-20 : ℝ) : ℂ) * I : ℂ) : OnePoint ℂ) := by
  have hk0 : k ≠ 0 := by intro h; rw [h, abs_zero] at hk; norm_num at hk
  obtain ⟨hS0, hS1⟩ := hga_coneS_pos k x hk hx
  set S := hga_coneS k x with hSdef
  have hw0 : a.weights 0 = (S - 2 * S ^ 2) / 2 := ha 0
  have hw2 : a.weights 2 = (S + 2 * S ^ 2) / 2 := ha 2
  have hsum : a.weights 0 + a.weights 2 = S := by rw [hw0, hw2]; ring
  have hdiff : a.weights 0 - a.weights 2 = -(2 * S ^ 2) := by rw [hw0, hw2]; ring
  have hmin : min (a.weights 0) (a.weights 2) = (S - 2 * S ^ 2) / 2 := by
    rw [min_eq_left (by rw [hw0, hw2]; nlinarith), hw0]
  rw [hga_cone_value k a (by rw [hsum]; exact hS0)
    (by rw [hdiff]; exact neg_ne_zero.mpr (by positivity)), hsum, hdiff, hmin]
  have hkx : k - x ≠ 0 := by
    intro h
    have : k = x := by linarith
    rw [this] at hk
    linarith
  have e1 : -11 / 2 + k * ((S - 2 * S ^ 2) / 2) / S ^ 2 = -11 / 2 - x := by
    rw [hSdef, hga_coneS]
    field_simp
    ring
  have e2 : 10 * -(2 * S ^ 2) / S ^ 2 = -20 := by
    field_simp
    ring
  rw [e1, e2]

/-- The radius parameter along the ray at the quarter point of the face `a₁ = 0` of a cone.
Source: inverse of `hg5_coneFun` along a segment perpendicular to the arc. -/
def hga_coneSF (b x : ℝ) : ℝ := 1 / (1 + x * (10 / b + b / 10))

/-- Ray weights at the quarter point of the face `a₁ = 0` of the cone over the arc with `b = ±7`.
Source: inverse of `hg5_coneFun`. -/
def hga_coneRayF (b x : ℝ) : Fin 3 → ℝ :=
  ![(hga_coneSF b x + (5 + b * x) * hga_coneSF b x ^ 2 / 10) / 2, 1 - hga_coneSF b x,
    (hga_coneSF b x - (5 + b * x) * hga_coneSF b x ^ 2 / 10) / 2]

theorem hga_coneRayF_sum (b x : ℝ) :
    hga_coneRayF b x 0 + hga_coneRayF b x 1 + hga_coneRayF b x 2 = 1 := by
  simp only [hga_coneRayF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem hga_coneSF_bounds (b x : ℝ) (hb : |b| = 7) (hx : |x| ≤ 1 / 1000) :
    0 < 1 + x * (10 / b + b / 10) ∧ |x * (10 / b + b / 10)| ≤ 1 / 300 ∧ |100 * x / b| ≤ 1 / 50 := by
  have hb0 : b ≠ 0 := by intro h; rw [h, abs_zero] at hb; norm_num at hb
  have h1 : |10 / b + b / 10| ≤ 3 := by
    have := abs_add_le (10 / b) (b / 10)
    rw [abs_div, abs_div, hb, abs_of_pos (by norm_num : (0 : ℝ) < 10)] at this
    linarith
  have h2 := hga_abs_mul_le_of x _ _ _ hx h1
  have h3 : |100 * x / b| ≤ 1 / 50 := by
    rw [abs_div, abs_mul, hb, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
    rw [div_le_iff₀ (by norm_num)]; linarith
  refine ⟨?_, by linarith, h3⟩
  linarith [neg_abs_le (x * (10 / b + b / 10))]

theorem hga_coneRayF_pos (b x : ℝ) (hb : |b| = 7) (hx : |x| ≤ 1 / 1000) (hside : 0 ≤ x * b)
    (j : Fin 3) : 0 ≤ hga_coneRayF b x j ∧ (x ≠ 0 → 0 < hga_coneRayF b x j) := by
  have hb0 : b ≠ 0 := by intro h; rw [h, abs_zero] at hb; norm_num at hb
  obtain ⟨hL, hL1, h100⟩ := hga_coneSF_bounds b x hb hx
  set L := 1 + x * (10 / b + b / 10) with hLdef
  have hS : hga_coneSF b x = 1 / L := rfl
  have hSpos : 0 < 1 / L := by positivity
  have hy : 0 < 5 + b * x := by
    have : |b * x| ≤ 7 / 1000 := by
      have := hga_abs_mul_le_of b x 7 (1 / 1000) hb.le hx; linarith
    linarith [neg_abs_le (b * x)]
  have hxb : x * (10 / b + b / 10) = x * b * ((100 + b ^ 2) / (10 * b ^ 2)) := by
    field_simp
    ring
  have hq : 0 < (100 + b ^ 2) / (10 * b ^ 2) := by positivity
  fin_cases j
  · simp only [hga_coneRayF, Fin.zero_eta, Matrix.cons_val_zero]
    rw [hS]
    constructor <;> [skip; intro _] <;> positivity
  · simp only [hga_coneRayF, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hS]
    have h1 : 1 ≤ L := by rw [hLdef, hxb]; nlinarith
    constructor
    · rw [sub_nonneg, div_le_one hL]; exact h1
    · intro hx0
      have hxb0 : x * b ≠ 0 := mul_ne_zero hx0 hb0
      have h1' : 1 < L := by
        rw [hLdef, hxb]
        have : 0 < x * b := lt_of_le_of_ne hside (Ne.symm hxb0)
        nlinarith
      rw [sub_pos, div_lt_one hL]; exact h1'
  · simp only [hga_coneRayF, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [hS]
    have key : (1 / L - (5 + b * x) * (1 / L) ^ 2 / 10) / 2 =
        (5 + 100 * x / b) / (20 * L ^ 2) := by
      rw [hLdef]
      field_simp
      ring
    rw [key]
    have h5 : 0 < 5 + 100 * x / b := by linarith [neg_abs_le (100 * x / b)]
    constructor
    · positivity
    · intro _; positivity

theorem hga_coneRayF_img (b x : ℝ) (hb : |b| = 7) (hx : |x| ≤ 1 / 1000)
    (a : Convexity.StdSimplex ℝ (Fin 3)) (ha : ∀ j, a.weights j = hga_coneRayF b x j) :
    hg5_chartInv (hg5_coneFun (2 * b) a) =
      ((((-11 / 2 + b / 2 + 10 * x : ℝ) : ℂ) + ((5 + b * x : ℝ) : ℂ) * I : ℂ) : OnePoint ℂ) := by
  have hb0 : b ≠ 0 := by intro h; rw [h, abs_zero] at hb; norm_num at hb
  obtain ⟨hL, -, -⟩ := hga_coneSF_bounds b x hb hx
  set L := 1 + x * (10 / b + b / 10) with hLdef
  set S := hga_coneSF b x with hSdef
  have hS : S = 1 / L := rfl
  have hSpos : 0 < S := by rw [hS]; positivity
  have hy : 0 < 5 + b * x := by
    have : |b * x| ≤ 7 / 1000 := by
      have := hga_abs_mul_le_of b x 7 (1 / 1000) hb.le hx; linarith
    linarith [neg_abs_le (b * x)]
  have hw0 : a.weights 0 = (S + (5 + b * x) * S ^ 2 / 10) / 2 := ha 0
  have hw2 : a.weights 2 = (S - (5 + b * x) * S ^ 2 / 10) / 2 := ha 2
  have hsum : a.weights 0 + a.weights 2 = S := by rw [hw0, hw2]; ring
  have hdiff : a.weights 0 - a.weights 2 = (5 + b * x) * S ^ 2 / 10 := by rw [hw0, hw2]; ring
  have hmin : min (a.weights 0) (a.weights 2) = (S - (5 + b * x) * S ^ 2 / 10) / 2 := by
    rw [min_eq_right (by rw [hw0, hw2]; nlinarith [sq_nonneg S]), hw2]
  rw [hga_cone_value (2 * b) a (by rw [hsum]; exact hSpos) (by rw [hdiff]; positivity), hsum,
    hdiff, hmin]
  have hL' : b * 10 + b ^ 2 * x + x * 100 ≠ 0 := by
    have e : (1 + x * (10 / b + b / 10)) * (10 * b) = b * 10 + b ^ 2 * x + x * 100 := by
      field_simp
      ring
    rw [← e]
    exact mul_ne_zero hL.ne' (mul_ne_zero (by norm_num) hb0)
  have e0 : 2 * b * ((S - (5 + b * x) * S ^ 2 / 10) / 2) / S ^ 2 =
      b / S - b * (5 + b * x) / 10 := by
    field_simp
  have e00 : b / S = b * L := by rw [hS]; field_simp
  have e1 : -11 / 2 + 2 * b * ((S - (5 + b * x) * S ^ 2 / 10) / 2) / S ^ 2 =
      -11 / 2 + b / 2 + 10 * x := by
    rw [e0, e00, hLdef]
    field_simp
    ring
  have e2 : 10 * ((5 + b * x) * S ^ 2 / 10) / S ^ 2 = 5 + b * x := by
    field_simp
  rw [e1, e2]

end HodgeLean.Foundations.Program

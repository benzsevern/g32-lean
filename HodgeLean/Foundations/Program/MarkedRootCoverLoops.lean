import HodgeLean.Foundations.Program.MarkedRootCoverDefs

/-! # Plane geometry of the explicit lassos

The lasso about an integer mark crosses the vertical ray below a nearby mark exactly once, on
its lower arc, from left to right, and otherwise stays off the rays below the marks. After
complex conjugation this is the cut-loop shape of the punctured-plane presentation.
-/

noncomputable section
open Complex
namespace HodgeLean.Foundations.Program

/-- Integer positions of the twelve finite marks of `mr_base`, indexed by `Fin 13` (the last
entry is unused). -/
def mr_int (j : Fin 13) : ℤ := if j.val < 10 then (j.val : ℤ) - 12 else (j.val : ℤ) - 10

theorem mr_marks_eq (i : Fin 12) : mr_marks i = ((mr_int i.castSucc : ℤ) : ℂ) := by
  fin_cases i <;> simp [mr_marks, mr_base, mr_int, Fin.append, Fin.addCases] <;> norm_num

theorem mr_int_range (j : Fin 13) (hj : j.val < 12) : -12 ≤ mr_int j ∧ mr_int j ≤ 1 := by
  unfold mr_int; split_ifs <;> omega

theorem mr_int_sep (i j : Fin 13) (hi : i.val < 12) (hj : j.val < 12) (h : i ≠ j) :
    mr_int i ≠ mr_int j := by
  revert i j; decide

theorem mr_base_ne_zero (i : Fin 10) : mr_base i ≠ 0 := by
  intro h
  have h1 : ((i.val : ℂ)) = 12 := by simp [mr_base] at h; linear_combination h
  have h2 : i.val = 12 := by exact_mod_cast h1
  omega

theorem mr_radius_lt : b6t_radius mr_base < 1 / 4 := by
  unfold b6t_radius
  have hS : 0 < ∑ i : Fin 10, (‖mr_base i‖⁻¹ + ‖mr_base i - 1‖⁻¹ +
      ∑ j : Fin 10, if i = j then 0 else (dist (mr_base i) (mr_base j))⁻¹) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro i _
    have h1 : 0 < ‖mr_base i‖⁻¹ := inv_pos.2 (norm_pos_iff.2 (mr_base_ne_zero i))
    have h2 : 0 ≤ ‖mr_base i - 1‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
    have h3 : 0 ≤ ∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (mr_base i) (mr_base j))⁻¹ :=
      Finset.sum_nonneg fun j _ ↦ by split_ifs <;> positivity
    linarith
  rw [inv_lt_comm₀ (by positivity) (by norm_num)]
  linarith

theorem mr_base_eq (k : Fin 10) : mr_base k = ((mr_int ⟨k.val, by omega⟩ : ℤ) : ℂ) := by
  fin_cases k <;> simp [mr_base, mr_int] <;> norm_num

/-- The real and imaginary parts of a point on the circle of radius `1/4` started at its top. -/
theorem mr_circle_re_im (x : ℝ) :
    (I / 4 * exp (2 * Real.pi * I * (x : ℂ))).re = -Real.sin (2 * Real.pi * x) / 4 ∧
      (I / 4 * exp (2 * Real.pi * I * (x : ℂ))).im = Real.cos (2 * Real.pi * x) / 4 := by
  have : 2 * Real.pi * I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * I := by push_cast; ring
  rw [this]
  constructor
  · rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp; ring
  · rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp; ring

theorem mr_cos_two_thirds : Real.cos (2 * Real.pi * (1 / 3)) = -1 / 2 := by
  have : 2 * Real.pi * (1 / 3) = Real.pi - Real.pi / 3 := by ring
  rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num

theorem mr_cos_ge (φ : ℝ) (h0 : 0 ≤ φ) (h1 : φ ≤ 2 * Real.pi * (1 / 3)) :
    -1 / 2 ≤ Real.cos φ := by
  rw [← mr_cos_two_thirds]
  exact Real.cos_le_cos_of_nonneg_of_le_pi h0 (by nlinarith [Real.pi_pos]) h1

theorem mr_cos_ge' (φ : ℝ) (h0 : 2 * Real.pi * (2 / 3) ≤ φ) (h1 : φ ≤ 2 * Real.pi) :
    -1 / 2 ≤ Real.cos φ := by
  have : Real.cos φ = Real.cos (2 * Real.pi - φ) := by
    rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]; ring
  rw [this]
  exact mr_cos_ge _ (by linarith) (by linarith)

theorem mr_cos_le (φ : ℝ) (h0 : 2 * Real.pi * (1 / 3) ≤ φ) (h1 : φ ≤ 2 * Real.pi * (2 / 3)) :
    Real.cos φ ≤ -1 / 2 := by
  rcases le_total φ Real.pi with h | h
  · rw [← mr_cos_two_thirds]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) h h0
  · have : Real.cos φ = Real.cos (2 * Real.pi - φ) := by
      rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]; ring
    rw [this, ← mr_cos_two_thirds]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by linarith)
      (by linarith)

/-- The lasso about a real point is the circle on its middle third. -/
theorem mr_lasso_mid (n : ℝ) (s : ℝ) (h1 : 1 / 3 < s) (h2 : s ≤ 2 / 3) :
    (mr_lasso n s).re = n - Real.sin (2 * Real.pi * (3 * s - 1)) / 4 ∧
      (mr_lasso n s).im = Real.cos (2 * Real.pi * (3 * s - 1)) / 4 := by
  have hs : ¬ s ≤ 1 / 3 := by linarith
  simp only [mr_lasso, hs, h2, ite_false, ite_true]
  obtain ⟨h3, h4⟩ := mr_circle_re_im (3 * s - 1)
  constructor
  · rw [Complex.add_re, h3]; simp; ring
  · rw [Complex.add_im, h4]; simp

/-- Off its middle third the lasso stays at height at least `1/4`. -/
theorem mr_lasso_seg_im (n : ℝ) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1)
    (h : s ≤ 1 / 3 ∨ 2 / 3 < s) : 1 / 4 ≤ (mr_lasso n s).im := by
  rcases h with h | h
  · simp only [mr_lasso, h, ite_true]
    simp [mr_basePoint, mr_centre]
    nlinarith
  · have h' : ¬ s ≤ 1 / 3 := by linarith
    have h'' : ¬ s ≤ 2 / 3 := by linarith
    simp only [mr_lasso, h', h'', ite_false]
    simp [mr_basePoint, mr_centre]
    nlinarith

theorem mr_sqrt_three : 1 < Real.sqrt 3 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem mr_sin_one_third : 1 / 2 < Real.sin (2 * Real.pi * (3 * (4 / 9) - 1)) := by
  have : 2 * Real.pi * (3 * (4 / 9) - 1) = Real.pi - Real.pi / 3 := by ring
  rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]
  linarith [mr_sqrt_three]

theorem mr_sin_two_thirds : Real.sin (2 * Real.pi * (3 * (5 / 9) - 1)) < -1 / 2 := by
  have : 2 * Real.pi * (3 * (5 / 9) - 1) = Real.pi / 3 + Real.pi := by ring
  rw [this, Real.sin_add_pi, Real.sin_pi_div_three]
  linarith [mr_sqrt_three]

/-- Away from its lower arc the lasso about `n` passes only above a mark sharing its real
part, for every mark near an integer. -/
theorem mr_lasso_off (n : ℝ) (m : ℂ) (hm : |m.im| < 1 / 8)
    (hre : |m.re - n| < 1 / 8 ∨ 1 / 2 < |m.re - n|) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1)
    (hs : s ≤ 4 / 9 ∨ 5 / 9 ≤ s) (heq : (mr_lasso n s).re = m.re) :
    m.im < (mr_lasso n s).im := by
  have hmi := (abs_lt.1 hm).2
  by_cases hseg : s ≤ 1 / 3 ∨ 2 / 3 < s
  · linarith [mr_lasso_seg_im n s h0 h1 hseg]
  push Not at hseg
  obtain ⟨hre', him⟩ := mr_lasso_mid n s hseg.1 hseg.2
  set φ := 2 * Real.pi * (3 * s - 1)
  have hsin := Real.sin_sq_add_cos_sq φ
  have hsb := Real.abs_sin_le_one φ
  have hcos : -1 / 2 ≤ Real.cos φ := by
    rcases hs with hs | hs
    · exact mr_cos_ge φ (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact mr_cos_ge' φ (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hd : |m.re - n| = |Real.sin φ| / 4 := by
    rw [← heq, hre', abs_sub_comm, show n - (n - Real.sin φ / 4) = Real.sin φ / 4 by ring,
      abs_div]
    norm_num
  rcases hre with hre | hre
  · rw [hd] at hre
    have h2 : Real.sin φ ^ 2 < 1 / 4 := by
      have : |Real.sin φ| < 1 / 2 := by linarith
      nlinarith [abs_nonneg (Real.sin φ), sq_abs (Real.sin φ)]
    have hc : 1 / 2 < Real.cos φ := by nlinarith
    rw [him]; linarith
  · rw [hd] at hre; linarith

/-- On its lower arc the lasso about `n` runs below a nearby mark, inside the strip of
half-width `1/2` about it. -/
theorem mr_lasso_cross (n : ℝ) (m : ℂ) (hm : |m.im| < 1 / 8) (hre : |m.re - n| < 1 / 8)
    (s : ℝ) (h0 : 4 / 9 ≤ s) (h1 : s ≤ 5 / 9) :
    |(mr_lasso n s).re - m.re| < 1 / 2 ∧ (mr_lasso n s).im < m.im := by
  obtain ⟨hre', him⟩ := mr_lasso_mid n s (by linarith) (by linarith)
  set φ := 2 * Real.pi * (3 * s - 1)
  have hcos : Real.cos φ ≤ -1 / 2 :=
    mr_cos_le φ (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hsb := Real.abs_sin_le_one φ
  have hmi := (abs_lt.1 hm).1
  refine ⟨?_, by rw [him]; linarith⟩
  rw [hre']
  have : n - Real.sin φ / 4 - m.re = -(Real.sin φ / 4) - (m.re - n) := by ring
  rw [this]
  calc |-(Real.sin φ / 4) - (m.re - n)| ≤ |-(Real.sin φ / 4)| + |m.re - n| := abs_sub _ _
    _ < 1 / 2 := by
      rw [abs_neg, abs_div]; norm_num; linarith

/-- The lower arc enters left of a nearby mark and leaves right of it. -/
theorem mr_lasso_ends (n : ℝ) (m : ℂ) (hre : |m.re - n| < 1 / 8) :
    (mr_lasso n (4 / 9)).re < m.re ∧ m.re < (mr_lasso n (5 / 9)).re := by
  obtain ⟨h1, -⟩ := mr_lasso_mid n (4 / 9) (by norm_num) (by norm_num)
  obtain ⟨h2, -⟩ := mr_lasso_mid n (5 / 9) (by norm_num) (by norm_num)
  have := abs_lt.1 hre
  rw [h1, h2]
  constructor <;> linarith [mr_sin_one_third, mr_sin_two_thirds]

theorem mr_radius_lt8 : b6t_radius mr_base < 1 / 8 := by
  unfold b6t_radius
  have hterm : ∀ i : Fin 10, 0 ≤ ‖mr_base i‖⁻¹ + ‖mr_base i - 1‖⁻¹ +
      ∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (mr_base i) (mr_base j))⁻¹ := by
    intro i
    have h3 : 0 ≤ ∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (mr_base i) (mr_base j))⁻¹ :=
      Finset.sum_nonneg fun j _ ↦ by split_ifs <;> positivity
    positivity
  have h0 : 1 < ‖mr_base 0‖⁻¹ + ‖mr_base 0 - 1‖⁻¹ +
      ∑ j : Fin 10, if (0 : Fin 10) = j then (0 : ℝ) else (dist (mr_base 0) (mr_base j))⁻¹ := by
    have hj : (if (0 : Fin 10) = 1 then (0 : ℝ) else (dist (mr_base 0) (mr_base 1))⁻¹) ≤
        ∑ j : Fin 10, if (0 : Fin 10) = j then (0 : ℝ) else (dist (mr_base 0) (mr_base j))⁻¹ :=
      Finset.single_le_sum (f := fun j ↦ if (0 : Fin 10) = j then (0 : ℝ) else
        (dist (mr_base 0) (mr_base j))⁻¹) (fun j _ ↦ by split_ifs <;> positivity)
        (Finset.mem_univ 1)
    have hd : dist (mr_base 0) (mr_base 1) = 1 := by
      simp [mr_base, dist_eq_norm]; norm_num
    rw [if_neg (by decide), hd] at hj
    have h1 : 0 < ‖mr_base 0‖⁻¹ := inv_pos.2 (norm_pos_iff.2 (mr_base_ne_zero 0))
    have h2 : 0 ≤ ‖mr_base 0 - 1‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
    linarith
  set F : Fin 10 → ℝ := fun i ↦ ‖mr_base i‖⁻¹ + ‖mr_base i - 1‖⁻¹ +
      ∑ j : Fin 10, if i = j then 0 else (dist (mr_base i) (mr_base j))⁻¹ with hF
  have hS : 1 < ∑ i : Fin 10, F i :=
    lt_of_lt_of_le h0 (Finset.single_le_sum (f := F) (fun i _ ↦ hterm i) (Finset.mem_univ 0))
  have hpos : 0 < 4 * (1 + ∑ i : Fin 10, F i) := by linarith
  rw [inv_lt_comm₀ hpos (by norm_num)]
  linarith

/-- The twelve finite marks of a configuration, in index order. -/
def mr_fin (t : Fin 10 → ℂ) : Fin 12 → ℂ := Fin.append t ![0, 1]

/-- The integer position of the `j`-th finite mark of `mr_base`. -/
def mr_pos (j : Fin 12) : ℝ := (mr_int j.castSucc : ℝ)

theorem mr_branch_castSucc (t : Fin 10 → ℂ) (j : Fin 12) :
    b6_branch t j.castSucc = ((mr_fin t j : ℂ) : OnePoint ℂ) := by
  fin_cases j <;> simp [b6_branch, mr_fin, Fin.append, Fin.addCases]

theorem mr_branch_last (t : Fin 10 → ℂ) : b6_branch t (Fin.last 12) = OnePoint.infty := by
  simp [b6_branch, Fin.append, Fin.addCases]

theorem mr_mem_branch (t : Fin 10 → ℂ) (y : OnePoint ℂ) :
    y ∈ Set.range (b6_branch t) ↔ y = OnePoint.infty ∨ ∃ j, y = ((mr_fin t j : ℂ) : OnePoint ℂ) := by
  constructor
  · rintro ⟨j, rfl⟩
    induction j using Fin.lastCases with
    | last => exact Or.inl (mr_branch_last t)
    | cast j => exact Or.inr ⟨j, mr_branch_castSucc t j⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨Fin.last 12, mr_branch_last t⟩
    · exact ⟨j.castSucc, mr_branch_castSucc t j⟩

theorem mr_marks_pos (j : Fin 12) : mr_marks j = ((mr_pos j : ℝ) : ℂ) := by
  rw [mr_marks_eq, mr_pos]; push_cast; rfl

theorem mr_fin_near (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (j : Fin 12) :
    ‖mr_fin t j - ((mr_pos j : ℝ) : ℂ)‖ < 1 / 8 := by
  have hr := mr_radius_lt8
  by_cases hj : j.val < 10
  · have h1 : mr_fin t j = t ⟨j.val, hj⟩ := by
      obtain ⟨k, rfl⟩ : ∃ k : Fin 10, j = Fin.castAdd 2 k := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
      simp [mr_fin]
    have h2 : ((mr_pos j : ℝ) : ℂ) = mr_base ⟨j.val, hj⟩ := by
      rw [mr_base_eq, mr_pos]; push_cast; rfl
    rw [h1, h2, ← dist_eq_norm]
    exact lt_trans (ht ⟨j.val, hj⟩) hr
  · have : j = 10 ∨ j = 11 := by omega
    rcases this with rfl | rfl <;> simp [mr_fin, mr_pos, mr_int, Fin.append, Fin.addCases]

theorem mr_fin_near_parts (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (j : Fin 12) :
    |(mr_fin t j).re - mr_pos j| < 1 / 8 ∧ |(mr_fin t j).im| < 1 / 8 := by
  have h := mr_fin_near t ht j
  constructor
  · calc |(mr_fin t j).re - mr_pos j| = |(mr_fin t j - ((mr_pos j : ℝ) : ℂ)).re| := by simp
      _ ≤ ‖mr_fin t j - ((mr_pos j : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
      _ < 1 / 8 := h
  · calc |(mr_fin t j).im| = |(mr_fin t j - ((mr_pos j : ℝ) : ℂ)).im| := by simp
      _ ≤ ‖mr_fin t j - ((mr_pos j : ℝ) : ℂ)‖ := Complex.abs_im_le_norm _
      _ < 1 / 8 := h

theorem mr_pos_sep (i j : Fin 12) (h : i ≠ j) : 1 ≤ |mr_pos i - mr_pos j| := by
  have hne := mr_int_sep i.castSucc j.castSucc (by simp) (by simp)
    (fun e ↦ h (Fin.castSucc_injective _ e))
  have : (1 : ℤ) ≤ |mr_int i.castSucc - mr_int j.castSucc| := Int.one_le_abs (sub_ne_zero.2 hne)
  unfold mr_pos
  exact_mod_cast this

theorem mr_pos_strictMono : StrictMono mr_pos := by
  intro i j h
  unfold mr_pos
  have : mr_int i.castSucc < mr_int j.castSucc := by
    revert i j; decide
  exact_mod_cast this

/-- Every mark is near its own integer and at real distance more than `1/2` from the others. -/
theorem mr_fin_re_cases (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (i j : Fin 12) :
    (i = j ∧ |(mr_fin t i).re - mr_pos j| < 1 / 8) ∨
      (i ≠ j ∧ 1 / 2 < |(mr_fin t i).re - mr_pos j|) := by
  by_cases h : i = j
  · subst h; exact Or.inl ⟨rfl, (mr_fin_near_parts t ht i).1⟩
  · refine Or.inr ⟨h, ?_⟩
    have h1 := mr_pos_sep i j h
    have h2 := (mr_fin_near_parts t ht i).1
    have : |mr_pos i - mr_pos j| ≤ |(mr_fin t i).re - mr_pos j| + |(mr_fin t i).re - mr_pos i| := by
      calc |mr_pos i - mr_pos j| = |((mr_fin t i).re - mr_pos j) - ((mr_fin t i).re - mr_pos i)| := by
            ring_nf
        _ ≤ _ := abs_sub _ _
    linarith

/-- The finite marks after complex conjugation: the punctures in plane coordinates. -/
def mr_planeSet (t : Fin 10 → ℂ) : Set ℂ := Set.range fun j ↦ (starRingEnd ℂ) (mr_fin t j)

theorem mr_planeSet_finite (t : Fin 10 → ℂ) : (mr_planeSet t).Finite := Set.finite_range _

/-- Conjugated affine coordinates identify the punctured sphere with the punctured plane. -/
theorem mr_plane_exists (t : Fin 10 → ℂ) :
    ∃ Ψ : b6t_punctured t ≃ₜ {z : ℂ // z ∉ mr_planeSet t},
      ∀ (y : b6t_punctured t) (z : ℂ), (y : OnePoint ℂ) = z → (Ψ y : ℂ) = (starRingEnd ℂ) z := by
  obtain ⟨e, he⟩ := RiemannRochTop_affine_complement_homeomorph (Set.range (b6_branch t))
    ⟨Fin.last 12, mr_branch_last t⟩
  have hiff : ∀ z : ℂ, (z : OnePoint ℂ) ∉ Set.range (b6_branch t) ↔
      Complex.conjCLE.toHomeomorph z ∉ mr_planeSet t := by
    intro z
    rw [mr_mem_branch]
    simp only [mr_planeSet, Set.mem_range, not_or, not_exists]
    constructor
    · rintro ⟨-, h⟩ j hj
      apply h j
      have : z = mr_fin t j := by
        have := congrArg (starRingEnd ℂ) hj
        simpa using this.symm
      rw [this]
    · intro h
      refine ⟨OnePoint.coe_ne_infty z, fun j hj ↦ h j ?_⟩
      have := OnePoint.coe_injective hj
      rw [this]; rfl
  let c := Complex.conjCLE.toHomeomorph.subtype
    (p := fun z : ℂ ↦ (z : OnePoint ℂ) ∉ Set.range (b6_branch t))
    (q := fun z : ℂ ↦ z ∉ mr_planeSet t) hiff
  refine ⟨e.symm.trans c, fun y z hyz ↦ ?_⟩
  have h1 := he (e.symm y)
  have h0 : ((e (e.symm y)) : OnePoint ℂ) = (y : OnePoint ℂ) :=
    congrArg Subtype.val (e.apply_symm_apply y)
  rw [h0, hyz] at h1
  have h2 : (e.symm y).val = z := (OnePoint.coe_injective h1).symm
  change (starRingEnd ℂ) (e.symm y).val = _
  rw [h2]

/-- In plane coordinates the marks have pairwise distinct real parts. -/
theorem mr_planeSet_injOn (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    Set.InjOn Complex.re (mr_planeSet t) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
  simp only [Complex.conj_re] at h
  by_cases hij : i = j
  · rw [hij]
  · rcases mr_fin_re_cases t ht i j with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 hij
    · have h3 := (mr_fin_near_parts t ht j).1
      rw [h] at h2; linarith

/-- A loop is homotopic to the concatenation of its three subpaths cut at two times. -/
theorem mr_three_split {X : Type} [TopologicalSpace X] {x : X} (c : Path x x)
    (u₁ u₂ : unitInterval) (h : u₁ ≤ u₂) :
    ∃ (α : Path x (c u₁)) (δ : Path (c u₁) (c u₂)) (β : Path (c u₂) x),
      (∀ t, ∃ s, s ≤ u₁ ∧ α t = c s) ∧ (∀ t, ∃ s, u₁ ≤ s ∧ s ≤ u₂ ∧ δ t = c s) ∧
      (∀ t, ∃ s, u₂ ≤ s ∧ β t = c s) ∧ ((α.trans δ).trans β).Homotopic c := by
  let α := (c.subpath 0 u₁).cast c.source.symm rfl
  let δ := c.subpath u₁ u₂
  let β := (c.subpath u₂ 1).cast rfl c.target.symm
  refine ⟨α, δ, β, ?_, ?_, ?_, ?_⟩
  · intro t
    have hm : α t ∈ Set.range (c.subpath 0 u₁) := ⟨t, rfl⟩
    rw [Path.range_subpath_of_le _ _ _ u₁.property.1] at hm
    obtain ⟨s, hs, heq⟩ := hm
    exact ⟨s, hs.2, heq.symm⟩
  · intro t
    have hm : δ t ∈ Set.range (c.subpath u₁ u₂) := ⟨t, rfl⟩
    rw [Path.range_subpath_of_le _ _ _ h] at hm
    obtain ⟨s, hs, heq⟩ := hm
    exact ⟨s, hs.1, hs.2, heq.symm⟩
  · intro t
    have hm : β t ∈ Set.range (c.subpath u₂ 1) := ⟨t, rfl⟩
    rw [Path.range_subpath_of_le _ _ _ (unitInterval.le_one u₂)] at hm
    obtain ⟨s, hs, heq⟩ := hm
    exact ⟨s, hs.1, heq.symm⟩
  · have H1 : (α.trans δ).Homotopic ((c.subpath 0 u₂).cast c.source.symm rfl) :=
      (Path.Homotopic.subpath_trans_subpath c 0 u₁ u₂).pathCast c.source.symm rfl
    have H2 : (((c.subpath 0 u₂).cast c.source.symm rfl).trans β).Homotopic
        ((c.subpath 0 1).cast c.source.symm c.target.symm) :=
      (Path.Homotopic.subpath_trans_subpath c 0 u₂ 1).pathCast c.source.symm c.target.symm
    have H3 : (c.subpath 0 1).cast c.source.symm c.target.symm = c := by
      ext s; simp
    rw [H3] at H2
    exact (H1.hcomp (Path.Homotopic.refl β)).trans H2

theorem mr_curve_castSucc (j : Fin 12) (s : ℝ) :
    mr_curve j.castSucc s = ((mr_lasso ((mr_pos j : ℝ) : ℂ) s : ℂ) : OnePoint ℂ) := by
  have h : (j.castSucc : Fin 13).val < 12 := by simp
  simp only [mr_curve, h, dite_true]
  rw [← mr_marks_pos]
  rfl

theorem mr_curve_last (s : ℝ) : mr_curve (Fin.last 12) s = ((mr_outer s : ℂ) : OnePoint ℂ) := by
  simp [mr_curve]

/-- In conjugated plane coordinates each explicit lasso is a cut loop for its own mark: a
stem off the slits above the marks, a crossing above its mark from left to right inside the
strip of half-width `1/2`, and a stem back. -/
theorem mr_lasso_cut (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (Ψ : b6t_punctured t ≃ₜ {z : ℂ // z ∉ mr_planeSet t})
    (hΨ : ∀ (y : b6t_punctured t) (z : ℂ), (y : OnePoint ℂ) = z → (Ψ y : ℂ) = (starRingEnd ℂ) z)
    (y₀ : b6t_punctured t) (j : Fin 12) (p : Path y₀ y₀)
    (hp : ∀ s : unitInterval, (p s : OnePoint ℂ) = mr_curve j.castSucc s) :
    ∃ (q₁ q₂ : {z : ℂ // z ∉ mr_planeSet t}) (α : Path (Ψ y₀) q₁) (δ : Path q₁ q₂)
      (β : Path q₂ (Ψ y₀)),
      (∀ τ, ∀ b ∈ mr_planeSet t, (α τ : ℂ).re = b.re → (α τ : ℂ).im < b.im) ∧
      (∀ τ, |(δ τ : ℂ).re - ((starRingEnd ℂ) (mr_fin t j)).re| < 1 / 2 ∧
        ((starRingEnd ℂ) (mr_fin t j)).im < (δ τ : ℂ).im) ∧
      (∀ τ, ∀ b ∈ mr_planeSet t, (β τ : ℂ).re = b.re → (β τ : ℂ).im < b.im) ∧
      (q₁ : ℂ).re < ((starRingEnd ℂ) (mr_fin t j)).re ∧
      ((starRingEnd ℂ) (mr_fin t j)).re < (q₂ : ℂ).re ∧
      ((α.trans δ).trans β).Homotopic (p.map Ψ.continuous) := by
  set P := p.map Ψ.continuous
  have hP : ∀ s : unitInterval,
      (P s : ℂ) = (starRingEnd ℂ) (mr_lasso ((mr_pos j : ℝ) : ℂ) s) := by
    intro s
    exact hΨ (p s) _ ((hp s).trans (mr_curve_castSucc j s))
  let u₁ : unitInterval := ⟨4 / 9, by norm_num, by norm_num⟩
  let u₂ : unitInterval := ⟨5 / 9, by norm_num, by norm_num⟩
  obtain ⟨α, δ, β, hα, hδ, hβ, hH⟩ := mr_three_split P u₁ u₂ (by
    show (4 / 9 : ℝ) ≤ 5 / 9; norm_num)
  have hm := mr_fin_near_parts t ht j
  have hoff : ∀ s : unitInterval, ((s : ℝ) ≤ 4 / 9 ∨ 5 / 9 ≤ (s : ℝ)) →
      ∀ b ∈ mr_planeSet t, (P s : ℂ).re = b.re → (P s : ℂ).im < b.im := by
    rintro s hs _ ⟨j', rfl⟩ heq
    rw [hP] at heq ⊢
    simp only [Complex.conj_re, Complex.conj_im] at heq ⊢
    have hre : |(mr_fin t j').re - mr_pos j| < 1 / 8 ∨ 1 / 2 < |(mr_fin t j').re - mr_pos j| := by
      rcases mr_fin_re_cases t ht j' j with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    have := mr_lasso_off (mr_pos j) (mr_fin t j') (mr_fin_near_parts t ht j').2 hre s
      s.property.1 s.property.2 hs heq
    linarith
  refine ⟨P u₁, P u₂, α, δ, β, ?_, ?_, ?_, ?_, ?_, hH⟩
  · intro τ
    obtain ⟨s, hs, heq⟩ := hα τ
    rw [heq]
    exact hoff s (Or.inl hs)
  · intro τ
    obtain ⟨s, hs1, hs2, heq⟩ := hδ τ
    rw [heq, hP]
    obtain ⟨h1, h2⟩ := mr_lasso_cross (mr_pos j) (mr_fin t j) hm.2 hm.1 s hs1 hs2
    simp only [Complex.conj_re, Complex.conj_im]
    exact ⟨h1, by linarith⟩
  · intro τ
    obtain ⟨s, hs, heq⟩ := hβ τ
    rw [heq]
    exact hoff s (Or.inr hs)
  · rw [hP]; simp only [Complex.conj_re]
    exact (mr_lasso_ends (mr_pos j) (mr_fin t j) hm.1).1
  · rw [hP]; simp only [Complex.conj_re]
    exact (mr_lasso_ends (mr_pos j) (mr_fin t j) hm.1).2

theorem mr_fin_re_sep (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (i j : Fin 12)
    (h : i ≠ j) : 3 / 4 < |(mr_fin t i).re - (mr_fin t j).re| := by
  have h1 := mr_pos_sep i j h
  have h2 := (mr_fin_near_parts t ht i).1
  have h3 := (mr_fin_near_parts t ht j).1
  have : |mr_pos i - mr_pos j| ≤ |(mr_fin t i).re - (mr_fin t j).re| +
      |(mr_fin t i).re - mr_pos i| + |(mr_fin t j).re - mr_pos j| := by
    calc |mr_pos i - mr_pos j| = |((mr_fin t i).re - (mr_fin t j).re) -
          ((mr_fin t i).re - mr_pos i) + ((mr_fin t j).re - mr_pos j)| := by ring_nf
      _ ≤ _ := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
  linarith

/-- The strip of half-width `1/2` about a plane mark contains no other mark. -/
theorem mr_plane_iso (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (j : Fin 12) :
    ∀ b ∈ mr_planeSet t, |b.re - ((starRingEnd ℂ) (mr_fin t j)).re| < 1 / 2 →
      b = (starRingEnd ℂ) (mr_fin t j) := by
  rintro _ ⟨i, rfl⟩ h
  simp only [Complex.conj_re] at h
  by_cases hij : i = j
  · rw [hij]
  · have := mr_fin_re_sep t ht i j hij
    linarith

theorem mr_fin_injective (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    Function.Injective fun j ↦ (starRingEnd ℂ) (mr_fin t j) := by
  intro i j h
  by_contra hij
  have := mr_fin_re_sep t ht i j hij
  have h' := congrArg Complex.re h
  simp only [Complex.conj_re] at h'
  rw [h', sub_self, abs_zero] at this
  linarith

/-- Index order enumerates the plane marks. -/
def mr_planeEquiv (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) : Fin 12 ≃ mr_planeSet t :=
  Equiv.ofBijective (fun j ↦ ⟨(starRingEnd ℂ) (mr_fin t j), j, rfl⟩)
    ⟨fun i j h ↦ mr_fin_injective t ht (congrArg Subtype.val h),
      fun ⟨_, j, rfl⟩ ↦ ⟨j, rfl⟩⟩

theorem mr_planeEquiv_apply (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (j : Fin 12) :
    (mr_planeEquiv t ht j : ℂ) = (starRingEnd ℂ) (mr_fin t j) := rfl

theorem mr_plane_base (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (o : {z : ℂ // z ∉ mr_planeSet t}) (ho : (o : ℂ) = (starRingEnd ℂ) mr_basePoint) :
    ∀ b ∈ mr_planeSet t, (o : ℂ).re = b.re → (o : ℂ).im < b.im := by
  rintro _ ⟨j, rfl⟩ -
  rw [ho, Complex.conj_im, Complex.conj_im]
  have := (abs_lt.1 (mr_fin_near_parts t ht j).2).2
  have h : mr_basePoint.im = 10 := by simp [mr_basePoint, mr_centre]
  linarith

/-- In plane coordinates the twelve lasso classes are a free basis. -/
theorem mr_plane_free (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (Ψ : b6t_punctured t ≃ₜ {z : ℂ // z ∉ mr_planeSet t})
    (hΨ : ∀ (y : b6t_punctured t) (z : ℂ), (y : OnePoint ℂ) = z → (Ψ y : ℂ) = (starRingEnd ℂ) z)
    (y₀ : b6t_punctured t) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (p : Fin 12 → Path y₀ y₀)
    (hp : ∀ j (s : unitInterval), (p j s : OnePoint ℂ) = mr_curve j.castSucc s) :
    ∀ (H : Type) [Group H] (k : Fin 12 → H),
      ∃! φ : FundamentalGroup {z : ℂ // z ∉ mr_planeSet t} (Ψ y₀) →* H,
        ∀ j, φ (FundamentalGroup.fromPath ⟦(p j).map Ψ.continuous⟧) = k j := by
  have hA := mr_planeSet_finite t
  have ho := mr_plane_base t ht (Ψ y₀) (hΨ y₀ _ hy₀)
  obtain ⟨ε, hε, hiso, γ', hγ', -, hu⟩ :=
    RiemannRochTop_cut_loops_universal_property (mr_planeSet t) hA (mr_planeSet_injOn t ht) (Ψ y₀) ho
  set e := mr_planeEquiv t ht
  have key : ∀ j, FundamentalGroup.fromPath ⟦(p j).map Ψ.continuous⟧ = γ' (e j) := by
    intro j
    obtain ⟨q₁', q₂', α', δ', β', h1, h2, h3, h4, h5, hcl⟩ := hγ' (e j)
    obtain ⟨q₁, q₂, α, δ, β, ha, hd, hb, hq1, hq2, hH⟩ :=
      mr_lasso_cut t ht Ψ hΨ y₀ j (p j) (hp j)
    have hea : ((e j : mr_planeSet t) : ℂ) = (starRingEnd ℂ) (mr_fin t j) := rfl
    have hW : 0 < max (ε (e j)) (1 / 2) := lt_max_of_lt_right (by norm_num)
    have hisoW : ∀ b ∈ mr_planeSet t, |b.re - ((e j : mr_planeSet t) : ℂ).re| <
        max (ε (e j)) (1 / 2) → b = ((e j : mr_planeSet t) : ℂ) := by
      intro b hb hlt
      rcases le_total (ε (e j)) (1 / 2) with hle | hle
      · rw [max_eq_right hle] at hlt
        exact mr_plane_iso t ht j b hb hlt
      · rw [max_eq_left hle] at hlt
        exact hiso (e j) b hb hlt
    have hhom := RiemannRochTop_cut_loops_homotopic (mr_planeSet t) hA ((e j : mr_planeSet t) : ℂ) (e j).2 _ hW hisoW
      α δ β α' δ' β' ha
      (fun τ ↦ ⟨lt_of_lt_of_le (hea ▸ (hd τ).1) (le_max_right _ _), hea ▸ (hd τ).2⟩) hb
      h1 (fun τ ↦ ⟨lt_of_lt_of_le (h2 τ).1 (le_max_left _ _), (h2 τ).2⟩) h3
      (Or.inl ⟨hea ▸ hq1, h4⟩) (Or.inr ⟨hea ▸ hq2, h5⟩)
    rw [← hcl]
    exact congrArg FundamentalGroup.fromPath (Quotient.sound (hH.symm.trans hhom))
  intro H _ k
  obtain ⟨φ, hφ, huniq⟩ := hu H (fun a ↦ k (e.symm a))
  refine ⟨φ, fun j ↦ by rw [key, hφ, Equiv.symm_apply_apply], fun ψ hψ ↦ huniq ψ ?_⟩
  intro a
  obtain ⟨j, rfl⟩ := e.surjective a
  rw [← key, hψ, Equiv.symm_apply_apply]

/-- A loop whose conjugate by a stem is homotopic to `c` is the stem-conjugate of `c`. -/
theorem mr_conj_loop {X : Type} [TopologicalSpace X] {x y : X} (P : Path x x) (h : Path x y)
    (c : Path y y) (H : (h.symm.trans (P.trans h)).Homotopic c) :
    P.Homotopic ((h.trans c).trans h.symm) := by
  have e1 : ((h.trans c).trans h.symm).Homotopic
      ((h.trans (h.symm.trans (P.trans h))).trans h.symm) :=
    ((Path.Homotopic.refl h).hcomp H.symm).hcomp (Path.Homotopic.refl h.symm)
  have e2 : (h.trans (h.symm.trans (P.trans h))).Homotopic (P.trans h) :=
    (Path.Homotopic.trans_assoc h h.symm (P.trans h)).symm.trans
      (((Path.Homotopic.trans_symm h).hcomp (Path.Homotopic.refl _)).trans
        (Path.Homotopic.refl_trans _))
  have e3 : ((P.trans h).trans h.symm).Homotopic P :=
    (Path.Homotopic.trans_assoc P h h.symm).trans
      (((Path.Homotopic.refl P).hcomp (Path.Homotopic.trans_symm h)).trans
        (Path.Homotopic.trans_refl P))
  exact ((e1.trans (e2.hcomp (Path.Homotopic.refl _))).trans e3).symm

/-- A free homotopy between two parametrized loops conjugates one into the other along any
stem homotopic to the track of the base point. -/
theorem mr_loop_conj_of_homotopy {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {f g : C(Z, X)} (H : f.Homotopy g) (z : Z) (ω : Path z z) {x y : X}
    (P : Path x x) (c : Path y y) (hx : f z = x) (hy : g z = y)
    (hP : ∀ s, P s = f (ω s)) (hc : ∀ s, c s = g (ω s)) (k : Path x y)
    (hk : k.Homotopic ((H.evalAt z).cast hx.symm hy.symm)) :
    P.Homotopic ((k.trans c).trans k.symm) := by
  subst hx hy
  have hP' : P = ω.map f.continuous := by ext s; exact hP s
  have hc' : c = ω.map g.continuous := by ext s; exact hc s
  rw [Path.cast_rfl_rfl] at hk
  have h1 := mr_conj_loop P (H.evalAt z) c (by
    rw [hP', hc']
    exact RiemannRochTop_homotopy_loop_conjugacy H z ω)
  exact h1.trans ((hk.symm.hcomp (Path.Homotopic.refl c)).hcomp (Path.Homotopic.symm₂ hk.symm))

/-- Two enumerations of a set of complex numbers, both increasing in the real part, agree. -/
theorem mr_enum_unique {n : ℕ} (A : Set ℂ) (e₁ : Fin (n + 1) ≃ A) (e₂ : Fin 12 ≃ A)
    (h₁ : StrictMono fun i ↦ (e₁ i : ℂ).re) (h₂ : StrictMono fun i ↦ (e₂ i : ℂ).re) :
    ∃ h : n + 1 = 12, ∀ i, e₁ i = e₂ (Fin.cast h i) := by
  have hcard : n + 1 = 12 := by
    simpa using Fintype.card_congr (e₁.trans e₂.symm)
  refine ⟨hcard, ?_⟩
  let f : Fin 12 → Fin 12 := fun i ↦ e₂.symm (e₁ (Fin.cast hcard.symm i))
  have hf : StrictMono f := by
    intro i j hij
    have hlt : (e₁ (Fin.cast hcard.symm i) : ℂ).re < (e₁ (Fin.cast hcard.symm j) : ℂ).re :=
      h₁ hij
    by_contra hle
    push Not at hle
    have := h₂.monotone hle
    simp only [f, Equiv.apply_symm_apply] at this
    linarith
  have hs : Function.Surjective f := by
    intro i
    refine ⟨Fin.cast hcard (e₁.symm (e₂ i)), ?_⟩
    simp [f]
  have hid : ∀ i, f i = i := by
    intro i
    have := Subsingleton.elim (hf.orderIsoOfSurjective f hs) (OrderIso.refl _)
    exact congrArg (fun φ : Fin 12 ≃o Fin 12 ↦ φ i) this
  intro i
  have := hid (Fin.cast hcard i)
  simp only [f, Fin.cast_cast, Fin.cast_eq_self] at this
  rw [← this, Equiv.apply_symm_apply]

/-- The straight homotopy from the outer circle of radius `10` about `-11/2`, in conjugated
coordinates, to the circle of radius `L` about `0`. -/
def mr_hmap (L τ : ℝ) (u : ℂ) : ℂ :=
  (1 - τ) * (-11 / 2 : ℂ) + u * ((1 - τ) * (-10 * I) + τ * L)

theorem mr_hmap_ne (L R τ : ℝ) (u b : ℂ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hu : ‖u‖ = 1)
    (hb1 : ‖b + 11 / 2‖ ≤ 27 / 4) (hb2 : ‖b‖ ≤ R) (hRL : 2 * R < L) : mr_hmap L τ u ≠ b := by
  intro h
  set κ : ℂ := (1 - τ) * (-10 * I) + τ * L
  have hw : u * κ = (1 - τ) * (b + 11 / 2) + τ * b := by
    rw [← h]; simp only [mr_hmap, κ]; ring
  have hN : ‖κ‖ ≤ (1 - τ) * (27 / 4) + τ * R := by
    have := congrArg norm hw
    rw [norm_mul, hu, one_mul] at this
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖((1 - τ : ℝ) : ℂ)‖ = 1 - τ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have h2 : ‖((τ : ℝ) : ℂ)‖ = τ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
    have e1 : ((1 : ℂ) - τ) = ((1 - τ : ℝ) : ℂ) := by push_cast; ring
    rw [e1, h1, h2]
    gcongr
  have hsq : ‖κ‖ ^ 2 = (τ * L) ^ 2 + (10 * (1 - τ)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [κ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im]
    norm_num; ring
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hb2
  have hκ := norm_nonneg κ
  have hD : ‖κ‖ ^ 2 ≤ ((1 - τ) * (27 / 4) + τ * R) ^ 2 := by
    have := pow_le_pow_left₀ hκ hN 2
    exact this
  rw [hsq] at hD
  rcases eq_or_lt_of_le hτ0 with h0 | h0
  · subst h0; nlinarith
  · have hL2 : 0 < τ ^ 2 * (L ^ 2 - 4 * R ^ 2) := by
      apply mul_pos (by positivity)
      nlinarith
    nlinarith [sq_nonneg (R * τ - 9 / 4 * (1 - τ))]

/-- The track of the base point of `mr_hmap` stays off the slits above the marks. -/
theorem mr_hmap_slit (L R τ : ℝ) (b : ℂ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hb1 : -1 / 8 < b.im) (hb2 : ‖b‖ ≤ R) (hR : 1 ≤ R) (hRL : 2 * R < L)
    (heq : (mr_hmap L τ 1).re = b.re) : (mr_hmap L τ 1).im < b.im := by
  have hre : (mr_hmap L τ 1).re = -11 / 2 * (1 - τ) + τ * L := by
    simp [mr_hmap]; ring
  have him : (mr_hmap L τ 1).im = -10 * (1 - τ) := by
    simp [mr_hmap]; ring
  have hbr : b.re ≤ R := le_trans (Complex.re_le_norm b) hb2
  rw [him]
  by_contra hcon
  push Not at hcon
  rw [hre] at heq
  nlinarith

theorem mr_hmap_continuous (L : ℝ) :
    Continuous fun x : unitInterval × {u : ℂ // ‖u‖ = 1} ↦ mr_hmap L x.1 x.2 := by
  unfold mr_hmap
  have h1 : Continuous fun x : unitInterval × {u : ℂ // ‖u‖ = 1} ↦ ((x.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  have h2 : Continuous fun x : unitInterval × {u : ℂ // ‖u‖ = 1} ↦ (x.2 : ℂ) :=
    continuous_subtype_val.comp continuous_snd
  fun_prop

/-- The straight homotopy between the two outer circles, as maps of the unit circle into the
punctured plane. -/
theorem mr_outer_homotopy (A : Set ℂ) (R L : ℝ) (hRL : 2 * R < L)
    (hb1 : ∀ b ∈ A, ‖b + 11 / 2‖ ≤ 27 / 4) (hb2 : ∀ b ∈ A, ‖b‖ ≤ R) :
    ∃ (f g : C({u : ℂ // ‖u‖ = 1}, {z : ℂ // z ∉ A})) (H : f.Homotopy g),
      (∀ u, (f u : ℂ) = mr_hmap L 0 u) ∧ (∀ u, (g u : ℂ) = mr_hmap L 1 u) ∧
        ∀ τ u, (H (τ, u) : ℂ) = mr_hmap L τ u := by
  let F : C(unitInterval × {u : ℂ // ‖u‖ = 1}, {z : ℂ // z ∉ A}) :=
    ⟨fun x ↦ ⟨mr_hmap L x.1 x.2, fun hm ↦ mr_hmap_ne L R x.1 x.2 _ x.1.2.1 x.1.2.2 x.2.2
      (hb1 _ hm) (hb2 _ hm) hRL rfl⟩, (mr_hmap_continuous L).subtype_mk _⟩
  let f : C({u : ℂ // ‖u‖ = 1}, {z : ℂ // z ∉ A}) :=
    ⟨fun u ↦ F (0, u), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let g : C({u : ℂ // ‖u‖ = 1}, {z : ℂ // z ∉ A}) :=
    ⟨fun u ↦ F (1, u), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let H : f.Homotopy g :=
    { toContinuousMap := F, map_zero_left := fun _ ↦ rfl, map_one_left := fun _ ↦ rfl }
  exact ⟨f, g, H, fun _ ↦ rfl, fun _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- The positive unit circle as a loop at `1`. -/
def mr_unitLoop : Path (⟨1, by simp⟩ : {u : ℂ // ‖u‖ = 1}) ⟨1, by simp⟩ where
  toFun s := ⟨Complex.exp ((((s : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I),
    Complex.norm_exp_ofReal_mul_I _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  source' := by ext; simp
  target' := by
    ext
    simp only [Set.Icc.coe_one, one_mul]
    have : ((2 * Real.pi : ℝ) : ℂ) * I = 2 * Real.pi * I := by push_cast; ring
    rw [this, Complex.exp_two_pi_mul_I]

theorem mr_unitLoop_apply (s : unitInterval) :
    (mr_unitLoop s : ℂ) = Complex.exp ((((s : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I) := rfl

theorem mr_pos_range (j : Fin 12) : -12 ≤ mr_pos j ∧ mr_pos j ≤ 1 := by
  have h := mr_int_range j.castSucc (by simp)
  unfold mr_pos
  constructor <;> exact_mod_cast (by omega : _)

theorem mr_plane_bounds (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    ∀ b ∈ mr_planeSet t, ‖b + 11 / 2‖ ≤ 27 / 4 ∧ -1 / 8 < b.im := by
  rintro _ ⟨j, rfl⟩
  obtain ⟨h1, h2⟩ := mr_fin_near_parts t ht j
  obtain ⟨h3, h4⟩ := mr_pos_range j
  have h1' := abs_lt.1 h1
  have h2' := abs_lt.1 h2
  refine ⟨?_, by simp only [Complex.conj_im]; linarith⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : ((starRingEnd ℂ) (mr_fin t j) + 11 / 2).re = (mr_fin t j).re + 11 / 2 := by
    simp
  have him : ((starRingEnd ℂ) (mr_fin t j) + 11 / 2).im = -(mr_fin t j).im := by
    simp
  rw [hre, him, abs_neg]
  have : |(mr_fin t j).re + 11 / 2| ≤ 13 / 2 + 1 / 8 := by
    rw [abs_le]; constructor <;> linarith
  linarith

theorem mr_plane_far (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    1 ≤ ‖(starRingEnd ℂ) (mr_fin t 0)‖ := by
  have h1 := abs_lt.1 (mr_fin_near_parts t ht 0).1
  have h0 : mr_pos 0 = -12 := by simp [mr_pos, mr_int]
  refine le_trans ?_ (Complex.abs_re_le_norm _)
  simp only [Complex.conj_re]
  rw [abs_of_neg (by linarith)]
  linarith

theorem mr_planeEquiv_strictMono (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    StrictMono fun i ↦ ((mr_planeEquiv t ht i : mr_planeSet t) : ℂ).re := by
  intro i j hij
  simp only [mr_planeEquiv_apply, Complex.conj_re]
  have h1 := mr_pos_strictMono hij
  have h2 := mr_pos_sep i j (ne_of_lt hij)
  rw [abs_sub_comm, abs_of_pos (by linarith)] at h2
  have h3 := abs_lt.1 (mr_fin_near_parts t ht i).1
  have h4 := abs_lt.1 (mr_fin_near_parts t ht j).1
  linarith

theorem mr_outer_conj (s : ℝ) :
    (starRingEnd ℂ) (mr_outer s) =
      mr_hmap 0 0 (Complex.exp (((s * (2 * Real.pi) : ℝ) : ℂ) * I)) := by
  simp only [mr_outer, mr_hmap, mr_centre, map_add, map_mul, map_neg, ← Complex.exp_conj,
    Complex.conj_I, Complex.conj_ofReal, map_ofNat, map_div₀]
  have : -(2 * (Real.pi : ℂ) * -I * (s : ℂ)) = (((s * (2 * Real.pi) : ℝ) : ℂ) * I) := by
    push_cast; ring
  rw [this]
  push_cast; ring

/-- In plane coordinates the outer loop times the reversed product of the lassos is trivial. -/
theorem mr_plane_outer (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (Ψ : b6t_punctured t ≃ₜ {z : ℂ // z ∉ mr_planeSet t})
    (hΨ : ∀ (y : b6t_punctured t) (z : ℂ), (y : OnePoint ℂ) = z → (Ψ y : ℂ) = (starRingEnd ℂ) z)
    (y₀ : b6t_punctured t) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (p : Fin 12 → Path y₀ y₀)
    (hp : ∀ j (s : unitInterval), (p j s : OnePoint ℂ) = mr_curve j.castSucc s)
    (q : Path y₀ y₀) (hq : ∀ s : unitInterval, (q s : OnePoint ℂ) = mr_curve (Fin.last 12) s) :
    FundamentalGroup.fromPath ⟦q.map Ψ.continuous⟧ *
      (List.ofFn fun j ↦ FundamentalGroup.fromPath ⟦(p j).map Ψ.continuous⟧).reverse.prod =
        1 := by
  have hA := mr_planeSet_finite t
  have hi := mr_planeSet_injOn t ht
  have hne : (mr_planeSet t).Nonempty := ⟨_, 0, rfl⟩
  have hΨ₀ : (Ψ y₀ : ℂ) = (starRingEnd ℂ) mr_basePoint := hΨ y₀ _ hy₀
  have ho := mr_plane_base t ht (Ψ y₀) hΨ₀
  have happly : ∀ a : mr_planeSet t,
      (a : ℂ) = (starRingEnd ℂ) (mr_fin t ((mr_planeEquiv t ht).symm a)) := by
    intro a
    conv_lhs => rw [← (mr_planeEquiv t ht).apply_symm_apply a]
    rfl
  let g : Fin 12 → FundamentalGroup {z : ℂ // z ∉ mr_planeSet t} (Ψ y₀) :=
    fun j ↦ FundamentalGroup.fromPath ⟦(p j).map Ψ.continuous⟧
  let γA : mr_planeSet t → FundamentalGroup {z : ℂ // z ∉ mr_planeSet t} (Ψ y₀) :=
    fun a ↦ g ((mr_planeEquiv t ht).symm a)
  have hγA : ∀ a : mr_planeSet t, ∃ (q₁ q₂ : {z : ℂ // z ∉ mr_planeSet t})
      (α : Path (Ψ y₀) q₁) (d : Path q₁ q₂) (β : Path q₂ (Ψ y₀)),
      (∀ τ b, b ∈ mr_planeSet t → (α τ : ℂ).re = b.re → (α τ : ℂ).im < b.im) ∧
      (∀ τ, |(d τ : ℂ).re - (a : ℂ).re| < (fun _ ↦ (1 / 2 : ℝ)) a ∧ (a : ℂ).im < (d τ : ℂ).im) ∧
      (∀ τ b, b ∈ mr_planeSet t → (β τ : ℂ).re = b.re → (β τ : ℂ).im < b.im) ∧
      (q₁ : ℂ).re < (a : ℂ).re ∧ (a : ℂ).re < (q₂ : ℂ).re ∧
      FundamentalGroup.fromPath ⟦(α.trans d).trans β⟧ = γA a := by
    intro a
    obtain ⟨q₁, q₂, α, δ, β, hα, hδ, hβ, hq1, hq2, hH⟩ :=
      mr_lasso_cut t ht Ψ hΨ y₀ ((mr_planeEquiv t ht).symm a) (p _) (hp _)
    rw [happly a]
    exact ⟨q₁, q₂, α, δ, β, hα, hδ, hβ, hq1, hq2,
      congrArg FundamentalGroup.fromPath (Quotient.sound hH)⟩
  have hiso : ∀ (a : mr_planeSet t) (b : ℂ), b ∈ mr_planeSet t →
      |b.re - (a : ℂ).re| < (fun _ ↦ (1 / 2 : ℝ)) a → b = a := by
    intro a b hb hlt
    rw [happly a] at hlt ⊢
    exact mr_plane_iso t ht _ b hb hlt
  obtain ⟨n, e', R, L, hR, hRL, hbound, hmono, x, k, c, hk, hc, hrel⟩ :=
    RiemannRochTop_cut_family_outer_relation (mr_planeSet t) hA hne hi (fun _ ↦ 1 / 2)
      (fun _ ↦ by norm_num) hiso (Ψ y₀) ho γA hγA
  obtain ⟨hn, he'⟩ := mr_enum_unique (mr_planeSet t) e' (mr_planeEquiv t ht) hmono
    (mr_planeEquiv_strictMono t ht)
  have hlist : (List.ofFn fun i ↦ γA (e' i)) = List.ofFn g := by
    rw [List.ofFn_congr hn]
    congr 1
    funext i
    simp only [γA, he', Equiv.symm_apply_apply, Fin.cast_cast, Fin.cast_eq_self]
  rw [hlist] at hrel
  -- the outer loop
  have hb := mr_plane_bounds t ht
  obtain ⟨f, g', H, hf, hg, hH⟩ := mr_outer_homotopy (mr_planeSet t) R L hRL
    (fun b hb' ↦ (hb b hb').1) hbound
  let z : {u : ℂ // ‖u‖ = 1} := ⟨1, by simp⟩
  have hx : f z = Ψ y₀ := by
    apply Subtype.ext
    rw [hf, hΨ₀]
    simp [mr_hmap, z, mr_basePoint, mr_centre, map_ofNat]
  have hc0 : (x : ℂ) = L := by
    have := hc 0
    rw [c.source] at this
    simpa using this
  have hy : g' z = x := by
    apply Subtype.ext
    rw [hg, hc0]
    simp [mr_hmap, z]
  have hP : ∀ s, (q.map Ψ.continuous) s = f (mr_unitLoop s) := by
    intro s
    apply Subtype.ext
    rw [hf]
    change (Ψ (q s) : ℂ) = _
    rw [hΨ (q s) (mr_outer s) ((hq s).trans (mr_curve_last s)), mr_outer_conj,
      mr_unitLoop_apply]
    simp [mr_hmap]
  have hc' : ∀ s, c s = g' (mr_unitLoop s) := by
    intro s
    apply Subtype.ext
    rw [hg, hc, mr_unitLoop_apply]
    simp [mr_hmap]
  have hR1 : 1 ≤ R := (mr_plane_far t ht).trans (hbound _ ⟨0, rfl⟩)
  have hk' : k.Homotopic ((H.evalAt z).cast hx.symm hy.symm) := by
    obtain ⟨hS, -⟩ := RiemannRochTop_punctured_cut_charts_contractible (mr_planeSet t) hA
      ((starRingEnd ℂ) (mr_fin t 0)) (1 / 2) (by norm_num) (mr_plane_iso t ht 0)
    let S := {w : {z : ℂ // z ∉ mr_planeSet t} |
      ∀ b ∈ mr_planeSet t, (w : ℂ).re = b.re → (w : ℂ).im < b.im}
    let _ : ContractibleSpace S := hS
    apply RiemannRochTop_paths_homotopic_in_subset S
    · intro τ; exact fun b hb' ↦ hk τ b hb'
    · intro τ b hb' heq
      change (H (τ, z) : ℂ).re = b.re at heq
      change (H (τ, z) : ℂ).im < b.im
      rw [hH] at heq ⊢
      exact mr_hmap_slit L R τ b τ.2.1 τ.2.2 (hb b hb').2 (hbound b hb') hR1 hRL heq
  have hhom := mr_loop_conj_of_homotopy H z mr_unitLoop (q.map Ψ.continuous) c hx hy hP hc' k hk'
  have hcl : FundamentalGroup.fromPath ⟦q.map Ψ.continuous⟧ =
      (FundamentalGroup.fromPath ⟦(k.trans c.symm).trans k.symm⟧)⁻¹ := by
    rw [RiemannRochTop_based_reverse_class, inv_inv]
    exact congrArg FundamentalGroup.fromPath (Quotient.sound hhom)
  rw [hcl, hrel, inv_mul_cancel]

theorem mr_reverse_prod_last {G : Type} [Group G] (f : Fin 13 → G) :
    (List.ofFn f).reverse.prod =
      f (Fin.last 12) * (List.ofFn fun j : Fin 12 ↦ f j.castSucc).reverse.prod := by
  rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  simp

/-- A stem-conjugated loop pulled back along a homeomorphism is stem-conjugated. -/
theorem mr_transport_conj {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Φ : X ≃ₜ Y)
    {x₀ : X} (P : Path x₀ x₀) {y : Y} (k : Path (Φ x₀) y) (c : Path y y)
    (h : (P.map Φ.continuous).Homotopic ((k.trans c).trans k.symm)) :
    ∃ (K : Path x₀ (Φ.symm y)) (D : Path (Φ.symm y) (Φ.symm y)),
      (∀ s, D s = Φ.symm (c s)) ∧ P.Homotopic ((K.trans D).trans K.symm) := by
  have h1 : x₀ = Φ.symm (Φ x₀) := (Φ.symm_apply_apply x₀).symm
  refine ⟨(k.map Φ.symm.continuous).cast h1 rfl, c.map Φ.symm.continuous, fun _ ↦ rfl, ?_⟩
  have h2 := (h.map ⟨Φ.symm, Φ.symm.continuous⟩).pathCast h1 h1
  have h3 : ((P.map Φ.continuous).map Φ.symm.continuous).cast h1 h1 = P := by
    ext s; simp
  rw [h3] at h2
  convert h2 using 1
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm]
  rfl

/-- Points of the punctured sphere seen from the plane chart. -/
theorem mr_plane_symm (t : Fin 10 → ℂ) (Ψ : b6t_punctured t ≃ₜ {z : ℂ // z ∉ mr_planeSet t})
    (hΨ : ∀ (y : b6t_punctured t) (z : ℂ), (y : OnePoint ℂ) = z → (Ψ y : ℂ) = (starRingEnd ℂ) z)
    (x : {z : ℂ // z ∉ mr_planeSet t}) :
    ((Ψ.symm x : b6t_punctured t) : OnePoint ℂ) = (((starRingEnd ℂ) x : ℂ) : OnePoint ℂ) := by
  have hne : ((Ψ.symm x : b6t_punctured t) : OnePoint ℂ) ≠ OnePoint.infty := by
    intro h
    apply (Ψ.symm x).property
    rw [h]
    exact ⟨Fin.last 12, mr_branch_last t⟩
  obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hne
  have := hΨ (Ψ.symm x) z hz.symm
  rw [Ψ.apply_symm_apply] at this
  rw [← hz, this, Complex.conj_conj]

theorem mr_outer_symm (s : ℝ) :
    mr_outer (1 - s) = mr_centre + Complex.exp (((s * (2 * Real.pi) : ℝ) : ℂ) * I) * (10 * I) := by
  unfold mr_outer
  have : -(2 * (Real.pi : ℂ) * I * ((1 - s : ℝ) : ℂ)) =
      ((s * (2 * Real.pi) : ℝ) : ℂ) * I + -(2 * Real.pi * I) := by push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I]
  ring

theorem mr_circle_conj (m : ℂ) (s : ℝ) :
    (starRingEnd ℂ) ((starRingEnd ℂ) m +
      Complex.exp (((Real.pi / 4 + (1 - s) * (2 * Real.pi) : ℝ) : ℂ) * I) *
        (((1 / 2 : ℝ) / 2 : ℝ) : ℂ)) =
      m + Complex.exp (((s * (2 * Real.pi) : ℝ) : ℂ) * I) *
        (Complex.exp (((-(Real.pi / 4)) : ℝ) * I) * ((1 / 4 : ℝ) : ℂ)) := by
  rw [map_add, map_mul, Complex.conj_conj, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_ofReal, Complex.conj_I]
  have : ((Real.pi / 4 + (1 - s) * (2 * Real.pi) : ℝ) : ℂ) * -I =
      (((s * (2 * Real.pi) : ℝ) : ℂ) * I + (((-(Real.pi / 4)) : ℝ) : ℂ) * I) +
        -(2 * Real.pi * I) := by push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I]
  push_cast; ring

theorem mr_fin_center_bound (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (j : Fin 12) :
    ‖mr_fin t j - mr_centre‖ < 7 := by
  have h := (mr_plane_bounds t ht _ ⟨j, rfl⟩).1
  have : mr_fin t j - mr_centre = (starRingEnd ℂ) ((starRingEnd ℂ) (mr_fin t j) + 11 / 2) := by
    simp [mr_centre, map_ofNat]; ring
  rw [this, Complex.norm_conj]
  linarith

end HodgeLean.Foundations.Program

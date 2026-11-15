import HodgeLean.Foundations.Program.BraidCertificateEnclosures

namespace HodgeLean.Foundations.Program

abbrev b65b_Interval := ℚ × ℚ
abbrev b65b_Rectangle := b65b_Interval × b65b_Interval

def b65b_iadd (a b : b65b_Interval) : b65b_Interval := (a.1+b.1, a.2+b.2)
def b65b_ineg (a : b65b_Interval) : b65b_Interval := (-a.2, -a.1)
def b65b_imul (a b : b65b_Interval) : b65b_Interval :=
  (min (min (a.1*b.1) (a.1*b.2)) (min (a.2*b.1) (a.2*b.2)),
   max (max (a.1*b.1) (a.1*b.2)) (max (a.2*b.1) (a.2*b.2)))
def b65b_isq (a : b65b_Interval) : b65b_Interval :=
  if 0 ≤ a.1 then (a.1^2, a.2^2)
  else if a.2 ≤ 0 then (a.2^2, a.1^2)
  else (0, max (a.1^2) (a.2^2))
def b65b_csub (a b : b65b_Rectangle) : b65b_Rectangle :=
  (b65b_iadd a.1 (b65b_ineg b.1), b65b_iadd a.2 (b65b_ineg b.2))
def b65b_cmul (a b : b65b_Rectangle) : b65b_Rectangle :=
  (b65b_iadd (b65b_imul a.1 b.1) (b65b_ineg (b65b_imul a.2 b.2)),
   b65b_iadd (b65b_imul a.1 b.2) (b65b_imul a.2 b.1))
def b65b_cnorm (a : b65b_Rectangle) : b65b_Interval :=
  b65b_iadd (b65b_isq a.1) (b65b_isq a.2)
def b65b_cinv (a : b65b_Rectangle) : b65b_Rectangle :=
  let n := b65b_cnorm a
  (b65b_imul a.1 (1/n.2, 1/n.1), b65b_imul (b65b_ineg a.2) (1/n.2, 1/n.1))

theorem b65b_iadd_sound (a b : b65b_Interval) (x y : ℝ)
    (hx : x ∈ Set.Icc (a.1 : ℝ) a.2) (hy : y ∈ Set.Icc (b.1 : ℝ) b.2) :
    x+y ∈ Set.Icc ((b65b_iadd a b).1 : ℝ) (b65b_iadd a b).2 := by
  simp only [b65b_iadd, Rat.cast_add, Set.mem_Icc] at *
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem b65b_ineg_sound (a : b65b_Interval) (x : ℝ)
    (hx : x ∈ Set.Icc (a.1 : ℝ) a.2) :
    -x ∈ Set.Icc ((b65b_ineg a).1 : ℝ) (b65b_ineg a).2 := by
  simp only [b65b_ineg, Rat.cast_neg, Set.mem_Icc] at *
  constructor <;> linarith [hx.1, hx.2]

theorem b65b_mul_four_bound (x y a b c d L U : ℝ)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d)
    (hL : L ≤ a*c ∧ L ≤ a*d ∧ L ≤ b*c ∧ L ≤ b*d)
    (hU : a*c ≤ U ∧ a*d ≤ U ∧ b*c ≤ U ∧ b*d ≤ U) :
    x*y ∈ Set.Icc L U := by
  have ha : L ≤ a*y ∧ a*y ≤ U := by
    by_cases h : 0 ≤ a
    · exact ⟨hL.1.trans (mul_le_mul_of_nonneg_left hy.1 h),
        (mul_le_mul_of_nonneg_left hy.2 h).trans hU.2.1⟩
    · have h := le_of_lt (lt_of_not_ge h)
      exact ⟨hL.2.1.trans (mul_le_mul_of_nonpos_left hy.2 h),
        (mul_le_mul_of_nonpos_left hy.1 h).trans hU.1⟩
  have hb : L ≤ b*y ∧ b*y ≤ U := by
    by_cases h : 0 ≤ b
    · exact ⟨hL.2.2.1.trans (mul_le_mul_of_nonneg_left hy.1 h),
        (mul_le_mul_of_nonneg_left hy.2 h).trans hU.2.2.2⟩
    · have h := le_of_lt (lt_of_not_ge h)
      exact ⟨hL.2.2.2.trans (mul_le_mul_of_nonpos_left hy.2 h),
        (mul_le_mul_of_nonpos_left hy.1 h).trans hU.2.2.1⟩
  by_cases h : 0 ≤ y
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_right hx.1 h),
      (mul_le_mul_of_nonneg_right hx.2 h).trans hb.2⟩
  · have h := le_of_lt (lt_of_not_ge h)
    exact ⟨hb.1.trans (mul_le_mul_of_nonpos_right hx.2 h),
      (mul_le_mul_of_nonpos_right hx.1 h).trans ha.2⟩

theorem b65b_imul_sound (a b : b65b_Interval) (x y : ℝ)
    (hx : x ∈ Set.Icc (a.1 : ℝ) a.2) (hy : y ∈ Set.Icc (b.1 : ℝ) b.2) :
    x*y ∈ Set.Icc ((b65b_imul a b).1 : ℝ) (b65b_imul a b).2 := by
  simp only [b65b_imul, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  apply b65b_mul_four_bound x y _ _ _ _ _ _ hx hy
  · exact ⟨(min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  · exact ⟨(le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _),
      (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩

theorem b65b_isq_sound (a : b65b_Interval) (x : ℝ)
    (hx : x ∈ Set.Icc (a.1 : ℝ) a.2) :
    x^2 ∈ Set.Icc ((b65b_isq a).1 : ℝ) (b65b_isq a).2 := by
  unfold b65b_isq
  split_ifs with h₁ h₂
  · have h : (0 : ℝ) ≤ a.1 := by exact_mod_cast h₁
    simp only [Rat.cast_pow, Set.mem_Icc]
    exact ⟨(sq_le_sq₀ h (h.trans hx.1)).mpr hx.1,
      (sq_le_sq₀ (h.trans hx.1) ((h.trans hx.1).trans hx.2)).mpr hx.2⟩
  · have h : (a.2 : ℝ) ≤ 0 := by exact_mod_cast h₂
    simp only [Rat.cast_pow, Set.mem_Icc]
    constructor <;> nlinarith [mul_nonneg (show 0 ≤ (a.2:ℝ)-x by linarith [hx.2])
      (show 0 ≤ -x-(a.2:ℝ) by linarith [hx.2]),
      mul_nonneg (show 0 ≤ x-(a.1:ℝ) by linarith [hx.1])
      (show 0 ≤ -(a.1:ℝ)-x by linarith [hx.1, hx.2])]
  · simp only [Rat.cast_zero, Rat.cast_max, Rat.cast_pow, Set.mem_Icc]
    refine ⟨sq_nonneg _, ?_⟩
    rcases b65b_square_endpoint_bound x 0 a.1 a.2 hx with h | h
    · have h' : x^2 ≤ (a.1 : ℝ)^2 := by simpa using h
      exact h'.trans (le_max_left _ _)
    · have h' : x^2 ≤ (a.2 : ℝ)^2 := by simpa using h
      exact h'.trans (le_max_right _ _)

theorem b65b_csub_sound (a b : b65b_Rectangle) (z w : ℂ)
    (hzr : z.re ∈ Set.Icc (a.1.1 : ℝ) a.1.2)
    (hzi : z.im ∈ Set.Icc (a.2.1 : ℝ) a.2.2)
    (hwr : w.re ∈ Set.Icc (b.1.1 : ℝ) b.1.2)
    (hwi : w.im ∈ Set.Icc (b.2.1 : ℝ) b.2.2) :
    (z-w).re ∈ Set.Icc ((b65b_csub a b).1.1 : ℝ) (b65b_csub a b).1.2 ∧
    (z-w).im ∈ Set.Icc ((b65b_csub a b).2.1 : ℝ) (b65b_csub a b).2.2 := by
  have hr := b65b_iadd_sound a.1 (b65b_ineg b.1) z.re (-w.re) hzr
    (b65b_ineg_sound b.1 w.re hwr)
  have hi := b65b_iadd_sound a.2 (b65b_ineg b.2) z.im (-w.im) hzi
    (b65b_ineg_sound b.2 w.im hwi)
  constructor
  · simpa only [b65b_csub, Complex.sub_re, sub_eq_add_neg,
      Complex.add_re, Complex.neg_re] using hr
  · simpa only [b65b_csub, Complex.sub_im, sub_eq_add_neg,
      Complex.add_im, Complex.neg_im] using hi

theorem b65b_cmul_sound (a b : b65b_Rectangle) (z w : ℂ)
    (hzr : z.re ∈ Set.Icc (a.1.1 : ℝ) a.1.2)
    (hzi : z.im ∈ Set.Icc (a.2.1 : ℝ) a.2.2)
    (hwr : w.re ∈ Set.Icc (b.1.1 : ℝ) b.1.2)
    (hwi : w.im ∈ Set.Icc (b.2.1 : ℝ) b.2.2) :
    (z*w).re ∈ Set.Icc ((b65b_cmul a b).1.1 : ℝ) (b65b_cmul a b).1.2 ∧
    (z*w).im ∈ Set.Icc ((b65b_cmul a b).2.1 : ℝ) (b65b_cmul a b).2.2 := by
  have hr := b65b_iadd_sound (b65b_imul a.1 b.1) (b65b_ineg (b65b_imul a.2 b.2))
    (z.re*w.re) (-(z.im*w.im)) (b65b_imul_sound a.1 b.1 z.re w.re hzr hwr)
    (b65b_ineg_sound _ _ (b65b_imul_sound a.2 b.2 z.im w.im hzi hwi))
  have hi := b65b_iadd_sound (b65b_imul a.1 b.2) (b65b_imul a.2 b.1)
    (z.re*w.im) (z.im*w.re) (b65b_imul_sound a.1 b.2 z.re w.im hzr hwi)
    (b65b_imul_sound a.2 b.1 z.im w.re hzi hwr)
  constructor
  · simpa only [b65b_cmul, Complex.mul_re, sub_eq_add_neg] using hr
  · simpa only [b65b_cmul, Complex.mul_im] using hi

theorem b65b_cnorm_sound (a : b65b_Rectangle) (z : ℂ)
    (hzr : z.re ∈ Set.Icc (a.1.1 : ℝ) a.1.2)
    (hzi : z.im ∈ Set.Icc (a.2.1 : ℝ) a.2.2) :
    Complex.normSq z ∈ Set.Icc ((b65b_cnorm a).1 : ℝ) (b65b_cnorm a).2 := by
  simpa only [b65b_cnorm, Complex.normSq_apply, ← sq] using
    b65b_iadd_sound (b65b_isq a.1) (b65b_isq a.2) (z.re^2) (z.im^2)
      (b65b_isq_sound a.1 z.re hzr) (b65b_isq_sound a.2 z.im hzi)

theorem b65b_cinv_sound (a : b65b_Rectangle) (z : ℂ)
    (ha : 0 < (b65b_cnorm a).1)
    (hzr : z.re ∈ Set.Icc (a.1.1 : ℝ) a.1.2)
    (hzi : z.im ∈ Set.Icc (a.2.1 : ℝ) a.2.2) :
    (z⁻¹).re ∈ Set.Icc ((b65b_cinv a).1.1 : ℝ) (b65b_cinv a).1.2 ∧
    (z⁻¹).im ∈ Set.Icc ((b65b_cinv a).2.1 : ℝ) (b65b_cinv a).2.2 := by
  have hn := b65b_cnorm_sound a z hzr hzi
  have hlo : (0 : ℝ) < (b65b_cnorm a).1 := by exact_mod_cast ha
  have hp : 0 < Complex.normSq z := hlo.trans_le hn.1
  have hi : 1 / Complex.normSq z ∈ Set.Icc
      ((1 / (b65b_cnorm a).2 : ℚ) : ℝ) ((1 / (b65b_cnorm a).1 : ℚ) : ℝ) := by
    simp only [Rat.cast_div, Rat.cast_one, Set.mem_Icc]
    exact ⟨one_div_le_one_div_of_le hp hn.2, one_div_le_one_div_of_le hlo hn.1⟩
  constructor
  · simpa only [b65b_cinv, Complex.inv_re, div_eq_mul_inv, one_div, one_mul] using
      b65b_imul_sound a.1 (1/(b65b_cnorm a).2, 1/(b65b_cnorm a).1)
        z.re (1 / Complex.normSq z) hzr hi
  · simpa only [b65b_cinv, Complex.inv_im, div_eq_mul_inv, one_div, neg_mul, one_mul] using
      b65b_imul_sound (b65b_ineg a.2) (1/(b65b_cnorm a).2, 1/(b65b_cnorm a).1)
        (-z.im) (1 / Complex.normSq z) (b65b_ineg_sound a.2 z.im hzi) hi

def b65b_boxRectangle (k : Fin 12) : b65b_Rectangle :=
  (((b65b_boxCentre k).1-1/10000, (b65b_boxCentre k).1+1/10000),
   ((b65b_boxCentre k).2-1/10000, (b65b_boxCentre k).2+1/10000))

def b65b_parameterRectangle (k : Fin 12) : b65b_Rectangle :=
  (((b65b_boxCentre k).1-1/10000, (b65b_boxCentre k).1+1/10000), (0, 0))

def b65b_denominatorRectangle (k : Fin 12) : b65b_Rectangle :=
  b65b_cmul (b65b_boxRectangle k)
    (b65b_csub (b65b_parameterRectangle 6) (b65b_parameterRectangle 0))

def b65b_normalizationRectangle (k : Fin 12) : b65b_Rectangle :=
  b65b_cmul (b65b_cmul (b65b_csub (b65b_boxRectangle k) (b65b_parameterRectangle 0))
    (b65b_parameterRectangle 6)) (b65b_cinv (b65b_denominatorRectangle k))

set_option maxHeartbeats 400000 in
set_option maxRecDepth 10000 in
theorem b65b_interval_literals : ∀ k : Fin 12,
    0 < (b65b_cnorm (b65b_denominatorRectangle k)).1 ∧
    (b65b_normalizationRectangle k).1.1 = b65b_enclosure (b65b_boxIndex k) 0 ∧
    (b65b_normalizationRectangle k).1.2 = b65b_enclosure (b65b_boxIndex k) 1 ∧
    (b65b_normalizationRectangle k).2.1 = b65b_enclosure (b65b_boxIndex k) 2 ∧
    (b65b_normalizationRectangle k).2.2 = b65b_enclosure (b65b_boxIndex k) 3 := by
  intro k
  fin_cases k <;> decide +kernel

theorem b65b_boxRectangle_sound (k : Fin 12) (z : ℂ)
    (hr : |z.re - ((b65b_boxCentre k).1 : ℝ)| ≤ (1/10000 : ℝ))
    (hi : |z.im - ((b65b_boxCentre k).2 : ℝ)| ≤ (1/10000 : ℝ)) :
    z.re ∈ Set.Icc ((b65b_boxRectangle k).1.1 : ℝ) (b65b_boxRectangle k).1.2 ∧
    z.im ∈ Set.Icc ((b65b_boxRectangle k).2.1 : ℝ) (b65b_boxRectangle k).2.2 := by
  simp only [b65b_boxRectangle, Rat.cast_sub, Rat.cast_add, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat, Set.mem_Icc]
  have hr := abs_le.mp hr
  have hi := abs_le.mp hi
  exact ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩,
    ⟨by linarith [hi.1], by linarith [hi.2]⟩⟩

theorem b65b_parameterRectangle_sound (k : Fin 12) (a : ℝ)
    (ha : |a - ((b65b_boxCentre k).1 : ℝ)| ≤ (1/10000 : ℝ)) :
    (a : ℂ).re ∈ Set.Icc ((b65b_parameterRectangle k).1.1 : ℝ) (b65b_parameterRectangle k).1.2 ∧
    (a : ℂ).im ∈ Set.Icc ((b65b_parameterRectangle k).2.1 : ℝ) (b65b_parameterRectangle k).2.2 := by
  simp only [b65b_parameterRectangle, Complex.ofReal_re, Complex.ofReal_im,
    Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    Rat.cast_zero, Set.mem_Icc]
  have ha := abs_le.mp ha
  exact ⟨⟨by linarith [ha.1], by linarith [ha.2]⟩, le_rfl, le_rfl⟩

theorem b65b_normalization_interval (k : Fin 12) (z : ℂ) (a b : ℝ)
    (hzr : |z.re - ((b65b_boxCentre k).1 : ℝ)| ≤ (1/10000 : ℝ))
    (hzi : |z.im - ((b65b_boxCentre k).2 : ℝ)| ≤ (1/10000 : ℝ))
    (ha : |a - ((b65b_boxCentre 0).1 : ℝ)| ≤ (1/10000 : ℝ))
    (hb : |b - ((b65b_boxCentre 6).1 : ℝ)| ≤ (1/10000 : ℝ)) :
    (b65s_normalize a b z).re ∈ Set.Icc
      (b65b_enclosure (b65b_boxIndex k) 0 : ℝ) (b65b_enclosure (b65b_boxIndex k) 1 : ℝ) ∧
    (b65s_normalize a b z).im ∈ Set.Icc
      (b65b_enclosure (b65b_boxIndex k) 2 : ℝ) (b65b_enclosure (b65b_boxIndex k) 3 : ℝ) := by
  have hz := b65b_boxRectangle_sound k z hzr hzi
  have ha' := b65b_parameterRectangle_sound 0 a ha
  have hb' := b65b_parameterRectangle_sound 6 b hb
  have hd := b65b_csub_sound (b65b_parameterRectangle 6) (b65b_parameterRectangle 0)
    b a hb'.1 hb'.2 ha'.1 ha'.2
  have hden := b65b_cmul_sound (b65b_boxRectangle k)
    (b65b_csub (b65b_parameterRectangle 6) (b65b_parameterRectangle 0))
    z ((b : ℂ)-a) hz.1 hz.2 hd.1 hd.2
  have hinv := b65b_cinv_sound (b65b_denominatorRectangle k) (z*((b : ℂ)-a))
    (b65b_interval_literals k).1 hden.1 hden.2
  have hsub := b65b_csub_sound (b65b_boxRectangle k) (b65b_parameterRectangle 0)
    z a hz.1 hz.2 ha'.1 ha'.2
  have hnum := b65b_cmul_sound (b65b_csub (b65b_boxRectangle k) (b65b_parameterRectangle 0))
    (b65b_parameterRectangle 6) (z-a) b hsub.1 hsub.2 hb'.1 hb'.2
  have hres := b65b_cmul_sound
    (b65b_cmul (b65b_csub (b65b_boxRectangle k) (b65b_parameterRectangle 0))
      (b65b_parameterRectangle 6)) (b65b_cinv (b65b_denominatorRectangle k))
    ((z-a)*b) (z*((b : ℂ)-a))⁻¹ hnum.1 hnum.2 hinv.1 hinv.2
  change (b65s_normalize a b z).re ∈ Set.Icc
      ((b65b_normalizationRectangle k).1.1 : ℝ) (b65b_normalizationRectangle k).1.2 ∧
    (b65s_normalize a b z).im ∈ Set.Icc
      ((b65b_normalizationRectangle k).2.1 : ℝ) (b65b_normalizationRectangle k).2.2 at hres
  rcases b65b_interval_literals k with ⟨_, h0, h1, h2, h3⟩
  simpa only [h0, h1, h2, h3] using hres

end HodgeLean.Foundations.Program

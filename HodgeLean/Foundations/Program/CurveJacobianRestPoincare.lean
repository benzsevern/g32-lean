import HodgeLean.Foundations.Program.CurveJacobianRestParam
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Track B3, lane Rest: the compactly supported Poincaré lemma in the plane

A smooth function `f` on `ℂ` supported in the disc `B(c, r)` with `∫ f = 0` is the divergence
`∂ₓP + ∂ᵧR` of a smooth vector field `(P, R)` supported in the closed square of half side `r`
about `c` (`b3Rest_poincare`). Fiber integration: with `m(x) = ∫ f(x, t) dt` and a normalized bump
`φ₀`, `R(x, y) = ∫_{-r}^y (f(x, t) - m(x) φ₀(t)) dt` and `P(x, y) = φ₀(y) ∫_{-r}^x m`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff

namespace HodgeLean.Foundations.Program

/-- **Integrals with a variable upper limit** of smooth functions are smooth. -/
theorem b3Rest_contDiff_integral_upper {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {G : E → ℝ → ℝ} (hG : ContDiff ℝ ∞ (Function.uncurry G)) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : E × ℝ ↦ ∫ t in a..p.2, G p.1 t) := by
  have h : ∀ p : E × ℝ, ∫ t in a..p.2, G p.1 t =
      ∫ s in (0 : ℝ)..1, (p.2 - a) * G p.1 ((p.2 - a) * s + a) := by
    intro p
    rw [intervalIntegral.integral_const_mul]
    have := intervalIntegral.smul_integral_comp_mul_add (f := G p.1) (a := 0) (b := 1) (p.2 - a) a
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] at this
    rw [this]
  rw [show (fun p : E × ℝ ↦ ∫ t in a..p.2, G p.1 t) =
    fun p ↦ ∫ s in (0 : ℝ)..1, (p.2 - a) * G p.1 ((p.2 - a) * s + a) from funext h]
  refine b3Rest_contDiff_intervalIntegral
    (F := fun (p : E × ℝ) (s : ℝ) ↦ (p.2 - a) * G p.1 ((p.2 - a) * s + a)) ?_ 0 1
  have : ContDiff ℝ ∞ (fun q : (E × ℝ) × ℝ ↦ (q.1.2 - a) * G q.1.1 ((q.1.2 - a) * q.2 + a)) := by
    refine (contDiff_fst.snd.sub contDiff_const).mul ?_
    exact hG.comp (contDiff_fst.fst.prodMk
      (((contDiff_fst.snd.sub contDiff_const).mul contDiff_snd).add contDiff_const))
  exact this

/-- The derivative of a differentiable function along `v`, read off a line through the point. -/
theorem b3Rest_fderiv_apply_of_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : F → ℝ} {z v : F} {d : ℝ} (hg : DifferentiableAt ℝ g z)
    (h : HasDerivAt (fun s : ℝ ↦ g (z + s • v)) d 0) : fderiv ℝ g z v = d := by
  have hk : HasFDerivAt g (fderiv ℝ g z) (z + (0 : ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact hg.hasFDerivAt
  have hl : HasDerivAt (fun s : ℝ ↦ z + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  exact (hk.comp_hasDerivAt (0 : ℝ) hl).unique h

/-- An integral over `[-r, r]` of a function vanishing off `(-r, r)` is the integral over `ℝ`. -/
theorem b3Rest_intervalIntegral_eq_integral {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : ∀ t, r ≤ |t| → g t = 0) : ∫ t in -r..r, g t = ∫ t, g t := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ hg t ?_
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht
  rcases ht with ht | ht
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- The point `c + x + y i`. -/
def b3Rest_pc (c : ℂ) (x y : ℝ) : ℂ := c + ((x : ℂ) + (y : ℂ) * Complex.I)

theorem b3Rest_pc_re (c : ℂ) (x y : ℝ) : (b3Rest_pc c x y - c).re = x := by
  simp [b3Rest_pc]

theorem b3Rest_pc_im (c : ℂ) (x y : ℝ) : (b3Rest_pc c x y - c).im = y := by
  simp [b3Rest_pc]

theorem b3Rest_pc_eq (c z : ℂ) : b3Rest_pc c (z - c).re (z - c).im = z := by
  simp only [b3Rest_pc]
  rw [Complex.re_add_im, add_sub_cancel]

theorem b3Rest_pc_add_re (c z : ℂ) (s : ℝ) :
    z + s • (1 : ℂ) = b3Rest_pc c ((z - c).re + s) (z - c).im := by
  conv_lhs => rw [← b3Rest_pc_eq c z]
  simp only [b3Rest_pc, Complex.real_smul, mul_one]
  push_cast
  ring

theorem b3Rest_pc_add_im (c z : ℂ) (s : ℝ) :
    z + s • Complex.I = b3Rest_pc c (z - c).re ((z - c).im + s) := by
  conv_lhs => rw [← b3Rest_pc_eq c z]
  simp only [b3Rest_pc, Complex.real_smul]
  push_cast
  ring

theorem b3Rest_contDiff_pc (c : ℂ) :
    ContDiff ℝ ∞ (Function.uncurry (b3Rest_pc c)) := by
  unfold b3Rest_pc
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ ((p.1 : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ ((p.2 : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  exact contDiff_const.add (h1.add (h2.mul contDiff_const))

theorem b3Rest_abs_le_norm_pc (c : ℂ) (x y : ℝ) : |x| ≤ ‖b3Rest_pc c x y - c‖ ∧
    |y| ≤ ‖b3Rest_pc c x y - c‖ := by
  constructor
  · have := Complex.abs_re_le_norm (b3Rest_pc c x y - c)
    rwa [b3Rest_pc_re] at this
  · have := Complex.abs_im_le_norm (b3Rest_pc c x y - c)
    rwa [b3Rest_pc_im] at this

section Poincare

variable {f : ℂ → ℝ} {c : ℂ} {r : ℝ}

/-- The normalized bump on the line used for fiber integration. -/
def b3Rest_phi0 (r : ℝ) (hr : 0 < r) : ℝ → ℝ :=
  (⟨r / 2, r, half_pos hr, half_lt_self hr⟩ : ContDiffBump (0 : ℝ)).normed volume

theorem b3Rest_phi0_contDiff (hr : 0 < r) : ContDiff ℝ ∞ (b3Rest_phi0 r hr) :=
  ContDiffBump.contDiff_normed _

theorem b3Rest_phi0_eq_zero (hr : 0 < r) {t : ℝ} (ht : r ≤ |t|) : b3Rest_phi0 r hr t = 0 := by
  have : t ∉ Function.support (b3Rest_phi0 r hr) := by
    rw [b3Rest_phi0, ContDiffBump.support_normed_eq]
    simp only [mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
    exact ht
  exact Function.notMem_support.1 this

theorem b3Rest_phi0_integral (hr : 0 < r) : ∫ t in -r..r, b3Rest_phi0 r hr t = 1 := by
  rw [b3Rest_intervalIntegral_eq_integral hr fun t ht ↦ b3Rest_phi0_eq_zero hr ht]
  exact ContDiffBump.integral_normed _

/-- `f` in rectangular coordinates about `c`. -/
def b3Rest_rect (f : ℂ → ℝ) (c : ℂ) (x y : ℝ) : ℝ := f (b3Rest_pc c x y)

/-- The fiber integral `m(x) = ∫_{-r}^r f(x, t) dt`. -/
def b3Rest_fib (f : ℂ → ℝ) (c : ℂ) (r x : ℝ) : ℝ := ∫ t in -r..r, b3Rest_rect f c x t

/-- The integrand of the second component. -/
def b3Rest_Rg (f : ℂ → ℝ) (c : ℂ) (r : ℝ) (hr : 0 < r) (x t : ℝ) : ℝ :=
  b3Rest_rect f c x t - b3Rest_fib f c r x * b3Rest_phi0 r hr t

/-- The second component `R(x, y) = ∫_{-r}^y (f(x, t) - m(x) φ₀(t)) dt`. -/
def b3Rest_Rt (f : ℂ → ℝ) (c : ℂ) (r : ℝ) (hr : 0 < r) (x y : ℝ) : ℝ :=
  ∫ t in -r..y, b3Rest_Rg f c r hr x t

/-- The first component `P(x, y) = φ₀(y) ∫_{-r}^x m`. -/
def b3Rest_Pt (f : ℂ → ℝ) (c : ℂ) (r : ℝ) (hr : 0 < r) (x y : ℝ) : ℝ :=
  b3Rest_phi0 r hr y * ∫ s in -r..x, b3Rest_fib f c r s

theorem b3Rest_rect_contDiff (hf : ContDiff ℝ ∞ f) (c : ℂ) :
    ContDiff ℝ ∞ (Function.uncurry (b3Rest_rect f c)) :=
  hf.comp (b3Rest_contDiff_pc c)

theorem b3Rest_rect_eq_zero (hs : tsupport f ⊆ ball c r) {x y : ℝ}
    (h : r ≤ |x| ∨ r ≤ |y|) : b3Rest_rect f c x y = 0 := by
  show f (b3Rest_pc c x y) = 0
  refine image_eq_zero_of_notMem_tsupport fun hm ↦ ?_
  have := hs hm
  rw [mem_ball, dist_eq_norm] at this
  have h2 := b3Rest_abs_le_norm_pc c x y
  rcases h with h | h <;> linarith [h2.1, h2.2]

theorem b3Rest_fib_contDiff (hf : ContDiff ℝ ∞ f) (c : ℂ) (r : ℝ) :
    ContDiff ℝ ∞ (b3Rest_fib f c r) :=
  b3Rest_contDiff_intervalIntegral (E := ℝ) (b3Rest_rect_contDiff hf c) _ _

theorem b3Rest_fib_eq_zero (hs : tsupport f ⊆ ball c r) {x : ℝ} (hx : r ≤ |x|) :
    b3Rest_fib f c r x = 0 := by
  unfold b3Rest_fib
  rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ))
    fun t _ ↦ b3Rest_rect_eq_zero hs (Or.inl hx)]
  simp

theorem b3Rest_integral_fib (hf : ContDiff ℝ ∞ f) (hr : 0 < r) (hs : tsupport f ⊆ ball c r) :
    ∫ x in -r..r, b3Rest_fib f c r x = ∫ z, f z := by
  have hFc : Continuous (Function.uncurry (b3Rest_rect f c)) :=
    (b3Rest_rect_contDiff hf c).continuous
  have hFs : HasCompactSupport (Function.uncurry (b3Rest_rect f c)) := by
    refine HasCompactSupport.intro (K := Icc (-r) r ×ˢ Icc (-r) r)
      (isCompact_Icc.prod isCompact_Icc) fun p hp ↦ ?_
    refine b3Rest_rect_eq_zero hs ?_
    simp only [mem_prod, mem_Icc, not_and_or, not_le] at hp
    rcases hp with (h | h) | (h | h)
    · left; rw [abs_of_neg (by linarith)]; linarith
    · left; rw [abs_of_pos (by linarith)]; linarith
    · right; rw [abs_of_neg (by linarith)]; linarith
    · right; rw [abs_of_pos (by linarith)]; linarith
  have h1 : ∫ z, f z = ∫ z, f (c + z) := (integral_add_left_eq_self (fun z ↦ f z) c).symm
  have h2 : ∫ z, f (c + z) = ∫ p : ℝ × ℝ, Function.uncurry (b3Rest_rect f c) p := by
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
    congr 1
    funext p
    simp only [Function.uncurry, b3Rest_rect, b3Rest_pc, Complex.measurableEquivRealProd_symm_apply]
    congr 2
    apply Complex.ext <;> simp
  rw [h1, h2, Measure.volume_eq_prod, integral_prod _ (hFc.integrable_of_hasCompactSupport hFs),
    b3Rest_intervalIntegral_eq_integral hr fun x hx ↦ b3Rest_fib_eq_zero hs hx]
  congr 1
  funext x
  rw [b3Rest_fib, b3Rest_intervalIntegral_eq_integral hr fun t ht ↦
    b3Rest_rect_eq_zero hs (Or.inr ht)]
  rfl

theorem b3Rest_fibInt_contDiff (hf : ContDiff ℝ ∞ f) (c : ℂ) (r : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ ↦ ∫ s in -r..x, b3Rest_fib f c r s) := by
  have h := b3Rest_contDiff_integral_upper (E := ℝ) (G := fun _ t ↦ b3Rest_fib f c r t)
    ((b3Rest_fib_contDiff hf c r).comp contDiff_snd) (-r)
  exact h.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)

theorem b3Rest_hasDerivAt_fibInt (hf : ContDiff ℝ ∞ f) (c : ℂ) (r x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ ∫ s in -r..x, b3Rest_fib f c r s) (b3Rest_fib f c r x) x := by
  have hc := (b3Rest_fib_contDiff hf c r).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem b3Rest_fibInt_eq_zero (hf : ContDiff ℝ ∞ f) (hr : 0 < r) (hs : tsupport f ⊆ ball c r)
    (h0 : ∫ z, f z = 0) {x : ℝ} (hx : r ≤ |x|) : ∫ s in -r..x, b3Rest_fib f c r s = 0 := by
  have hc := (b3Rest_fib_contDiff hf c r).continuous
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0] at hx
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := r) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _), b3Rest_integral_fib hf hr hs, h0, zero_add,
      intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_]
    · simp
    · rw [uIcc_of_le hx] at ht
      exact b3Rest_fib_eq_zero hs (by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1)
  · rw [abs_of_neg hx0] at hx
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_]
    · simp
    · rw [uIcc_of_ge (by linarith)] at ht
      exact b3Rest_fib_eq_zero hs (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])

theorem b3Rest_Rg_contDiff (hf : ContDiff ℝ ∞ f) (c : ℂ) (hr : 0 < r) :
    ContDiff ℝ ∞ (Function.uncurry (b3Rest_Rg f c r hr)) :=
  (b3Rest_rect_contDiff hf c).sub
    (((b3Rest_fib_contDiff hf c r).comp contDiff_fst).mul ((b3Rest_phi0_contDiff hr).comp contDiff_snd))

theorem b3Rest_Rt_contDiff (hf : ContDiff ℝ ∞ f) (c : ℂ) (hr : 0 < r) :
    ContDiff ℝ ∞ (Function.uncurry (b3Rest_Rt f c r hr)) :=
  b3Rest_contDiff_integral_upper (E := ℝ) (b3Rest_Rg_contDiff hf c hr) (-r)

theorem b3Rest_hasDerivAt_Rt (hf : ContDiff ℝ ∞ f) (c : ℂ) (hr : 0 < r) (x y : ℝ) :
    HasDerivAt (fun y ↦ b3Rest_Rt f c r hr x y) (b3Rest_Rg f c r hr x y) y := by
  have hc : Continuous (b3Rest_Rg f c r hr x) :=
    (b3Rest_Rg_contDiff hf c hr).continuous.comp (continuous_const.prodMk continuous_id)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem b3Rest_Rg_eq_zero (hr : 0 < r) (hs : tsupport f ⊆ ball c r) {x t : ℝ}
    (h : r ≤ |x| ∨ r ≤ |t|) : b3Rest_Rg f c r hr x t = 0 := by
  unfold b3Rest_Rg
  rw [b3Rest_rect_eq_zero hs h]
  rcases h with h | h
  · rw [b3Rest_fib_eq_zero hs h]; ring
  · rw [b3Rest_phi0_eq_zero hr h]; ring

theorem b3Rest_Rt_eq_zero (hf : ContDiff ℝ ∞ f) (hr : 0 < r) (hs : tsupport f ⊆ ball c r)
    {x y : ℝ} (h : r ≤ |x| ∨ r ≤ |y|) : b3Rest_Rt f c r hr x y = 0 := by
  have hc : Continuous (b3Rest_Rg f c r hr x) :=
    (b3Rest_Rg_contDiff hf c hr).continuous.comp (continuous_const.prodMk continuous_id)
  unfold b3Rest_Rt
  rcases h with hx | hy
  · rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ))
      fun t _ ↦ b3Rest_Rg_eq_zero hr hs (Or.inl hx)]
    simp
  rcases le_or_gt 0 y with hy0 | hy0
  · rw [abs_of_nonneg hy0] at hy
    have hm : ∫ t in -r..r, b3Rest_Rg f c r hr x t = 0 := by
      have hrc : Continuous (b3Rest_rect f c x) :=
        (b3Rest_rect_contDiff hf c).continuous.comp (continuous_const.prodMk continuous_id)
      unfold b3Rest_Rg
      rw [intervalIntegral.integral_sub (hrc.intervalIntegrable _ _)
        (((b3Rest_phi0_contDiff hr).continuous.const_mul _).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, b3Rest_phi0_integral hr, mul_one]
      exact sub_self _
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := r) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _), hm, zero_add,
      intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_]
    · simp
    · rw [uIcc_of_le hy] at ht
      exact b3Rest_Rg_eq_zero hr hs
        (Or.inr (by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1))
  · rw [abs_of_neg hy0] at hy
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_]
    · simp
    · rw [uIcc_of_ge (by linarith)] at ht
      exact b3Rest_Rg_eq_zero hr hs
        (Or.inr (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2]))

theorem b3Rest_Pt_eq_zero (hf : ContDiff ℝ ∞ f) (hr : 0 < r) (hs : tsupport f ⊆ ball c r)
    (h0 : ∫ z, f z = 0) {x y : ℝ} (h : r ≤ |x| ∨ r ≤ |y|) : b3Rest_Pt f c r hr x y = 0 := by
  unfold b3Rest_Pt
  rcases h with h | h
  · rw [b3Rest_fibInt_eq_zero hf hr hs h0 h, mul_zero]
  · rw [b3Rest_phi0_eq_zero hr h, zero_mul]

/-- The real-and-imaginary coordinates about `c`. -/
def b3Rest_rc (c : ℂ) (z : ℂ) : ℝ × ℝ := ((z - c).re, (z - c).im)

theorem b3Rest_rc_contDiff (c : ℂ) : ContDiff ℝ ∞ (b3Rest_rc c) :=
  (Complex.reCLM.contDiff.comp (contDiff_id.sub contDiff_const)).prodMk
    (Complex.imCLM.contDiff.comp (contDiff_id.sub contDiff_const))

/-- A function of `z` vanishing unless both coordinates of `z - c` are less than `r` has
topological support in the closed disc of radius `2 r`. -/
theorem b3Rest_tsupport_sub_of_square {g : ℂ → ℝ}
    (hg : ∀ z : ℂ, r ≤ |(z - c).re| ∨ r ≤ |(z - c).im| → g z = 0) :
    tsupport g ⊆ closedBall c (2 * r) := by
  have hcl : IsClosed {z : ℂ | |(z - c).re| ≤ r ∧ |(z - c).im| ≤ r} := by
    exact (isClosed_le (by fun_prop : Continuous fun z : ℂ ↦ |(z - c).re|) continuous_const).inter
      (isClosed_le (by fun_prop : Continuous fun z : ℂ ↦ |(z - c).im|) continuous_const)
  refine (closure_minimal (fun z hz ↦ ?_) hcl).trans fun z hz ↦ ?_
  · by_contra h
    simp only [mem_ofPred_eq, not_and_or, not_le] at h
    exact hz (hg z (h.imp le_of_lt le_of_lt))
  · rw [mem_closedBall, dist_eq_norm]
    linarith [Complex.norm_le_abs_re_add_abs_im (z - c), hz.1, hz.2]

/-- **The compactly supported Poincaré lemma in the plane**: a smooth function supported in
`B(c, r)` with integral zero is the divergence `∂₁P + ∂_i R` of a smooth vector field supported in
the closed disc of radius `2 r`. -/
theorem b3Rest_poincare (hf : ContDiff ℝ ∞ f) (hr : 0 < r) (hs : tsupport f ⊆ ball c r)
    (h0 : ∫ z, f z = 0) :
    ∃ P R : ℂ → ℝ, ContDiff ℝ ∞ P ∧ ContDiff ℝ ∞ R ∧ tsupport P ⊆ closedBall c (2 * r) ∧
      tsupport R ⊆ closedBall c (2 * r) ∧ ∀ z, fderiv ℝ P z 1 + fderiv ℝ R z Complex.I = f z := by
  set P : ℂ → ℝ := fun z ↦ Function.uncurry (b3Rest_Pt f c r hr) (b3Rest_rc c z)
  set R : ℂ → ℝ := fun z ↦ Function.uncurry (b3Rest_Rt f c r hr) (b3Rest_rc c z)
  have hPt : ContDiff ℝ ∞ (Function.uncurry (b3Rest_Pt f c r hr)) :=
    ((b3Rest_phi0_contDiff hr).comp contDiff_snd).mul
      ((b3Rest_fibInt_contDiff hf c r).comp contDiff_fst)
  have hP : ContDiff ℝ ∞ P := hPt.comp (b3Rest_rc_contDiff c)
  have hR : ContDiff ℝ ∞ R := (b3Rest_Rt_contDiff hf c hr).comp (b3Rest_rc_contDiff c)
  refine ⟨P, R, hP, hR, b3Rest_tsupport_sub_of_square fun z hz ↦ ?_,
    b3Rest_tsupport_sub_of_square fun z hz ↦ ?_, fun z ↦ ?_⟩
  · exact b3Rest_Pt_eq_zero hf hr hs h0 hz
  · exact b3Rest_Rt_eq_zero hf hr hs hz
  set x := (z - c).re
  set y := (z - c).im
  have h1 : fderiv ℝ P z 1 = b3Rest_phi0 r hr y * b3Rest_fib f c r x := by
    refine b3Rest_fderiv_apply_of_line (hP.differentiable (by simp) z) ?_
    have he : (fun s : ℝ ↦ P (z + s • (1 : ℂ))) =
        fun s ↦ b3Rest_phi0 r hr y * ∫ u in -r..(x + s), b3Rest_fib f c r u := by
      funext s
      simp only [P, b3Rest_rc, Function.uncurry, b3Rest_Pt, b3Rest_pc_add_re c z s, b3Rest_pc_re,
        b3Rest_pc_im, x, y]
    rw [he]
    have hd : HasDerivAt (fun x : ℝ ↦ ∫ s in -r..x, b3Rest_fib f c r s) (b3Rest_fib f c r x)
        (x + 0) := by
      rw [add_zero]; exact b3Rest_hasDerivAt_fibInt hf c r x
    simpa only [add_zero] using (hd.comp_const_add x 0).const_mul (b3Rest_phi0 r hr y)
  have h2 : fderiv ℝ R z Complex.I = b3Rest_Rg f c r hr x y := by
    refine b3Rest_fderiv_apply_of_line (hR.differentiable (by simp) z) ?_
    have he : (fun s : ℝ ↦ R (z + s • Complex.I)) = fun s ↦ b3Rest_Rt f c r hr x (y + s) := by
      funext s
      simp only [R, b3Rest_rc, Function.uncurry, b3Rest_pc_add_im c z s, b3Rest_pc_re,
        b3Rest_pc_im, x, y]
    rw [he]
    have hd : HasDerivAt (fun y ↦ b3Rest_Rt f c r hr x y) (b3Rest_Rg f c r hr x y) (y + 0) := by
      rw [add_zero]; exact b3Rest_hasDerivAt_Rt hf c hr x y
    simpa only [add_zero] using hd.comp_const_add y 0
  rw [h1, h2, b3Rest_Rg, b3Rest_rect, b3Rest_pc_eq]
  ring

end Poincare

end HodgeLean.Foundations.Program

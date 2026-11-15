import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian6ThetaDefs
import HodgeLean.Ported.TauCeti.TauCeti.Analysis.Contour.Argument.Principle
import Mathlib.Topology.Algebra.Module.Cardinality

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Curves
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open Set Filter Topology
open scoped CategoryTheory.MonObj
namespace HodgeLean.Adapters
local instance : IsCommMonObj E :=
  isCommMonObj_of_complexSelfProductIntegral E (complexSelfProductIntegral_of_isIntegral E)

/-- The shifted theta series vanishes at the origin by parity and quasi-periodicity.
Source: `jacobiTheta₂_neg_left`, `jacobiTheta₂_add_left`, `jacobiTheta₂_add_left'`. -/
theorem bh6_theta_zero (τ : ℂ) : bh6_theta τ 0 = 0 := by
  let z := -(1 + τ) / 2
  have he : -z = (z + τ) + 1 := by dsimp [z]; ring
  have hx : -(Real.pi : ℂ) * Complex.I * (τ + 2 * z) = Real.pi * Complex.I := by
    dsimp [z]; ring
  have h := jacobiTheta₂_neg_left z τ
  rw [he, jacobiTheta₂_add_left, jacobiTheta₂_add_left', hx,
    Complex.exp_pi_mul_I, neg_one_mul] at h
  have hz : jacobiTheta₂ z τ = 0 := by linear_combination -h / 2
  simpa only [bh6_theta, zero_sub, z, neg_div] using hz

/-- Analyticity follows from the existing differentiated theta series.
Source: `differentiableAt_jacobiTheta₂_fst`. -/
theorem bh6_theta_analytic (τ : ℂ) (hτ : 0 < τ.im) :
    AnalyticOnNhd ℂ (bh6_theta τ) univ := by
  have hd : Differentiable ℂ (bh6_theta τ) := by
    intro z
    exact (differentiableAt_jacobiTheta₂_fst (z - (1 + τ) / 2) hτ).comp z
      (differentiableAt_id.sub_const _)
  exact fun z _ ↦ hd.analyticAt z

private lemma jacobiTheta₂_add_one_eq_zero_iff (z τ : ℂ) :
    jacobiTheta₂ (z + 1) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by
  rw [jacobiTheta₂_add_left]

private lemma jacobiTheta₂_add_tau_eq_zero_iff (z τ : ℂ) :
    jacobiTheta₂ (z + τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by
  rw [jacobiTheta₂_add_left', mul_eq_zero]
  exact or_iff_right (Complex.exp_ne_zero _)

private lemma jacobiTheta₂_add_int_eq_zero_iff (z τ : ℂ) (a : ℤ) :
    jacobiTheta₂ (z + a) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by
  induction a using Int.induction_on with
  | zero => simp
  | succ a ih =>
      rw [Int.cast_add, Int.cast_one, ← add_assoc, jacobiTheta₂_add_one_eq_zero_iff, ih]
  | pred a ih =>
      rw [show ((-a - 1 : ℤ) : ℂ) = ((-a : ℤ) : ℂ) - 1 by push_cast; ring]
      have h := jacobiTheta₂_add_one_eq_zero_iff (z + ((-a : ℤ) : ℂ) - 1) τ
      rw [show z + ((-a : ℤ) : ℂ) - 1 + 1 = z + ((-a : ℤ) : ℂ) by ring] at h
      simpa only [sub_eq_add_neg, add_assoc] using h.symm.trans ih

private lemma jacobiTheta₂_add_int_tau_eq_zero_iff (z τ : ℂ) (b : ℤ) :
    jacobiTheta₂ (z + τ * b) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by
  induction b using Int.induction_on with
  | zero => simp
  | succ b ih =>
      rw [Int.cast_add, Int.cast_one, mul_add, mul_one, ← add_assoc,
        jacobiTheta₂_add_tau_eq_zero_iff, ih]
  | pred b ih =>
      rw [show τ * ((-b - 1 : ℤ) : ℂ) = τ * ((-b : ℤ) : ℂ) - τ by push_cast; ring]
      have h := jacobiTheta₂_add_tau_eq_zero_iff (z + τ * ((-b : ℤ) : ℂ) - τ) τ
      rw [show z + τ * ((-b : ℤ) : ℂ) - τ + τ =
        z + τ * ((-b : ℤ) : ℂ) by ring] at h
      simpa only [sub_eq_add_neg, add_assoc] using h.symm.trans ih

/-- Integer period translates of the origin are theta zeros.
Source: Mathlib's theta quasi-periodicity; Mumford, *Tata Lectures on Theta I*, section 1. -/
theorem bh6_theta_lattice_zero_aux (τ : ℂ) (hτ : 0 < τ.im) (a b : ℤ) :
    bh6_theta τ ((a : ℂ) + τ * b) = 0 := by
  rw [bh6_theta]
  have h0 : jacobiTheta₂ (-(1 + τ) / 2) τ = 0 := by
    simpa only [bh6_theta, zero_sub, neg_div] using bh6_theta_zero τ
  rw [show (a : ℂ) + τ * b - (1 + τ) / 2 =
      (-(1 + τ) / 2 + τ * b) + a by ring,
    jacobiTheta₂_add_int_eq_zero_iff,
    jacobiTheta₂_add_int_tau_eq_zero_iff]
  exact h0

private lemma bh6_theta_not_identically_zero (τ : ℂ) (hτ : 0 < τ.im) :
    bh6_theta τ ≠ 0 := by
  intro hzero
  have hz : ∀ x : ℝ, jacobiTheta₂ (x : ℂ) τ = 0 := by
    intro x
    have h := congrFun hzero ((x : ℂ) + (1 + τ) / 2)
    simpa only [bh6_theta, add_sub_cancel_right, Pi.zero_apply] using h
  have hi := HodgeLean.Foundations.AppellHumbert.integral_jacobiTheta₂ hτ
  simp only [hz, intervalIntegral.integral_zero] at hi
  exact zero_ne_one hi

private lemma bh6_theta_order_ne_top (τ : ℂ) (hτ : 0 < τ.im) (z : ℂ) :
    analyticOrderAt (bh6_theta τ) z ≠ ⊤ := by
  intro h
  exact bh6_theta_not_identically_zero τ hτ
    ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      (fun w ↦ bh6_theta_analytic τ hτ w (mem_univ w))).mp h)

private lemma bh6_theta_compact_zeros_finite (τ : ℂ) (hτ : 0 < τ.im)
    (K : Set ℂ) (hK : IsCompact K) :
    {z ∈ K | bh6_theta τ z = 0}.Finite := by
  obtain ⟨w, hw⟩ := Function.ne_iff.mp (bh6_theta_not_identically_zero τ hτ)
  have hc := (bh6_theta_analytic τ hτ).preimage_zero_mem_codiscrete hw
  have hcK : (bh6_theta τ) ⁻¹' {0}ᶜ ∈ codiscreteWithin K :=
    (Filter.codiscreteWithin_mono (subset_univ K)) hc
  convert hK.finite_sdiff_of_mem_codiscreteWithin hcK using 1
  ext z
  simp

private lemma bh6_theta_deriv_eq (τ : ℂ) (hτ : 0 < τ.im) (z : ℂ) :
    deriv (bh6_theta τ) z = jacobiTheta₂' (z - (1 + τ) / 2) τ := by
  change deriv (fun z ↦ jacobiTheta₂ (z - (1 + τ) / 2) τ) z = _
  simpa only [Function.comp_def, id_eq, mul_one] using
    ((hasDerivAt_jacobiTheta₂_fst (z - (1 + τ) / 2) hτ).comp z
      ((hasDerivAt_id z).sub_const ((1 + τ) / 2))).deriv

private lemma bh6_theta_logDeriv_add_one (τ : ℂ) (hτ : 0 < τ.im) (z : ℂ) :
    logDeriv (bh6_theta τ) (z + 1) = logDeriv (bh6_theta τ) z := by
  simp only [logDeriv_apply, bh6_theta_deriv_eq τ hτ, bh6_theta]
  rw [show z + 1 - (1 + τ) / 2 = (z - (1 + τ) / 2) + 1 by ring,
    jacobiTheta₂'_add_left, jacobiTheta₂_add_left]

private lemma bh6_theta_logDeriv_add_tau (τ : ℂ) (hτ : 0 < τ.im) (z : ℂ)
    (hz : bh6_theta τ z ≠ 0) :
    logDeriv (bh6_theta τ) (z + τ) =
      logDeriv (bh6_theta τ) z - 2 * Real.pi * Complex.I := by
  change jacobiTheta₂ (z - (1 + τ) / 2) τ ≠ 0 at hz
  simp only [logDeriv_apply, bh6_theta_deriv_eq τ hτ, bh6_theta]
  rw [show z + τ - (1 + τ) / 2 = (z - (1 + τ) / 2) + τ by ring,
    jacobiTheta₂'_add_left', jacobiTheta₂_add_left', mul_div_mul_left _ _
      (Complex.exp_ne_zero _), sub_div, mul_div_cancel_right₀ _ hz]

private def bh6_rectIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x in a..b, f (x + c * Complex.I)) -
    (∫ x in a..b, f (x + d * Complex.I)) +
    Complex.I * (∫ y in c..d, f (b + y * Complex.I)) -
    Complex.I * (∫ y in c..d, f (a + y * Complex.I))

private lemma bh6_rectIntegral_periodic (f : ℂ → ℂ) (a c d : ℝ)
    (hf : Function.Periodic f 1) :
    bh6_rectIntegral f a (a + 1) c d =
      (∫ x in a..a + 1, f (x + c * Complex.I)) -
        (∫ x in a..a + 1, f (x + d * Complex.I)) := by
  have he : (fun y : ℝ ↦ f ((a + 1 : ℝ) + y * Complex.I)) =
      fun y : ℝ ↦ f (a + y * Complex.I) := by
    funext y
    rw [show ((a + 1 : ℝ) : ℂ) + y * Complex.I =
      (a + y * Complex.I) + 1 by push_cast; ring, hf]
  unfold bh6_rectIntegral
  rw [he]
  ring

private lemma bh6_theta_horizontal_integral (τ : ℂ) (hτ : 0 < τ.im) (a b : ℝ)
    (hb : ∀ x : ℝ, bh6_theta τ (x + b * Complex.I) ≠ 0) :
    (∫ x in a..a + 1, logDeriv (bh6_theta τ) (x + ((b + τ.im : ℝ) : ℂ) * Complex.I)) =
      (∫ x in a..a + 1, logDeriv (bh6_theta τ) (x + b * Complex.I)) -
        2 * Real.pi * Complex.I := by
  let F : ℝ → ℂ := fun x ↦ logDeriv (bh6_theta τ) (x + b * Complex.I)
  have hp : Function.Periodic F 1 := by
    intro x
    dsimp only [F]
    rw [show ((x + 1 : ℝ) : ℂ) + b * Complex.I =
      (x + b * Complex.I) + 1 by push_cast; ring]
    exact bh6_theta_logDeriv_add_one τ hτ _
  have hF : Continuous F := by
    have ha : ∀ x : ℝ, ContinuousAt (logDeriv (bh6_theta τ)) (x + b * Complex.I) :=
      fun x ↦ ((bh6_theta_analytic τ hτ _ (mem_univ _)).deriv.div
        (bh6_theta_analytic τ hτ _ (mem_univ _)) (hb x)).continuousAt
    exact continuous_iff_continuousAt.mpr fun x ↦
      ContinuousAt.comp (g := logDeriv (bh6_theta τ))
        (f := fun t : ℝ ↦ (t : ℂ) + b * Complex.I) (ha x) (by fun_prop)
  have he : (fun x : ℝ ↦ logDeriv (bh6_theta τ) (x + ((b + τ.im : ℝ) : ℂ) * Complex.I)) =
      fun x ↦ F (x - τ.re) - 2 * Real.pi * Complex.I := by
    funext x
    dsimp only [F]
    rw [show (x : ℂ) + ((b + τ.im : ℝ) : ℂ) * Complex.I =
      (((x - τ.re : ℝ) : ℂ) + b * Complex.I) + τ by
        rw [Complex.ofReal_add, Complex.ofReal_sub]
        linear_combination Complex.re_add_im τ]
    exact bh6_theta_logDeriv_add_tau τ hτ _ (hb _)
  have hi : IntervalIntegrable (fun x ↦ F (x - τ.re)) MeasureTheory.volume a (a + 1) :=
    (hF.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  rw [he, intervalIntegral.integral_sub hi (intervalIntegrable_const),
    intervalIntegral.integral_const,
    intervalIntegral.integral_comp_sub_right]
  rw [show a + 1 - τ.re = (a - τ.re) + 1 by ring,
    hp.intervalIntegral_add_eq (a - τ.re) a]
  simp only [add_sub_cancel_left, one_smul]
  rfl

private lemma bh6_theta_rectIntegral (τ : ℂ) (hτ : 0 < τ.im) (a b : ℝ)
    (hb : ∀ x : ℝ, bh6_theta τ (x + b * Complex.I) ≠ 0) :
    bh6_rectIntegral (logDeriv (bh6_theta τ)) a (a + 1) b (b + τ.im) =
      2 * Real.pi * Complex.I := by
  rw [bh6_rectIntegral_periodic _ a b (b + τ.im)
    (fun z ↦ bh6_theta_logDeriv_add_one τ hτ z),
    bh6_theta_horizontal_integral τ hτ a b hb]
  ring

private lemma bh6_integral_inv_horizontal (a b c : ℝ) (hc : c ≠ 0) :
    (∫ x in a..b, ((x : ℂ) + c * Complex.I)⁻¹) =
      Complex.log (b + c * Complex.I) - Complex.log (a + c * Complex.I) := by
  have hs (x : ℝ) : (x : ℂ) + c * Complex.I ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa using hc
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_div] using
      (Complex.ofRealCLM.hasDerivAt.add_const (c * Complex.I)).clog_real (hs x)
  · exact ((Complex.continuous_ofReal.add continuous_const).inv₀
      (fun x ↦ Complex.slitPlane_ne_zero (hs x))).intervalIntegrable _ _

private lemma bh6_integral_inv_vertical (b c d : ℝ) (hb : 0 < b) :
    Complex.I * (∫ y in c..d, ((b : ℂ) + y * Complex.I)⁻¹) =
      Complex.log (b + d * Complex.I) - Complex.log (b + c * Complex.I) := by
  have hs (y : ℝ) : (b : ℂ) + y * Complex.I ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa using hb
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y _
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul, div_eq_mul_inv] using
      ((Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).const_add (b : ℂ)).clog_real (hs y)
  · exact (continuous_const.mul
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
        (fun y ↦ Complex.slitPlane_ne_zero (hs y)))).intervalIntegrable _ _

private lemma bh6_integral_inv_vertical_neg (a c d : ℝ) (ha : a < 0) :
    Complex.I * (∫ y in c..d, ((a : ℂ) + y * Complex.I)⁻¹) =
      Complex.log (-(a + d * Complex.I)) - Complex.log (-(a + c * Complex.I)) := by
  have hs (y : ℝ) : -((a : ℂ) + y * Complex.I) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa using neg_pos.mpr ha
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y _
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul, Pi.neg_apply, neg_div_neg_eq, div_eq_mul_inv, inv_neg, neg_mul_neg] using
      (((Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).const_add (a : ℂ)).neg).clog_real (hs y)
  · exact (continuous_const.mul
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
        (fun y h ↦ Complex.slitPlane_ne_zero (hs y) (by change (a : ℂ) + y * Complex.I = 0 at h; rw [h, neg_zero])))).intervalIntegrable _ _

private lemma bh6_rectIntegral_inv (a b c d : ℝ)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    bh6_rectIntegral (fun z ↦ z⁻¹) a b c d = 2 * Real.pi * Complex.I := by
  have hn (x y : ℝ) : Complex.log (-((x : ℂ) + y * Complex.I)) =
      Complex.log ((x : ℂ) + y * Complex.I) +
        (Complex.arg (-((x : ℂ) + y * Complex.I)) -
          Complex.arg ((x : ℂ) + y * Complex.I)) * Complex.I := by
    simp only [Complex.log, norm_neg]
    ring
  have htop := Complex.arg_neg_eq_arg_sub_pi_of_im_pos
    (x := (a : ℂ) + d * Complex.I) (by simpa using hd)
  have hbot := Complex.arg_neg_eq_arg_add_pi_of_im_neg
    (x := (a : ℂ) + c * Complex.I) (by simpa using hc)
  unfold bh6_rectIntegral
  rw [bh6_integral_inv_horizontal a b c hc.ne,
    bh6_integral_inv_horizontal a b d hd.ne',
    bh6_integral_inv_vertical b c d hb,
    bh6_integral_inv_vertical_neg a c d ha,
    hn a d, hn a c, htop, hbot]
  push_cast
  ring


private lemma bh6_rectIntegral_sub_inv (a b c d : ℝ) (w : ℂ)
    (ha : a < w.re) (hb : w.re < b) (hc : c < w.im) (hd : w.im < d) :
    bh6_rectIntegral (fun z ↦ (z - w)⁻¹) a b c d = 2 * Real.pi * Complex.I := by
  have hh (y : ℝ) : (∫ x in a..b, ((x : ℂ) + y * Complex.I - w)⁻¹) =
      ∫ x in (a - w.re)..(b - w.re), ((x : ℂ) + (y - w.im : ℝ) * Complex.I)⁻¹ := by
    rw [← intervalIntegral.integral_comp_sub_right (f := fun x : ℝ ↦
      ((x : ℂ) + (y - w.im : ℝ) * Complex.I)⁻¹) w.re]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    apply congrArg (fun z : ℂ ↦ z⁻¹)
    push_cast
    linear_combination Complex.re_add_im w
  have hv (x : ℝ) : (∫ y in c..d, ((x : ℂ) + y * Complex.I - w)⁻¹) =
      ∫ y in (c - w.im)..(d - w.im), ((x - w.re : ℝ) + y * Complex.I)⁻¹ := by
    rw [← intervalIntegral.integral_comp_sub_right (f := fun y : ℝ ↦
      ((x - w.re : ℝ) + y * Complex.I)⁻¹) w.im]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    apply congrArg (fun z : ℂ ↦ z⁻¹)
    push_cast
    linear_combination Complex.re_add_im w
  unfold bh6_rectIntegral
  rw [hh c, hh d, hv b, hv a]
  exact bh6_rectIntegral_inv _ _ _ _ (sub_neg.mpr ha) (sub_pos.mpr hb)
    (sub_neg.mpr hc) (sub_pos.mpr hd)

private lemma bh6_rectIntegral_analytic (f : ℂ → ℂ) (a b c d : ℝ)
    (hf : AnalyticOnNhd ℂ f (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    bh6_rectIntegral f a b c d = 0 := by
  simpa only [bh6_rectIntegral, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ⟨a, c⟩ ⟨b, d⟩ hf.differentiableOn

private lemma bh6_rect_edges (a b c d : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d) :
    (∀ x ∈ uIcc a b, ∀ y ∈ ({c, d} : Set ℝ),
      (x : ℂ) + y * Complex.I ∈ (uIcc a b ×ℂ uIcc c d) \ (S : Set ℂ)) ∧
    (∀ y ∈ uIcc c d, ∀ x ∈ ({a, b} : Set ℝ),
      (x : ℂ) + y * Complex.I ∈ (uIcc a b ×ℂ uIcc c d) \ (S : Set ℂ)) := by
  constructor
  · intro x hx y hy
    rcases hy with hy | hy
    · have hy : y = c := hy
      subst y
      refine ⟨?_, ?_⟩
      · simpa [Complex.mem_reProdIm] using And.intro hx (left_mem_uIcc : c ∈ uIcc c d)
      · intro hs
        have h := (hS _ hs).2.2.1
        simp at h
    · have hy : y = d := hy
      subst y
      refine ⟨?_, ?_⟩
      · simpa [Complex.mem_reProdIm] using And.intro hx (right_mem_uIcc : d ∈ uIcc c d)
      · intro hs
        have h := (hS _ hs).2.2.2
        simp at h
  · intro y hy x hx
    rcases hx with hx | hx
    · have hx : x = a := hx
      subst x
      refine ⟨?_, ?_⟩
      · simpa [Complex.mem_reProdIm] using And.intro (left_mem_uIcc : a ∈ uIcc a b) hy
      · intro hs
        have h := (hS _ hs).1
        simp at h
    · have hx : x = b := hx
      subst x
      refine ⟨?_, ?_⟩
      · simpa [Complex.mem_reProdIm] using And.intro (right_mem_uIcc : b ∈ uIcc a b) hy
      · intro hs
        have h := (hS _ hs).2.1
        simp at h

private lemma bh6_rect_integrable (f : ℂ → ℂ) (a b c d : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d)
    (hf : ContinuousOn f ((uIcc a b ×ℂ uIcc c d) \ (S : Set ℂ))) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + c * Complex.I)) MeasureTheory.volume a b ∧
    IntervalIntegrable (fun x : ℝ ↦ f (x + d * Complex.I)) MeasureTheory.volume a b ∧
    IntervalIntegrable (fun y : ℝ ↦ f (b + y * Complex.I)) MeasureTheory.volume c d ∧
    IntervalIntegrable (fun y : ℝ ↦ f (a + y * Complex.I)) MeasureTheory.volume c d := by
  have he := bh6_rect_edges a b c d S hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hf.comp (by fun_prop) (fun x hx ↦ he.1 x hx c (by simp))).intervalIntegrable
  · exact (hf.comp (by fun_prop) (fun x hx ↦ he.1 x hx d (by simp))).intervalIntegrable
  · exact (hf.comp (by fun_prop) (fun y hy ↦ he.2 y hy b (by simp))).intervalIntegrable
  · exact (hf.comp (by fun_prop) (fun y hy ↦ he.2 y hy a (by simp))).intervalIntegrable

private lemma bh6_rectIntegral_congr (f g : ℂ → ℂ) (a b c d : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d)
    (he : EqOn f g ((uIcc a b ×ℂ uIcc c d) \ (S : Set ℂ))) :
    bh6_rectIntegral f a b c d = bh6_rectIntegral g a b c d := by
  have hm := bh6_rect_edges a b c d S hS
  have h1 : (∫ x in a..b, f (x + c * Complex.I)) = ∫ x in a..b, g (x + c * Complex.I) :=
    intervalIntegral.integral_congr fun x hx ↦ he (hm.1 x hx c (by simp))
  have h2 : (∫ x in a..b, f (x + d * Complex.I)) = ∫ x in a..b, g (x + d * Complex.I) :=
    intervalIntegral.integral_congr fun x hx ↦ he (hm.1 x hx d (by simp))
  have h3 : (∫ y in c..d, f (b + y * Complex.I)) = ∫ y in c..d, g (b + y * Complex.I) :=
    intervalIntegral.integral_congr fun y hy ↦ he (hm.2 y hy b (by simp))
  have h4 : (∫ y in c..d, f (a + y * Complex.I)) = ∫ y in c..d, g (a + y * Complex.I) :=
    intervalIntegral.integral_congr fun y hy ↦ he (hm.2 y hy a (by simp))
  simp only [bh6_rectIntegral, h1, h2, h3, h4]

private lemma bh6_rectIntegral_add (f g : ℂ → ℂ) (a b c d : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d)
    (hf : ContinuousOn f ((uIcc a b ×ℂ uIcc c d) \ (S : Set ℂ)))
    (hg : ContinuousOn g ((uIcc a b ×ℂ uIcc c d) \ (S : Set ℂ))) :
    bh6_rectIntegral (fun z ↦ f z + g z) a b c d =
      bh6_rectIntegral f a b c d + bh6_rectIntegral g a b c d := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := bh6_rect_integrable f a b c d S hS hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := bh6_rect_integrable g a b c d S hS hg
  simp only [bh6_rectIntegral, intervalIntegral.integral_add hf1 hg1,
    intervalIntegral.integral_add hf2 hg2, intervalIntegral.integral_add hf3 hg3,
    intervalIntegral.integral_add hf4 hg4]
  ring

private lemma bh6_rectIntegral_const_mul (f : ℂ → ℂ) (a b c d : ℝ) (k : ℂ) :
    bh6_rectIntegral (fun z ↦ k * f z) a b c d = k * bh6_rectIntegral f a b c d := by
  simp only [bh6_rectIntegral, intervalIntegral.integral_const_mul]
  ring

private lemma bh6_rectIntegral_sum (F : ℂ → ℂ → ℂ) (a b c d : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d)
    (hF : ∀ s ∈ S, ContinuousOn (F s) ((uIcc a b ×ℂ uIcc c d) \ (S : Set ℂ))) :
    bh6_rectIntegral (fun z ↦ ∑ s ∈ S, F s z) a b c d =
      ∑ s ∈ S, bh6_rectIntegral (F s) a b c d := by
  have hi := fun s hs ↦ bh6_rect_integrable (F s) a b c d S hS (hF s hs)
  simp only [bh6_rectIntegral,
    intervalIntegral.integral_finsetSum (fun s hs ↦ (hi s hs).1),
    intervalIntegral.integral_finsetSum (fun s hs ↦ (hi s hs).2.1),
    intervalIntegral.integral_finsetSum (fun s hs ↦ (hi s hs).2.2.1),
    intervalIntegral.integral_finsetSum (fun s hs ↦ (hi s hs).2.2.2),
    Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]


private lemma bh6_logDeriv_regular_part (f : ℂ → ℂ) (K : Set ℂ)
    (hf : AnalyticOnNhd ℂ f K) (S : Finset ℂ) (ord : ℂ → ℤ)
    (hord : ∀ s ∈ S, meromorphicOrderAt f s = (ord s : WithTop ℤ))
    (hz : ∀ z ∈ K, z ∉ S → f z ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G K ∧
      ∀ z ∈ K, z ∉ S → logDeriv f z = G z + ∑ s ∈ S, (ord s : ℂ) * (z - s)⁻¹ := by
  classical
  let P : ℂ → ℂ := fun z ↦ ∑ s ∈ S, (ord s : ℂ) * (z - s)⁻¹
  let A : ℂ → ℂ := fun z ↦ logDeriv f z - P z
  have hP : MeromorphicOn P K := by
    apply MeromorphicOn.fun_sum
    intro s _ z _
    exact (MeromorphicAt.const (ord s : ℂ) z).mul
      (((MeromorphicAt.id z).sub (MeromorphicAt.const s z)).inv)
  have hA : MeromorphicOn A K := hf.meromorphicOn.logDeriv.sub hP
  have hPa (z : ℂ) (hzS : z ∉ S) : AnalyticAt ℂ P z := by
    apply Finset.analyticAt_fun_sum
    intro s hs
    exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
      (sub_ne_zero.mpr (by intro h; change z = s at h; exact hzS (h.symm ▸ hs))))
  have hAa (z : ℂ) (hzK : z ∈ K) (hzS : z ∉ S) : AnalyticAt ℂ A z :=
    ((hf z hzK).deriv.div (hf z hzK) (hz z hzK hzS)).sub (hPa z hzS)
  have hnonneg (z : ℂ) (hzK : z ∈ K) : 0 ≤ meromorphicOrderAt A z := by
    by_cases hzS : z ∈ S
    · obtain ⟨g, hg, hgn, hge⟩ := TauCeti.Contour.logDeriv_eventuallyEq_principalPart
        (hf z hzK).meromorphicAt (hord z hzS)
      have he : A =ᶠ[𝓝[≠] z] fun w ↦ logDeriv g w -
          ∑ s ∈ S.erase z, (ord s : ℂ) * (w - s)⁻¹ := by
        filter_upwards [hge] with w hw
        dsimp only [A, P]
        rw [← Finset.add_sum_erase S (fun s ↦ (ord s : ℂ) * (w - s)⁻¹) hzS, hw]
        ring
      rw [meromorphicOrderAt_congr he]
      apply AnalyticAt.meromorphicOrderAt_nonneg
      apply (hg.deriv.div hg hgn).sub
      apply Finset.analyticAt_fun_sum
      intro s hs
      exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
        (sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hs))))
    · exact (hAa z hzK hzS).meromorphicOrderAt_nonneg
  let G := toMeromorphicNFOn A K
  have hG : AnalyticOnNhd ℂ G K := by
    intro z hzK
    apply (meromorphicNFOn_toMeromorphicNFOn A K hzK).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hA hzK]
    exact hnonneg z hzK
  refine ⟨G, hG, ?_⟩
  intro z hzK hzS
  have he : G z = A z := by
    dsimp only [G]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hA hzK,
      toMeromorphicNFAt_eq_self.mpr (hAa z hzK hzS).meromorphicNFAt]
  rw [he]
  dsimp only [A, P]
  ring

private lemma bh6_rect_argument_principle (f : ℂ → ℂ) (a b c d : ℝ)
    (hf : AnalyticOnNhd ℂ f (uIcc a b ×ℂ uIcc c d)) (S : Finset ℂ) (ord : ℂ → ℤ)
    (hS : ∀ z ∈ S, a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d)
    (hord : ∀ s ∈ S, meromorphicOrderAt f s = (ord s : WithTop ℤ))
    (hz : ∀ z ∈ (uIcc a b ×ℂ uIcc c d), z ∉ S → f z ≠ 0) :
    bh6_rectIntegral (logDeriv f) a b c d =
      (2 * Real.pi * Complex.I) * ∑ s ∈ S, (ord s : ℂ) := by
  classical
  obtain ⟨G, hG, he⟩ := bh6_logDeriv_regular_part f _ hf S ord hord hz
  let P : ℂ → ℂ := fun z ↦ ∑ s ∈ S, (ord s : ℂ) * (z - s)⁻¹
  have hP (s : ℂ) (hs : s ∈ S) : ContinuousOn
      (fun z ↦ (ord s : ℂ) * (z - s)⁻¹)
      ((uIcc a b ×ℂ uIcc c d) \ (S : Set ℂ)) := by
    apply continuousOn_const.mul
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz
    apply sub_ne_zero.mpr
    intro h
    change z = s at h
    exact hz.2 (h.symm ▸ hs)
  have hPs : ContinuousOn P ((uIcc a b ×ℂ uIcc c d) \ (S : Set ℂ)) :=
    continuousOn_finsetSum S hP
  have hGc := hG.continuousOn.mono (sdiff_subset :
    (uIcc a b ×ℂ uIcc c d) \ (S : Set ℂ) ⊆ _)
  rw [bh6_rectIntegral_congr (logDeriv f) (fun z ↦ G z + P z) a b c d S hS
    (fun z hz ↦ he z hz.1 hz.2), bh6_rectIntegral_add G P a b c d S hS hGc hPs,
    bh6_rectIntegral_analytic G a b c d hG, zero_add]
  change bh6_rectIntegral (fun z ↦ ∑ s ∈ S, (ord s : ℂ) * (z - s)⁻¹) a b c d = _
  rw [bh6_rectIntegral_sum _ a b c d S hS hP]
  calc
    _ = ∑ s ∈ S, (ord s : ℂ) * (2 * Real.pi * Complex.I) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [bh6_rectIntegral_const_mul,
        bh6_rectIntegral_sub_inv a b c d s (hS s hs).1 (hS s hs).2.1
          (hS s hs).2.2.1 (hS s hs).2.2.2]
    _ = _ := by rw [← Finset.sum_mul]; ring


private lemma bh6_theta_zeros_countable (τ : ℂ) (hτ : 0 < τ.im) :
    {z | bh6_theta τ z = 0}.Countable := by
  obtain ⟨w, hw⟩ := Function.ne_iff.mp (bh6_theta_not_identically_zero τ hτ)
  have hc := (bh6_theta_analytic τ hτ).preimage_zero_mem_codiscrete hw
  have hc' : {z | bh6_theta τ z = 0}ᶜ ∈ codiscrete ℂ := hc
  exact IsLindelof.of_coe.countable_of_isDiscrete (compl_mem_codiscrete_iff.mp hc').2

private lemma bh6_theta_good_rect (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ a b : ℝ, -1 < a ∧ a < 0 ∧ -τ.im < b ∧ b < 0 ∧
      (∀ x : ℝ, bh6_theta τ (x + b * Complex.I) ≠ 0) ∧
      (∀ z : ℂ, z.re = a ∨ z.re = a + 1 ∨ z.im = b ∨ z.im = b + τ.im →
        bh6_theta τ z ≠ 0) := by
  have hc := bh6_theta_zeros_countable τ hτ
  obtain ⟨a, ha, haI⟩ := ((hc.image Complex.re).dense_compl ℝ).exists_mem_open
    isOpen_Ioo (nonempty_Ioo.mpr (by norm_num : (-1 : ℝ) < 0))
  obtain ⟨b, hb, hbI⟩ := ((hc.image Complex.im).dense_compl ℝ).exists_mem_open
    isOpen_Ioo (nonempty_Ioo.mpr (neg_neg_of_pos hτ))
  have hre (z : ℂ) (hz : z.re = a) : bh6_theta τ z ≠ 0 :=
    fun h ↦ ha ⟨z, h, hz⟩
  have him (z : ℂ) (hz : z.im = b) : bh6_theta τ z ≠ 0 :=
    fun h ↦ hb ⟨z, h, hz⟩
  have h1 (z : ℂ) : bh6_theta τ (z + 1) = bh6_theta τ z := by
    unfold bh6_theta
    rw [show z + 1 - (1 + τ) / 2 = (z - (1 + τ) / 2) + 1 by ring,
      jacobiTheta₂_add_left]
  have ht (z : ℂ) : bh6_theta τ (z + τ) = 0 ↔ bh6_theta τ z = 0 := by
    unfold bh6_theta
    rw [show z + τ - (1 + τ) / 2 = (z - (1 + τ) / 2) + τ by ring]
    exact jacobiTheta₂_add_tau_eq_zero_iff _ τ
  refine ⟨a, b, haI.1, haI.2, hbI.1, hbI.2, fun x ↦ him _ (by simp), ?_⟩
  intro z hz
  rcases hz with hz | hz | hz | hz
  · exact hre z hz
  · have hn := hre (z - 1) (by simp [hz])
    intro hzero
    apply hn
    rw [← h1 (z - 1), sub_add_cancel]
    exact hzero
  · exact him z hz
  · intro hzero
    apply him (z - τ) (by simp [Complex.sub_im, hz])
    exact (ht (z - τ)).mp (by simpa only [sub_add_cancel] using hzero)


private lemma bh6_theta_single_rect (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ a b : ℝ, -1 < a ∧ a < 0 ∧ -τ.im < b ∧ b < 0 ∧
      (∀ z ∈ (uIcc a (a + 1) ×ℂ uIcc b (b + τ.im)), bh6_theta τ z = 0 → z = 0) ∧
      analyticOrderAt (bh6_theta τ) 0 = 1 := by
  classical
  obtain ⟨a, b, ha1, ha0, hb1, hb0, hbot, hbd⟩ := bh6_theta_good_rect τ hτ
  let K : Set ℂ := uIcc a (a + 1) ×ℂ uIcc b (b + τ.im)
  have hK : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  let S : Finset ℂ := (bh6_theta_compact_zeros_finite τ hτ K hK).toFinset
  have hmem (z : ℂ) : z ∈ S ↔ z ∈ K ∧ bh6_theta τ z = 0 := by simp [S]
  have hS : ∀ z ∈ S, a < z.re ∧ z.re < a + 1 ∧ b < z.im ∧ z.im < b + τ.im := by
    intro z hz
    obtain ⟨hzK, hz0⟩ := (hmem z).mp hz
    change z.re ∈ uIcc a (a + 1) ∧ z.im ∈ uIcc b (b + τ.im) at hzK
    rw [uIcc_of_le (by linarith : a ≤ a + 1),
      uIcc_of_le (by linarith : b ≤ b + τ.im)] at hzK
    have hn := fun h ↦ hbd z h hz0
    refine ⟨lt_of_le_of_ne hzK.1.1 ?_, lt_of_le_of_ne hzK.1.2 ?_,
      lt_of_le_of_ne hzK.2.1 ?_, lt_of_le_of_ne hzK.2.2 ?_⟩
    · exact fun h ↦ hn (Or.inl h.symm)
    · exact fun h ↦ hn (Or.inr (Or.inl h))
    · exact fun h ↦ hn (Or.inr (Or.inr (Or.inl h.symm)))
    · exact fun h ↦ hn (Or.inr (Or.inr (Or.inr h)))
  let m : ℂ → ℕ := fun z ↦ (analyticOrderAt (bh6_theta τ) z).toNat
  have hm (z : ℂ) : (m z : ℕ∞) = analyticOrderAt (bh6_theta τ) z :=
    ENat.natCast_toNat (bh6_theta_order_ne_top τ hτ z)
  have hmp (z : ℂ) (hz : z ∈ S) : 0 < m z :=
    ENat.toNat_pos ((bh6_theta_analytic τ hτ z (mem_univ z)).analyticOrderAt_ne_zero.mpr
      ((hmem z).mp hz).2) (bh6_theta_order_ne_top τ hτ z)
  have hord (z : ℂ) (_hz : z ∈ S) :
      meromorphicOrderAt (bh6_theta τ) z = ((m z : ℤ) : WithTop ℤ) := by
    rw [(bh6_theta_analytic τ hτ z (mem_univ z)).meromorphicOrderAt_eq, ← hm z,
      ENat.map_natCast]
  have hi := bh6_rect_argument_principle (bh6_theta τ) a (a + 1) b (b + τ.im)
    ((bh6_theta_analytic τ hτ).mono (subset_univ K)) S (fun z ↦ (m z : ℤ)) hS hord
    (fun z hz hn hzero ↦ hn ((hmem z).mpr ⟨hz, hzero⟩))
  rw [bh6_theta_rectIntegral τ hτ a b hbot] at hi
  have hsC : (∑ z ∈ S, (m z : ℂ)) = 1 := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    simpa only [Int.cast_natCast, mul_one] using hi.symm
  have hs : ∑ z ∈ S, m z = 1 := by exact_mod_cast hsC
  have h0K : (0 : ℂ) ∈ K := by
    change (0 : ℝ) ∈ uIcc a (a + 1) ∧ (0 : ℝ) ∈ uIcc b (b + τ.im)
    rw [uIcc_of_le (by linarith : a ≤ a + 1),
      uIcc_of_le (by linarith : b ≤ b + τ.im)]
    exact ⟨⟨ha0.le, by linarith⟩, ⟨hb0.le, by linarith⟩⟩
  have h0S := (hmem 0).mpr ⟨h0K, bh6_theta_zero τ⟩
  have hm0 : m 0 = 1 := by
    have hp := hmp 0 h0S
    have hl := Finset.single_le_sum (fun z (_ : z ∈ S) ↦ Nat.zero_le (m z)) h0S
    omega
  have herase : ∑ z ∈ S.erase 0, m z = 0 := by
    have he := Finset.sum_erase_add S m h0S
    omega
  refine ⟨a, b, ha1, ha0, hb1, hb0, ?_, ?_⟩
  · intro z hzK hz0
    have hzS := (hmem z).mpr ⟨hzK, hz0⟩
    by_contra hn
    have hp := hmp z hzS
    have hl := Finset.single_le_sum (fun t (_ : t ∈ S.erase 0) ↦ Nat.zero_le (m t))
      (Finset.mem_erase.mpr ⟨hn, hzS⟩)
    omega
  · rw [← hm 0, hm0]
    rfl


private lemma bh6_theta_reduce_rect (τ : ℂ) (hτ : 0 < τ.im) (a b : ℝ) (z : ℂ) :
    ∃ (w : ℂ) (i j : ℤ), z = w + (i : ℂ) + τ * j ∧
      w ∈ (uIcc a (a + 1) ×ℂ uIcc b (b + τ.im)) ∧
      (bh6_theta τ z = 0 ↔ bh6_theta τ w = 0) := by
  let y : ℝ := (z.im - b) / τ.im
  let j : ℤ := ⌊y⌋
  let x : ℝ := z.re - τ.re * j - a
  let i : ℤ := ⌊x⌋
  let w : ℂ := z - i - τ * j
  have hw : z = w + (i : ℂ) + τ * j := by dsimp only [w]; ring
  have him : w.im = z.im - τ.im * j := by simp [w, Complex.mul_im]
  have hre : w.re = z.re - i - τ.re * j := by simp [w, Complex.mul_re]
  refine ⟨w, i, j, hw, ?_, ?_⟩
  · change w.re ∈ uIcc a (a + 1) ∧ w.im ∈ uIcc b (b + τ.im)
    rw [uIcc_of_le (by linarith : a ≤ a + 1),
      uIcc_of_le (by linarith : b ≤ b + τ.im)]
    have hxle : (i : ℝ) ≤ z.re - τ.re * j - a := Int.floor_le x
    have hxlt : z.re - τ.re * j - a < (i : ℝ) + 1 := Int.lt_floor_add_one x
    have hyle : (j : ℝ) * τ.im ≤ z.im - b :=
      (le_div_iff₀ hτ).mp (Int.floor_le y)
    have hylt : z.im - b < ((j : ℝ) + 1) * τ.im :=
      (div_lt_iff₀ hτ).mp (Int.lt_floor_add_one y)
    rw [hre, him]
    constructor <;> constructor <;> nlinarith
  · rw [hw]
    unfold bh6_theta
    rw [show w + (i : ℂ) + τ * j - (1 + τ) / 2 =
      (w - (1 + τ) / 2 + τ * j) + i by ring,
      jacobiTheta₂_add_int_eq_zero_iff, jacobiTheta₂_add_int_tau_eq_zero_iff]

private lemma bh6_theta_zero_is_period (τ : ℂ) (hτ : 0 < τ.im) (z : ℂ)
    (hz : bh6_theta τ z = 0) : ∃ i j : ℤ, z = (i : ℂ) + τ * j := by
  obtain ⟨a, b, _, _, _, _, huniq, _⟩ := bh6_theta_single_rect τ hτ
  obtain ⟨w, i, j, he, hw, hziff⟩ := bh6_theta_reduce_rect τ hτ a b z
  have hw0 := huniq w hw (hziff.mp hz)
  exact ⟨i, j, by simpa only [hw0, zero_add] using he⟩


/-- The centered half-open fundamental parallelogram contains exactly one theta zero.
Source: Mumford, *Tata Lectures on Theta I*, section 1, fundamental-parallelogram zero count. -/
theorem bh6_theta_cell_count_aux (τ : ℂ) (hτ : 0 < τ.im) :
    {w : ℂ | w.im / τ.im ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      w.re - τ.re * (w.im / τ.im) ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      bh6_theta τ w = 0}.ncard = 1 := by
  have he : {w : ℂ | w.im / τ.im ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      w.re - τ.re * (w.im / τ.im) ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      bh6_theta τ w = 0} = {0} := by
    ext w
    constructor
    · rintro ⟨hy, hx, hz⟩
      obtain ⟨i, j, rfl⟩ := bh6_theta_zero_is_period τ hτ w hz
      have him : ((i : ℂ) + τ * j).im / τ.im = (j : ℝ) := by
        simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im,
          Complex.intCast_re, mul_zero, zero_add]
        exact mul_div_cancel_left₀ _ (ne_of_gt hτ)
      have hre : ((i : ℂ) + τ * j).re - τ.re * (((i : ℂ) + τ * j).im / τ.im) =
          (i : ℝ) := by
        rw [him]
        simp [Complex.mul_re]
      rw [him] at hy
      rw [hre] at hx
      have hint (k : ℤ) (hk : (k : ℝ) ∈ Ico (-1 / 2 : ℝ) (1 / 2)) : k = 0 := by
        have hl : (-1 : ℝ) < (k : ℝ) := by linarith [hk.1]
        have hu : (k : ℝ) < 1 := by linarith [hk.2]
        have hl' : (-1 : ℤ) < k := by exact_mod_cast hl
        have hu' : k < (1 : ℤ) := by exact_mod_cast hu
        omega
      simp only [hint i hx, hint j hy, Int.cast_zero, mul_zero, add_zero,
        mem_singleton_iff]
    · intro hw
      rw [mem_singleton_iff] at hw
      subst w
      norm_num [bh6_theta_zero]
  rw [he]
  exact Set.ncard_singleton 0

private lemma sub_floor_centered_mem_Ico (x : ℝ) :
    x - (⌊x + 1 / 2⌋ : ℤ) ∈ Ico (-1 / 2 : ℝ) (1 / 2) := by
  have hnonneg := Int.fract_nonneg (x + 1 / 2)
  have hlt := Int.fract_lt_one (x + 1 / 2)
  have he := Int.floor_add_fract (x + 1 / 2)
  constructor <;> linarith

private lemma bh6_theta_add_period_eq_zero_iff (τ z : ℂ) (a b : ℤ) :
    bh6_theta τ (z + a + τ * b) = 0 ↔ bh6_theta τ z = 0 := by
  rw [bh6_theta, bh6_theta,
    show z + (a : ℂ) + τ * b - (1 + τ) / 2 =
      (z - (1 + τ) / 2 + τ * b) + a by ring,
    jacobiTheta₂_add_int_eq_zero_iff,
    jacobiTheta₂_add_int_tau_eq_zero_iff]

/-- Reduce an arbitrary point to the centered cell, preserving vanishing by quasi-periodicity.
Source: Mumford, *Tata Lectures on Theta I*, section 1, the two theta translation formulas. -/
theorem bh6_theta_period_reduce_aux (τ : ℂ) (hτ : 0 < τ.im) (z : ℂ) :
    ∃ (w : ℂ) (a b : ℤ), z = w + (a : ℂ) + τ * b ∧
      w.im / τ.im ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      w.re - τ.re * (w.im / τ.im) ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      (bh6_theta τ z = 0 ↔ bh6_theta τ w = 0) := by
  let y : ℝ := z.im / τ.im
  let b : ℤ := ⌊y + 1 / 2⌋
  let x : ℝ := z.re - τ.re * y
  let a : ℤ := ⌊x + 1 / 2⌋
  let w : ℂ := z - a - τ * b
  have hzw : z = w + (a : ℂ) + τ * b := by
    dsimp only [w]
    ring
  refine ⟨w, a, b, hzw, ?_, ?_, ?_⟩
  · have hτ0 : τ.im ≠ 0 := ne_of_gt hτ
    have him : w.im = z.im - τ.im * b := by
      simp [w, Complex.mul_im]
    rw [him]
    have hy : (z.im - τ.im * (b : ℝ)) / τ.im = y - b := by
      dsimp only [y]
      field_simp [hτ0]
    rw [hy]
    exact sub_floor_centered_mem_Ico y
  · have hτ0 : τ.im ≠ 0 := ne_of_gt hτ
    have him : w.im = z.im - τ.im * b := by
      simp [w, Complex.mul_im]
    have hre : w.re = z.re - a - τ.re * b := by
      simp [w, Complex.mul_re]
    rw [him, hre]
    have hy : (z.im - τ.im * (b : ℝ)) / τ.im = y - b := by
      dsimp only [y]
      field_simp [hτ0]
    rw [hy]
    have he : z.re - (a : ℝ) - τ.re * (b : ℝ) - τ.re * (y - b) = x - a := by
      dsimp only [x]
      ring
    rw [he]
    exact sub_floor_centered_mem_Ico x
  · rw [hzw]
    exact bh6_theta_add_period_eq_zero_iff τ w a b

/-- The shifted elliptic theta function has no zeros off its period lattice.
Source: Mumford, *Tata Lectures on Theta I*, section 1, fundamental-parallelogram zero count. -/
theorem bh6_theta_nonlattice_aux (τ : ℂ) (hτ : 0 < τ.im) (z : ℂ)
    (hz : ¬ ∃ a b : ℤ, z = (a : ℂ) + τ * b) : bh6_theta τ z ≠ 0 := by
  intro hzero
  obtain ⟨w, a, b, hzw, hw₁, hw₂, hw⟩ := bh6_theta_period_reduce_aux τ hτ z
  obtain ⟨u, hu⟩ := Set.ncard_eq_one.mp (bh6_theta_cell_count_aux τ hτ)
  have h0 : (0 : ℂ) ∈ {w : ℂ | w.im / τ.im ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      w.re - τ.re * (w.im / τ.im) ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      bh6_theta τ w = 0} := by
    norm_num [bh6_theta_zero]
  have hwmem : w ∈ {w : ℂ | w.im / τ.im ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      w.re - τ.re * (w.im / τ.im) ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      bh6_theta τ w = 0} := ⟨hw₁, hw₂, hw.mp hzero⟩
  rw [hu, mem_singleton_iff] at h0 hwmem
  have hw0 : w = 0 := hwmem.trans h0.symm
  exact hz ⟨a, b, by simpa [hw0] using hzw⟩

/-- The shifted elliptic theta function is entire and has precisely the prescribed lattice zeros.
Source: Mumford, *Tata Lectures on Theta I*, section 1. -/
theorem bh6_theta_zeros (τ : ℂ) (hτ : 0 < τ.im) :
    AnalyticOnNhd ℂ (bh6_theta τ) univ ∧
      ∀ z, bh6_theta τ z = 0 ↔ ∃ a b : ℤ, z = (a : ℂ) + τ * b := by
  refine ⟨bh6_theta_analytic τ hτ, fun z ↦ ⟨?_, ?_⟩⟩
  · intro hz
    by_contra hn
    exact bh6_theta_nonlattice_aux τ hτ z hn hz
  · rintro ⟨a, b, rfl⟩
    exact bh6_theta_lattice_zero_aux τ hτ a b

/-- The theta zero at the origin has nonzero derivative.
Source: Mumford, *Tata Lectures on Theta I*, section 1, Jacobi product and the simple origin zero. -/
theorem bh6_theta_deriv_origin_aux (τ : ℂ) (hτ : 0 < τ.im) :
    deriv (bh6_theta τ) 0 ≠ 0 := by
  obtain ⟨a, b, _, _, _, _, _, ho⟩ := bh6_theta_single_rect τ hτ
  have hdo : analyticOrderAt (deriv (bh6_theta τ)) 0 = 0 :=
    analyticOrderAt_deriv_of_pos (bh6_theta_analytic τ hτ 0 (mem_univ 0))
      (n := 0) (by simpa using ho)
  exact (bh6_theta_analytic τ hτ 0 (mem_univ 0)).deriv.analyticOrderAt_eq_zero.mp hdo

/-- Translation by periods preserves nonvanishing of the derivative at the origin zero.
Source: Mumford, *Tata Lectures on Theta I*, section 1, differentiated quasi-periodicity. -/
theorem bh6_theta_deriv_translate_aux (τ : ℂ) (hτ : 0 < τ.im) (a b : ℤ) :
    deriv (bh6_theta τ) ((a : ℂ) + τ * b) ≠ 0 ↔ deriv (bh6_theta τ) 0 ≠ 0 := by
  have hderiv (z : ℂ) :
      deriv (bh6_theta τ) z = jacobiTheta₂' (z - (1 + τ) / 2) τ := by
    change deriv (fun z ↦ jacobiTheta₂ (z - (1 + τ) / 2) τ) z = _
    simpa only [Function.comp_def, id_eq, mul_one] using
      ((hasDerivAt_jacobiTheta₂_fst (z - (1 + τ) / 2) hτ).comp z
        ((hasDerivAt_id z).sub_const ((1 + τ) / 2))).deriv
  have hperiod : Function.Periodic (fun z ↦ jacobiTheta₂' z τ) 1 :=
    fun z ↦ jacobiTheta₂'_add_left z τ
  rw [hderiv, hderiv]
  have ha : jacobiTheta₂' ((a : ℂ) + τ * b - (1 + τ) / 2) τ =
      jacobiTheta₂' (τ * b - (1 + τ) / 2) τ := by
    convert hperiod.int_mul a (τ * b - (1 + τ) / 2) using 1 <;> push_cast <;> ring
  rw [ha]
  have hb : ∀ b : ℤ,
      jacobiTheta₂' (τ * b - (1 + τ) / 2) τ ≠ 0 ↔
        jacobiTheta₂' (-(1 + τ) / 2) τ ≠ 0 := by
    intro b
    rcases b with n | n
    · induction n with
      | zero => ring_nf
      | succ n ih =>
        have hz := bh6_theta_lattice_zero_aux τ hτ 0 (n : ℤ)
        have ht := jacobiTheta₂'_add_left' (τ * (n : ℂ) - (1 + τ) / 2) τ
        change jacobiTheta₂' (τ * ((n + 1 : ℕ) : ℂ) - (1 + τ) / 2) τ ≠ 0 ↔ _
        rw [show τ * ((n + 1 : ℕ) : ℂ) - (1 + τ) / 2 =
          (τ * (n : ℂ) - (1 + τ) / 2) + τ by push_cast; ring, ht]
        have hz' : jacobiTheta₂ (τ * (n : ℂ) - (1 + τ) / 2) τ = 0 := by
          simpa only [bh6_theta, Int.cast_zero, zero_add, Int.cast_natCast] using hz
        rw [hz', mul_zero, sub_zero]
        constructor
        · intro hp
          exact ih.mp (right_ne_zero_of_mul hp)
        · intro ho
          exact mul_ne_zero (Complex.exp_ne_zero _) (ih.mpr ho)
    · induction n with
      | zero =>
        have hz := bh6_theta_lattice_zero_aux τ hτ 0 (-1)
        have ht := jacobiTheta₂'_add_left' (τ * (-1 : ℂ) - (1 + τ) / 2) τ
        have hz' : jacobiTheta₂ (τ * (-1 : ℂ) - (1 + τ) / 2) τ = 0 := by
          simpa only [bh6_theta, Int.cast_zero, zero_add, Int.cast_neg, Int.cast_one] using hz
        rw [hz', mul_zero, sub_zero] at ht
        have harg : τ * (-1 : ℂ) - (1 + τ) / 2 + τ = -(1 + τ) / 2 := by ring
        rw [harg] at ht
        rw [show τ * ((Int.negSucc 0 : ℤ) : ℂ) - (1 + τ) / 2 =
          τ * (-1 : ℂ) - (1 + τ) / 2 by norm_num]
        constructor
        · intro hn
          rw [ht]
          exact mul_ne_zero (Complex.exp_ne_zero _) hn
        · intro h0
          rw [ht] at h0
          exact right_ne_zero_of_mul h0
      | succ n ih =>
        have hz := bh6_theta_lattice_zero_aux τ hτ 0 (Int.negSucc (n + 1))
        have ht := jacobiTheta₂'_add_left'
          (τ * ((Int.negSucc (n + 1) : ℤ) : ℂ) - (1 + τ) / 2) τ
        have hz' : jacobiTheta₂ (τ * ((Int.negSucc (n + 1) : ℤ) : ℂ) -
            (1 + τ) / 2) τ = 0 := by
          simpa only [bh6_theta, Int.cast_zero, zero_add] using hz
        rw [hz', mul_zero, sub_zero] at ht
        have he : jacobiTheta₂' (τ * ((Int.negSucc n : ℤ) : ℂ) - (1 + τ) / 2) τ ≠ 0 ↔
            jacobiTheta₂' (τ * ((Int.negSucc (n + 1) : ℤ) : ℂ) - (1 + τ) / 2) τ ≠ 0 := by
          rw [show τ * ((Int.negSucc n : ℤ) : ℂ) - (1 + τ) / 2 =
            (τ * ((Int.negSucc (n + 1) : ℤ) : ℂ) - (1 + τ) / 2) + τ by
              push_cast; ring, ht]
          constructor
          · exact fun h ↦ right_ne_zero_of_mul h
          · exact fun h ↦ mul_ne_zero (Complex.exp_ne_zero _) h
        exact he.symm.trans ih
  convert hb b using 1 <;> ring_nf

/-- All zeros of the shifted elliptic theta function are simple.
Source: Mumford, *Tata Lectures on Theta I*, section 1, one zero counted with multiplicity. -/
theorem bh6_theta_simple_aux (τ : ℂ) (hτ : 0 < τ.im) (z : ℂ)
    (hz : bh6_theta τ z = 0) : deriv (bh6_theta τ) z ≠ 0 := by
  obtain ⟨a, b, rfl⟩ := (bh6_theta_zeros τ hτ).2 z |>.mp hz
  exact (bh6_theta_deriv_translate_aux τ hτ a b).mpr (bh6_theta_deriv_origin_aux τ hτ)

private theorem bh6_analyticGermAt_isUnit_iff {n : ℕ} {p : Fin n → ℂ}
    (g : AnalyticGermAt n p) :
    IsUnit g ↔ analyticGermAtValue n p g ≠ 0 := by
  constructor
  · intro h
    exact (h.map (analyticGermAtValue n p)).ne_zero
  · obtain ⟨u, hu, hug⟩ := g.2
    intro h
    have hu0 : u p ≠ 0 := by
      change g.1.value ≠ 0 at h
      rw [← hug, Filter.Germ.value_ofFun] at h
      exact h
    let v : AnalyticGermAt n p :=
      ⟨Filter.Germ.ofFun (fun z ↦ (u z)⁻¹), fun z ↦ (u z)⁻¹, hu.inv hu0, rfl⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨v, ?_⟩
    apply Subtype.ext
    change g.1 * v.1 = 1
    rw [← hug]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hu.continuousAt.eventually_ne hu0] with z hz
    exact mul_inv_cancel₀ hz

private theorem bh6_squarefree_germ_of_fderiv_ne_zero {n : ℕ}
    {g : (Fin n → ℂ) → ℂ} {p : Fin n → ℂ} (hg : AnalyticAt ℂ g p)
    (hd : fderiv ℂ g p ≠ 0) :
    Squarefree (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p) := by
  intro a ha
  obtain ⟨b, hab⟩ := ha
  by_contra hau
  obtain ⟨u, hu, hua⟩ := a.2
  obtain ⟨v, hv, hvb⟩ := b.2
  have hu0 : u p = 0 := by
    by_contra h
    apply hau
    apply (bh6_analyticGermAt_isUnit_iff a).mpr
    change a.1.value ≠ 0
    rw [← hua, Filter.Germ.value_ofFun]
    exact h
  apply hd
  have he : g =ᶠ[𝓝 p] fun z ↦ u z * u z * v z := by
    apply Filter.Germ.coe_eq.mp
    calc
      Filter.Germ.ofFun g = (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p).1 := rfl
      _ = (a * a * b).1 := congrArg Subtype.val hab
      _ = a.1 * a.1 * b.1 := rfl
      _ = Filter.Germ.ofFun u * Filter.Germ.ofFun u * Filter.Germ.ofFun v := by rw [hua, hvb]
      _ = Filter.Germ.ofFun (fun z ↦ u z * u z * v z) := rfl
  rw [he.fderiv_eq]
  change fderiv ℂ (u * u * v) p = 0
  rw [fderiv_mul (hu.mul hu).differentiableAt hv.differentiableAt,
    fderiv_mul hu.differentiableAt hu.differentiableAt, hu0]
  apply ContinuousLinearMap.ext
  intro z
  simp [hu0]

/-- A one-variable function with simple zeros has reduced germs after a surjective linear pullback.
Source: Gunning--Rossi, Chapter II, regular local coordinates and reduced hypersurface germs. -/
theorem bh6_reduced_linear_pullback_aux (n : ℕ)
    (q : (Fin n → ℂ) →ₗ[ℂ] ℂ) (hq : Function.Surjective q)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hs : ∀ z, f z = 0 → deriv f z ≠ 0) :
    ∃ hg : AnalyticOnNhd ℂ (f ∘ q) univ,
      ∀ p, Squarefree (⟨Filter.Germ.ofFun (f ∘ q), f ∘ q,
        hg p (mem_univ p), rfl⟩ : AnalyticGermAt n p) := by
  have hqa : ∀ p, AnalyticAt ℂ q p := q.toContinuousLinearMap.analyticAt
  have hg : AnalyticOnNhd ℂ (f ∘ q) univ := fun p _ ↦
    (hf (q p) (mem_univ _)).comp (hqa p)
  refine ⟨hg, fun p ↦ ?_⟩
  by_cases hp : f (q p) = 0
  · apply bh6_squarefree_germ_of_fderiv_ne_zero (hg p (mem_univ p))
    rw [fderiv_comp p (hf (q p) (mem_univ _)).differentiableAt
      (hqa p).differentiableAt]
    intro hz
    have hd := hs (q p) hp
    apply hd
    obtain ⟨v, hv⟩ := hq 1
    have hzv := congrArg (fun L : (Fin n → ℂ) →L[ℂ] ℂ ↦ L v) hz
    have hqfd : fderiv ℂ (q : (Fin n → ℂ) → ℂ) p = q.toContinuousLinearMap :=
      q.toContinuousLinearMap.hasFDerivAt.fderiv
    rw [ContinuousLinearMap.comp_apply, hqfd] at hzv
    change fderiv ℂ f (q p) (q v) = 0 at hzv
    rw [hv] at hzv
    change fderiv ℂ f (q p) 1 = 0 at hzv
    exact hzv
  · apply IsUnit.squarefree
    apply (bh6_analyticGermAt_isUnit_iff _).mpr
    change (Filter.Germ.ofFun (f ∘ q)).value ≠ 0
    rw [Filter.Germ.value_ofFun]
    exact hp

/-- The identity point of the cubic is a nonempty codimension-one algebraic component.
Source: Hartshorne, Chapter I, section 6, closed points of a smooth integral curve. -/
theorem bh6_point_component_aux :
    ∃ x : E.left, Order.coheight x = 1 ∧
      bh4_componentSupport E x = {1} := by
  let z : ComplexPoint E := 1
  let x : E.left := z.underlying
  have hxclosed : IsClosed ({x} : Set E.left) :=
    ((pointEquivClosedPoint E.hom) ⟨z.left, z.w⟩).2
  refine ⟨x, coheight_eq_one_of_isClosed E x hxclosed, ?_⟩
  ext w
  change w.underlying ∈ closure ({x} : Set E.left) ↔ w = 1
  rw [hxclosed.closure_eq, Set.mem_singleton_iff]
  exact ⟨fun h => underlying_injective_of_locallyOfFiniteType (h.trans rfl),
    fun h => congrArg Point.underlying h⟩

/-- The image of the second factor's generic point under the coordinate inclusion.
Source: Hartshorne, Chapter II, section 6, generic points of prime divisors. -/
def bh6_product_generic : (g3_power E 2).left :=
  (g3_incl E 2 1).left (genericPoint E.left)

/-- The coordinate inclusion has irreducible closed image with the specified generic point.
Source: Hartshorne, Chapter I, section 1, images of irreducible spaces and generic points. -/
theorem bh6_product_generic_aux :
    IsGenericPoint bh6_product_generic (Set.range (g3_incl E 2 1).left) ∧
      IsClosed (Set.range (g3_incl E 2 1).left) ∧
      IsIrreducible (Set.range (g3_incl E 2 1).left) := by
  have hp : IsProper ((g3_incl E 2 1).left ≫ (g3_power E 2).hom) := by
    rw [(g3_incl E 2 1).w]
    infer_instance
  let : IsProper (g3_incl E 2 1).left :=
    IsProper.of_comp (g3_incl E 2 1).left (g3_power E 2).hom
  have hc := (g3_incl E 2 1).left.isClosedMap.isClosed_range
  have hg := (genericPoint_spec E.left).image (g3_incl E 2 1).left.continuous
  rw [Set.image_univ, hc.closure_eq] at hg
  exact ⟨hg, hc, hg.isIrreducible⟩

private theorem bh6_product_support_eq (x : (g3_power E 2).left)
    (hx : IsGenericPoint x (Set.range (g3_incl E 2 1).left)) :
    bh4_componentSupport (g3_power E 2) x =
      {z | AlgebraicGeometry.Point.map (g3_proj E 2 0) z = 1} := by
  ext z
  change z.underlying ∈ closure ({x} : Set _) ↔ _
  rw [hx]
  constructor
  · rintro ⟨y, hy⟩
    have hi : Function.Injective (g3_incl E 2 1).left := by
      intro a b hab
      have he := congrArg (g3_proj E 2 1).left hab
      change ((g3_incl E 2 1 ≫ g3_proj E 2 1).left) a =
        ((g3_incl E 2 1 ≫ g3_proj E 2 1).left) b at he
      simpa [spec_g3_incl_proj] using he
    have hzclosed : IsClosed ({z.underlying} : Set _) :=
      ((pointEquivClosedPoint (g3_power E 2).hom) ⟨z.left, z.w⟩).2
    have hpre : (g3_incl E 2 1).left ⁻¹' {z.underlying} = {y} := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun ht ↦ hi (ht.trans hy.symm), fun ht ↦ by subst t; exact hy⟩
    have hyclosed : IsClosed ({y} : Set E.left) := by
      rw [← hpre]
      exact hzclosed.preimage (g3_incl E 2 1).left.continuous
    let p := (pointEquivClosedPoint E.hom).symm ⟨y, hyclosed⟩
    let u : ComplexPoint E := Over.homMk p.1 p.2
    have hu : u.underlying = y :=
      congrArg Subtype.val
        ((pointEquivClosedPoint E.hom).apply_symm_apply ⟨y, hyclosed⟩)
    have hzu : Point.map (g3_incl E 2 1) u = z := by
      apply underlying_injective_of_locallyOfFiniteType
      change (g3_incl E 2 1).left u.underlying = z.underlying
      rw [hu, hy]
    rw [← hzu]
    change Point.map (g3_proj E 2 0) (Point.map (g3_incl E 2 1) u) = 1
    rw [← Point.map_comp_apply, spec_g3_incl_proj]
    change Point.map η (Point.map (SemiCartesianMonoidalCategory.toUnit E) u) =
      Point.map η (𝟙 _)
    exact congrArg (Point.map η) (Subsingleton.elim _ _)
  · intro hz
    let w : ComplexPoint E := Point.map (g3_proj E 2 1) z
    refine ⟨w.underlying, ?_⟩
    have he : Point.map (g3_incl E 2 1) w = z := by
      apply (complexPointProdEquiv E (g3_power E 1)).injective
      apply Prod.ext
      · change Point.map (g3_proj E 2 0) (Point.map (g3_incl E 2 1) w) =
          Point.map (g3_proj E 2 0) z
        rw [← Point.map_comp_apply, spec_g3_incl_proj, hz]
        change Point.map η (Point.map (SemiCartesianMonoidalCategory.toUnit E) w) =
          Point.map η (𝟙 _)
        exact congrArg (Point.map η) (Subsingleton.elim _ _)
      · apply (complexPointProdEquiv E (g3_power E 0)).injective
        apply Prod.ext
        · change Point.map (g3_proj E 2 1) (Point.map (g3_incl E 2 1) w) =
            Point.map (g3_proj E 2 1) z
          rw [← Point.map_comp_apply, spec_g3_incl_proj]
          rfl
        · apply Over.OverMorphism.ext
          let a : ComplexPoint (g3_power E 0) := ((complexPointProdEquiv E (g3_power E 0))
            ((complexPointProdEquiv E (g3_power E 1))
              (Point.map (g3_incl E 2 1) w)).2).2
          let b : ComplexPoint (g3_power E 0) := ((complexPointProdEquiv E (g3_power E 0))
            ((complexPointProdEquiv E (g3_power E 1)) z).2).2
          change a.left = b.left
          have ha : a.left ≫ 𝟙 (Spec ↧ℂ) = 𝟙 (Spec ↧ℂ) := a.w
          have hb : b.left ≫ 𝟙 (Spec ↧ℂ) = 𝟙 (Spec ↧ℂ) := b.w
          rw [← Category.comp_id a.left, ← Category.comp_id b.left]
          exact ha.trans hb.symm
    exact congrArg Point.underlying he

attribute [local instance] specializationOrder in
private theorem bh6_product_generic_height_pos (x : (g3_power E 2).left)
    (hx : IsGenericPoint x (Set.range (g3_incl E 2 1).left)) :
    0 < Order.height x := by
  let e : E.left := (1 : ComplexPoint E).underlying
  let y : (g3_power E 2).left := (g3_incl E 2 1).left e
  have hyle : y ≤ x := by
    change x ⤳ y
    apply specializes_iff_mem_closure.mpr
    rw [hx]
    exact ⟨e, rfl⟩
  have hine : Function.Injective (g3_incl E 2 1).left := by
    intro a b hab
    have he := congrArg (g3_proj E 2 1).left hab
    change ((g3_incl E 2 1 ≫ g3_proj E 2 1).left) a =
      ((g3_incl E 2 1 ≫ g3_proj E 2 1).left) b at he
    simpa [spec_g3_incl_proj] using he
  have heclosed : IsClosed ({e} : Set E.left) :=
    ((pointEquivClosedPoint E.hom) ⟨(1 : ComplexPoint E).left, (1 : ComplexPoint E).w⟩).2
  have heco : Order.coheight e = 1 := coheight_eq_one_of_isClosed E e heclosed
  have hgne : genericPoint E.left ≠ e := by
    intro h
    have hg0 : Order.coheight (genericPoint E.left) = 0 := coheight_genericPoint E.left
    rw [h, heco] at hg0
    norm_num at hg0
  have hyne : y ≠ x := by
    intro h
    have hp : IsProper ((g3_incl E 2 1).left ≫ (g3_power E 2).hom) := by
      rw [(g3_incl E 2 1).w]
      infer_instance
    letI : IsProper (g3_incl E 2 1).left :=
      IsProper.of_comp (g3_incl E 2 1).left (g3_power E 2).hom
    have hyclosed : IsClosed ({y} : Set (g3_power E 2).left) := by
      simpa [y] using (g3_incl E 2 1).left.isClosedMap _ heclosed
    have hr : Set.range (g3_incl E 2 1).left = {y} := by
      rw [← hx, ← h]
      exact hyclosed.closure_eq
    have hgy : (g3_incl E 2 1).left (genericPoint E.left) = y :=
      Set.mem_singleton_iff.mp (hr ▸ Set.mem_range_self (genericPoint E.left))
    exact hgne (hine (by simpa [y] using hgy))
  exact Order.height_pos.mpr (fun hmin ↦ hyne (le_antisymm hyle (hmin hyle)))

attribute [local instance] specializationOrder in
private theorem bh6_product_generic_coheight_pos (x : (g3_power E 2).left)
    (hx : IsGenericPoint x (Set.range (g3_incl E 2 1).left))
    (hs : bh4_componentSupport (g3_power E 2) x =
      {z | Point.map (g3_proj E 2 0) z = 1}) :
    0 < Order.coheight x := by
  classical
  let e : E.left := (1 : ComplexPoint E).underlying
  let a : E.left := if finitePoint.base default = e then cubicInfinity else finitePoint.base default
  have haclosed : IsClosed ({a} : Set E.left) := by
    dsimp [a]
    split_ifs
    · exact cubicPointOf_isClosed 0
    · exact finitePoint_isClosed
  have hae : a ≠ e := by
    dsimp [a]
    split_ifs with h
    · intro he
      exact CubicDivisor.finitePoint_ne_infinity (h.trans he.symm)
    · exact h
  let p := (pointEquivClosedPoint E.hom).symm ⟨a, haclosed⟩
  let u : ComplexPoint E := Over.homMk p.1 p.2
  have hu : u.underlying = a := congrArg Subtype.val
    ((pointEquivClosedPoint E.hom).apply_symm_apply ⟨a, haclosed⟩)
  have hu1 : u ≠ 1 := fun h ↦ hae (hu ▸ congrArg Point.underlying h)
  let z : ComplexPoint (g3_power E 2) := Point.map (g3_incl E 2 0) u
  have hzproj : Point.map (g3_proj E 2 0) z = u := by
    change Point.map (g3_proj E 2 0) (Point.map (g3_incl E 2 0) u) = u
    rw [← Point.map_comp_apply, spec_g3_incl_proj]
    rfl
  have hxne : x ≠ genericPoint (g3_power E 2).left := by
    intro he
    have hr : Set.range (g3_incl E 2 1).left = Set.univ := by
      rw [← hx, he, genericPoint_spec]
    have hzmem : z ∈ bh4_componentSupport (g3_power E 2) x := by
      change z.underlying ∈ closure ({x} : Set _)
      rw [hx, hr]
      trivial
    rw [hs] at hzmem
    exact hu1 (hzproj.symm.trans hzmem)
  apply Order.coheight_pos.mpr
  intro hmax
  have hc0 : Order.coheight x = 0 := Order.coheight_eq_zero.mpr hmax
  exact hxne (eq_genericPoint_of_coheight_zero x hc0)

private theorem bh6_product_generic_coheight_one (x : (g3_power E 2).left)
    (hh : 0 < Order.height x) (hc : 0 < Order.coheight x) :
    Order.coheight x = 1 := by
  have hrel := SmoothOfRelativeDimension.of_isIntegral (g3_power E 2).hom
  have hdim : dim (g3_power E 2).left = 2 := by rw [spec_g3link_dim_eq, E_dim]
  rw [hdim] at hrel
  letI : SmoothOfRelativeDimension 2 (g3_power E 2).hom := hrel
  have hs := SmoothOfRelativeDimension.height_add_coheight_le_complex
    (f := (g3_power E 2).hom) (d := 2) x
  have hh1 : (1 : ℕ∞) ≤ Order.height x := ENat.one_le_iff_ne_zero.mpr (ne_of_gt hh)
  have hc1 : (1 : ℕ∞) ≤ Order.coheight x := ENat.one_le_iff_ne_zero.mpr (ne_of_gt hc)
  have hc_le : Order.coheight x ≤ 1 := by
    have ht := (add_le_add_left hh1 (Order.coheight x)).trans hs
    have htwo : ((2 : ℕ) : ℕ∞) = 1 + 1 := by norm_num
    rw [htwo] at ht
    exact (ENat.add_le_add_iff_left (by norm_num : (1 : ℕ∞) ≠ ⊤)).mp ht
  exact le_antisymm hc_le hc1

/-- The generic point of the coordinate fiber has coheight one and the specified analytic support.
Source: Hartshorne, Chapter II, section 6, prime divisors on a smooth surface. -/
theorem bh6_product_support_aux (x : (g3_power E 2).left)
    (hx : IsGenericPoint x (Set.range (g3_incl E 2 1).left)) :
    Order.coheight x = 1 ∧ (bh4_componentSupport (g3_power E 2) x).Nonempty ∧
      bh4_componentSupport (g3_power E 2) x =
        {z | AlgebraicGeometry.Point.map (g3_proj E 2 0) z = 1} := by
  have hs := bh6_product_support_eq x hx
  refine ⟨bh6_product_generic_coheight_one x
    (bh6_product_generic_height_pos x hx)
    (bh6_product_generic_coheight_pos x hx hs), ?_, hs⟩
  rw [hs]
  refine ⟨Point.map (g3_incl E 2 1) (1 : ComplexPoint E), ?_⟩
  change Point.map (g3_proj E 2 0)
    (Point.map (g3_incl E 2 1) (1 : ComplexPoint E)) = 1
  rw [← Point.map_comp_apply, spec_g3_incl_proj]
  change Point.map η (Point.map (SemiCartesianMonoidalCategory.toUnit E) (1 : ComplexPoint E)) =
    Point.map η (𝟙 _)
  exact congrArg (Point.map η) (Subsingleton.elim _ _)

/-- The fiber of the first projection over the identity is a nonempty prime divisor in the square.
Source: Hartshorne, Chapter II, section 6, prime divisors; the fiber is the second elliptic factor. -/
theorem bh6_product_component_aux :
    ∃ x : (g3_power E 2).left, Order.coheight x = 1 ∧
      (bh4_componentSupport (g3_power E 2) x).Nonempty ∧
      bh4_componentSupport (g3_power E 2) x =
        {z | AlgebraicGeometry.Point.map (g3_proj E 2 0) z = 1} := by
  exact ⟨bh6_product_generic, bh6_product_support_aux bh6_product_generic
    bh6_product_generic_aux.1⟩

/-- Normalized period coordinates identify the theta zero set with the exponential kernel.
Source: Birkenhake--Lange, second edition, section 1.1; `abelianPeriodLattice`. -/
theorem bh6_theta_kernel (τ : ℂ) (hτ : 0 < τ.im)
    (q : (Fin (dim E.left) → ℂ) ≃ₗ[ℂ] ℂ)
    (a b : abelianPeriodLattice E →+ ℤ)
    (hs : Function.Surjective (fun l ↦ (a l, b l)))
    (hc : ∀ l : abelianPeriodLattice E, q l = (a l : ℂ) + τ * b l)
    (v : Fin (dim E.left) → ℂ) :
    bh6_theta τ (q v) = 0 ↔ abelianExp E v = 1 := by
  rw [(bh6_theta_zeros τ hτ).2]
  constructor
  · rintro ⟨i, j, hij⟩
    obtain ⟨l, hl⟩ := hs (i, j)
    have he : v = (l : Fin (dim E.left) → ℂ) := q.injective (by
      rw [hc, hij]
      simp only [Prod.mk.injEq] at hl
      rw [hl.1, hl.2])
    subst v
    have h : complexExponential E (dim E.left) (l : Fin (dim E.left) → ℂ) = 0 := l.2
    simp only [abelianExp, h]
    rfl
  · intro hv
    have hl : v ∈ abelianPeriodLattice E := by
      change complexExponential E (dim E.left) v = 0
      exact congrArg Additive.ofMul hv
    exact ⟨a ⟨v, hl⟩, b ⟨v, hl⟩, hc ⟨v, hl⟩⟩

/-- A nonzero entire reduced equation gives simultaneous equation and component boundary avoidance.
Source: `bh5_analytic_set_avoidance_aux`; analytic zero sets. -/
theorem bh6_component_avoidance (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (S : Set (ComplexPoint X))
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hne : ∃ v, f v ≠ 0)
    (hs : ∀ v, f v = 0 ↔ abelianExp X v ∈ S)
    (l m : abelianPeriodLattice X) :
    ∃ z : Fin (dim X.left) → ℂ,
      (∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) ∧
      (∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
        abelianExp X (bh4_squareEdge X l m z i t) ∉ S) := by
  have hd : Differentiable ℂ f := fun v ↦ (hf v (mem_univ v)).differentiableAt
  obtain ⟨z, hz⟩ := bh5_analytic_set_avoidance_aux X {v | f v = 0}
    (AnalyticDivisorAlgebraic2.spec_isClosedAnalytic_zeroSet_of_differentiable hd)
    (by intro he; obtain ⟨v, hv⟩ := hne; apply hv; change v ∈ {v | f v = 0}; rw [he]; trivial) l m
  exact ⟨z, hz, fun i t ht h ↦ hz i t ht ((hs _).mpr h)⟩

/-- The theta equation is not the zero function, since its zero at the origin is simple.
Source: `bh6_theta_simple_aux`; derivative of the zero function. -/
theorem bh6_theta_nonzero (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ z, bh6_theta τ z ≠ 0 := by
  by_contra! h
  have he : bh6_theta τ = fun _ ↦ 0 := funext h
  have hz : bh6_theta τ 0 = 0 := h 0
  have hd := bh6_theta_simple_aux τ hτ 0 hz
  rw [he] at hd
  simp at hd

/-- Assemble the simultaneous component witness in dimension 1.
Source: the theta zero, reduced pullback and component constructions above. -/
theorem bh6_witness_component_dim1 :
    ∃ (x : E.left) (f : (Fin (dim E.left) → ℂ) → ℂ)
      (hf : AnalyticOnNhd ℂ f univ),
      Order.coheight x = 1 ∧ (bh4_componentSupport E x).Nonempty ∧
      (∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
        AnalyticGermAt (dim E.left) p)) ∧
      (∀ p, f p = 0 ↔ abelianExp E p ∈ bh4_componentSupport E x) ∧
      ∀ l m : abelianPeriodLattice E, ∃ z : Fin (dim E.left) → ℂ,
        (∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
          f (bh4_squareEdge E l m z i t) ≠ 0) ∧
        (∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
          abelianExp E (bh4_squareEdge E l m z i t) ∉ cycleComponentSupport E x) := by
  obtain ⟨τ, q, a, b, hτ, hs, hc⟩ := bh6_elliptic_coordinates_aux
  obtain ⟨x, hx, hxS⟩ := bh6_point_component_aux
  obtain ⟨hf, hred⟩ := bh6_reduced_linear_pullback_aux (dim E.left) q.toLinearMap
    q.surjective (bh6_theta τ) (bh6_theta_zeros τ hτ).1
    (bh6_theta_simple_aux τ hτ)
  have he : ∀ v, (bh6_theta τ ∘ q) v = 0 ↔ abelianExp E v ∈ bh4_componentSupport E x := by
    intro v
    rw [hxS, Set.mem_singleton_iff]
    exact bh6_theta_kernel τ hτ q a b hs hc v
  have hn : ∃ v, (bh6_theta τ ∘ q) v ≠ 0 := by
    obtain ⟨w, hw⟩ := bh6_theta_nonzero τ hτ
    exact ⟨q.symm w, by simpa using hw⟩
  refine ⟨x, bh6_theta τ ∘ q, hf, hx, ?_, hred, he, ?_⟩
  · rw [hxS]; exact Set.singleton_nonempty _
  · exact fun l m ↦ bh6_component_avoidance E (bh4_componentSupport E x) _ hf hn he l m

/-- Assemble the simultaneous component witness in dimension 2.
Source: the theta zero, reduced pullback and component constructions above. -/
theorem bh6_witness_component_dim2 :
    ∃ (x : (g3_power E 2).left) (f : (Fin (dim (g3_power E 2).left) → ℂ) → ℂ)
      (hf : AnalyticOnNhd ℂ f univ),
      Order.coheight x = 1 ∧ (bh4_componentSupport (g3_power E 2) x).Nonempty ∧
      (∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
        AnalyticGermAt (dim (g3_power E 2).left) p)) ∧
      (∀ p, f p = 0 ↔ abelianExp (g3_power E 2) p ∈ bh4_componentSupport (g3_power E 2) x) ∧
      ∀ l m : abelianPeriodLattice (g3_power E 2), ∃ z : Fin (dim (g3_power E 2).left) → ℂ,
        (∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
          f (bh4_squareEdge (g3_power E 2) l m z i t) ≠ 0) ∧
        (∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
          abelianExp (g3_power E 2) (bh4_squareEdge (g3_power E 2) l m z i t) ∉ cycleComponentSupport (g3_power E 2) x) := by
  obtain ⟨τ, q, a, b, hτ, hs, hc⟩ := bh6_elliptic_coordinates_aux
  obtain ⟨Q, t, ht, hQ⟩ := bh6_product_coordinates_aux
  obtain ⟨x, hx, hxne, hxS⟩ := bh6_product_component_aux
  let r : (Fin (dim (g3_power E 2).left) → ℂ) →ₗ[ℂ] ℂ :=
    q.toLinearMap.comp ((LinearMap.proj (0 : Fin 2)).comp Q.toLinearMap)
  have hr : Function.Surjective r := by
    intro w
    refine ⟨Q.symm (fun _ ↦ q.symm w), ?_⟩
    simp [r]
  obtain ⟨hf, hred⟩ := bh6_reduced_linear_pullback_aux _ r hr (bh6_theta τ)
    (bh6_theta_zeros τ hτ).1 (bh6_theta_simple_aux τ hτ)
  have he : ∀ v, (bh6_theta τ ∘ r) v = 0 ↔
      abelianExp (g3_power E 2) v ∈ bh4_componentSupport (g3_power E 2) x := by
    intro v
    rw [hxS]
    change bh6_theta τ (q (Q v 0)) = 0 ↔ _ = 1
    rw [hQ]
    exact bh6_theta_kernel τ hτ q a b hs hc (Q v 0)
  have hn : ∃ v, (bh6_theta τ ∘ r) v ≠ 0 := by
    obtain ⟨w, hw⟩ := bh6_theta_nonzero τ hτ
    obtain ⟨v, hv⟩ := hr w
    exact ⟨v, by simpa [Function.comp_apply, hv] using hw⟩
  exact ⟨x, bh6_theta τ ∘ r, hf, hx, hxne, hred, he,
    fun l m ↦ bh6_component_avoidance (g3_power E 2) (bh4_componentSupport (g3_power E 2) x) _ hf hn he l m⟩

end HodgeLean.Adapters

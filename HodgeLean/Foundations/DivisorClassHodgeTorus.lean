import Mathlib

/-! # Dolbeault on the flat torus: Fourier analysis on `ℤ^ι`-periodic functions (DC1-c)

Helpers for `dc1_torus_dbar_aux`. A `ℤ^ι`-periodic function on `ι → ℝ` is a function on
`UnitAddTorus ι`; its Fourier coefficients are integrals over a unit cube. This file proves:

* translation multiplies the coefficients by a character, so integration by parts holds for
  periodic `C¹` functions (`dct_coeff_fderiv`);
* the coefficients of a smooth periodic function decay rapidly (`dct_coeff_decay`);
* a rapidly decaying trigonometric series is smooth and is differentiated termwise;
* a continuous periodic function with summable coefficients is the sum of its Fourier series
  (Mathlib's `hasSum_mFourier_series_apply_of_summable`).

Source: Grafakos, *Classical Fourier Analysis*, §3.1 and §3.2; BL §1.4.
-/

noncomputable section
open MeasureTheory Set Filter Topology UnitAddTorus
open scoped ContDiff

namespace HodgeLean.Foundations

variable {ι : Type} [Fintype ι]

/-- `ℤ^ι`-periodicity of a function on `ι → ℝ`. -/
def dct_Periodic (F : (ι → ℝ) → ℂ) : Prop := ∀ (k : ι → ℤ) x, F (x + fun i ↦ (k i : ℝ)) = F x

/-- The unit cube `∏ (aᵢ, aᵢ + 1]`. -/
def dct_cube (a : ι → ℝ) : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc (a i) (a i + 1)}

/-- The character `x ↦ e^{2πi ⟨ξ, x⟩}`. -/
def dct_char (ξ : ι → ℤ) (x : ι → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ i, (ξ i : ℂ) * (x i : ℂ))

/-- The Fourier coefficient over the unit cube. -/
def dct_coeff (F : (ι → ℝ) → ℂ) (ξ : ι → ℤ) : ℂ :=
  ∫ x in dct_cube 0, dct_char (-ξ) x * F x

/-- The projection `ι → ℝ` to the torus. -/
def dct_proj (x : ι → ℝ) : UnitAddTorus ι := fun i ↦ (x i : UnitAddCircle)

/-- The function on the torus induced by a function on `ι → ℝ`. -/
def dct_desc (F : (ι → ℝ) → ℂ) (y : UnitAddTorus ι) : ℂ :=
  F fun i ↦ (AddCircle.equivIoc 1 0 (y i) : ℝ)

theorem dct_mFourier_proj (ξ : ι → ℤ) (x : ι → ℝ) :
    mFourier ξ (dct_proj x) = dct_char ξ x := by
  simp only [mFourier, ContinuousMap.coe_mk, dct_proj, fourier_coe_apply, dct_char,
    Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  congr 1
  push_cast
  ring

omit [Fintype ι] in
theorem dct_desc_proj {F : (ι → ℝ) → ℂ} (hF : dct_Periodic F) (x : ι → ℝ) :
    dct_desc F (dct_proj x) = F x := by
  have : ∀ i, ∃ k : ℤ, (AddCircle.equivIoc 1 0 ((x i : ℝ) : UnitAddCircle) : ℝ) = x i + k := by
    intro i
    have h0 : (((AddCircle.equivIoc 1 0 ((x i : ℝ) : UnitAddCircle) : ℝ) - x i : ℝ) :
        UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, AddCircle.coe_equivIoc, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff 1).mp h0
    exact ⟨k, by rw [zsmul_one] at hk; linarith⟩
  choose k hk using this
  have := hF k x
  simp only [dct_desc, dct_proj]
  rw [← this]
  congr 1
  funext i
  simp [hk i]

omit [Fintype ι] in
theorem dct_proj_isOpenQuotientMap : IsOpenQuotientMap (dct_proj (ι := ι)) :=
  IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk

omit [Fintype ι] in
theorem dct_continuous_desc {F : (ι → ℝ) → ℂ} (hF : dct_Periodic F) (hc : Continuous F) :
    Continuous (dct_desc F) := by
  rw [dct_proj_isOpenQuotientMap.isQuotientMap.continuous_iff]
  convert hc using 1
  funext x
  exact dct_desc_proj hF x


theorem dct_coeff_eq_mFourierCoeff {F : (ι → ℝ) → ℂ} (hF : dct_Periodic F) (ξ : ι → ℤ)
    (a : ι → ℝ) : mFourierCoeff (dct_desc F) ξ = ∫ x in dct_cube a, dct_char (-ξ) x * F x := by
  rw [mFourierCoeff_eq_integral _ ξ a]
  refine setIntegral_congr_fun ?_ fun x _ ↦ ?_
  · exact MeasurableSet.univ_pi' fun _ ↦ measurableSet_Ioc
  · change mFourier (-ξ) (dct_proj x) • dct_desc F (dct_proj x) = _
    rw [dct_mFourier_proj, dct_desc_proj hF, smul_eq_mul]

theorem dct_coeff_eq_cube {F : (ι → ℝ) → ℂ} (hF : dct_Periodic F) (ξ : ι → ℤ) (a : ι → ℝ) :
    dct_coeff F ξ = ∫ x in dct_cube a, dct_char (-ξ) x * F x := by
  rw [← dct_coeff_eq_mFourierCoeff hF, dct_coeff, dct_coeff_eq_mFourierCoeff hF]

theorem dct_char_add (ξ : ι → ℤ) (x y : ι → ℝ) :
    dct_char ξ (x + y) = dct_char ξ x * dct_char ξ y := by
  simp only [dct_char, ← Complex.exp_add, Pi.add_apply, Complex.ofReal_add, mul_add,
    Finset.sum_add_distrib]

theorem dct_char_neg_mul (ξ : ι → ℤ) (x : ι → ℝ) : dct_char (-ξ) x * dct_char ξ x = 1 := by
  simp only [dct_char, ← Complex.exp_add, Pi.neg_apply, Int.cast_neg, neg_mul,
    Finset.sum_neg_distrib, mul_neg, neg_add_cancel, Complex.exp_zero]

theorem dct_norm_char (ξ : ι → ℤ) (x : ι → ℝ) : ‖dct_char ξ x‖ = 1 := by
  rw [dct_char, Complex.norm_exp]
  simp

omit [Fintype ι] in
theorem dct_periodic_shift {F : (ι → ℝ) → ℂ} (hF : dct_Periodic F) (t : ι → ℝ) :
    dct_Periodic fun x ↦ F (x + t) := by
  intro k x
  simp only
  rw [add_right_comm, hF]

theorem dct_coeff_shift {F : (ι → ℝ) → ℂ} (hF : dct_Periodic F) (t : ι → ℝ) (ξ : ι → ℤ) :
    dct_coeff (fun x ↦ F (x + t)) ξ = dct_char ξ t * dct_coeff F ξ := by
  have hpre : dct_cube (0 : ι → ℝ) = (· + t) ⁻¹' dct_cube t := by
    ext x
    simp only [dct_cube, mem_ofPred_eq, mem_preimage, Pi.add_apply, Pi.zero_apply, zero_add,
      mem_Ioc]
    exact forall_congr' fun i ↦ by constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hmp := measurePreserving_add_right (volume : Measure (ι → ℝ)) t
  have hemb : MeasurableEmbedding (· + t : (ι → ℝ) → ι → ℝ) :=
    (MeasurableEquiv.addRight t).measurableEmbedding
  have key := hmp.setIntegral_preimage_emb hemb (fun y ↦ dct_char (-ξ) (y - t) * F y)
    (dct_cube t)
  rw [dct_coeff, hpre, dct_coeff_eq_cube hF ξ t, ← integral_const_mul]
  simp only [add_sub_cancel_right] at key
  rw [key]
  refine setIntegral_congr_fun ?_ fun x _ ↦ ?_
  · exact MeasurableSet.univ_pi' fun _ ↦ measurableSet_Ioc
  · have h1 := dct_char_add (-ξ) (x - t) t
    have h2 := dct_char_neg_mul ξ t
    rw [sub_add_cancel] at h1
    rw [h1]
    linear_combination (-(dct_char (-ξ) (x - t) * F x)) * h2


theorem dct_volume_cube (a : ι → ℝ) : volume (dct_cube a) = 1 := by
  have : dct_cube a = Set.pi univ fun i ↦ Ioc (a i) (a i + 1) := by
    ext x
    simp [dct_cube]
  rw [this, volume_pi_pi]
  simp

theorem dct_measurableSet_cube (a : ι → ℝ) : MeasurableSet (dct_cube a) :=
  MeasurableSet.univ_pi' fun _ ↦ measurableSet_Ioc

omit [Fintype ι] in
theorem dct_exists_bound {G : (ι → ℝ) → ℂ} (hG : dct_Periodic G) (hc : Continuous G) :
    ∃ C, ∀ x, ‖G x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (dct_continuous_desc hG hc).continuousOn
  exact ⟨C, fun x ↦ by simpa [dct_desc_proj hG] using hC (dct_proj x) (mem_univ _)⟩

theorem dct_norm_coeff_le {G : (ι → ℝ) → ℂ} {C : ℝ} (hC : ∀ x, ‖G x‖ ≤ C) (ξ : ι → ℤ) :
    ‖dct_coeff G ξ‖ ≤ C := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := fun x ↦ dct_char (-ξ) x * G x) (s := dct_cube 0) (C := C)
    (by rw [dct_volume_cube]; exact ENNReal.one_lt_top)
    (fun x _ ↦ by rw [norm_mul, dct_norm_char, one_mul]; exact hC x)
  rwa [measureReal_def, dct_volume_cube, ENNReal.toReal_one, mul_one] at h

theorem dct_periodic_fderiv {F : (ι → ℝ) → ℂ} (hF : dct_Periodic F) (v : ι → ℝ) :
    dct_Periodic fun x ↦ fderiv ℝ F x v := by
  intro k x
  have : (fun y ↦ F (y + fun i ↦ (k i : ℝ))) = F := funext fun y ↦ hF k y
  simp only
  rw [← fderiv_comp_add_right (f := F) (x := x) (fun i ↦ (k i : ℝ)), this]

theorem dct_hasDerivAt_char (ξ : ι → ℤ) (v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ dct_char ξ (s • v))
      (2 * Real.pi * Complex.I * (∑ i, (ξ i : ℂ) * (v i : ℂ)) * dct_char ξ (t • v)) t := by
  have h : (fun s : ℝ ↦ dct_char ξ (s • v)) = fun s : ℝ ↦
      Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I * ∑ i, (ξ i : ℂ) * (v i : ℂ))) := by
    funext s
    simp only [dct_char, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [h]
  have := ((hasDerivAt_id (t : ℂ)).mul_const
    (2 * Real.pi * Complex.I * ∑ i, (ξ i : ℂ) * (v i : ℂ))).cexp.comp_ofReal
  convert this using 1
  · rfl
  · rw [show dct_char ξ (t • v) = _ from congrFun h t]
    simp only [id, one_mul]
    ring

/-- Integration by parts on the torus, through translation invariance. -/
theorem dct_coeff_fderiv {F : (ι → ℝ) → ℂ} (hF : dct_Periodic F) (hc : ContDiff ℝ 1 F)
    (v : ι → ℝ) (ξ : ι → ℤ) :
    dct_coeff (fun x ↦ fderiv ℝ F x v) ξ =
      2 * Real.pi * Complex.I * (∑ i, (ξ i : ℂ) * (v i : ℂ)) * dct_coeff F ξ := by
  have hd : Differentiable ℝ F := hc.differentiable one_ne_zero
  have hc' : Continuous fun x ↦ fderiv ℝ F x v :=
    (hc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨B, hB⟩ := dct_exists_bound (dct_periodic_fderiv hF v) hc'
  have hfin : volume (dct_cube (0 : ι → ℝ)) < ⊤ := by
    rw [dct_volume_cube]; exact ENNReal.one_lt_top
  have : IsFiniteMeasure (volume.restrict (dct_cube (0 : ι → ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨B0, hB0⟩ := dct_exists_bound hF hd.continuous
  have hcont : ∀ t : ℝ, Continuous fun x ↦ dct_char (-ξ) x * F (x + t • v) := by
    intro t
    refine Continuous.mul ?_ (hd.continuous.comp (continuous_id.add continuous_const))
    unfold dct_char
    fun_prop
  have hcont' : ∀ t : ℝ, Continuous fun x ↦ dct_char (-ξ) x * fderiv ℝ F (x + t • v) v := by
    intro t
    refine Continuous.mul ?_ (hc'.comp (continuous_id.add continuous_const))
    unfold dct_char
    fun_prop
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (dct_cube 0)) (x₀ := (0 : ℝ)) (s := univ)
    (F := fun t x ↦ dct_char (-ξ) x * F (x + t • v))
    (F' := fun t x ↦ dct_char (-ξ) x * fderiv ℝ F (x + t • v) v) (bound := fun _ ↦ B)
    Filter.univ_mem (Eventually.of_forall fun t ↦ (hcont t).aestronglyMeasurable)
    (Integrable.of_bound (hcont 0).aestronglyMeasurable B0 (Eventually.of_forall fun x ↦ by
      rw [norm_mul, dct_norm_char, one_mul]; exact hB0 _))
    (hcont' 0).aestronglyMeasurable
    (Eventually.of_forall fun x t _ ↦ by
      rw [norm_mul, dct_norm_char, one_mul]; exact hB _)
    (integrable_const B)
    (Eventually.of_forall fun x t _ ↦ by
      have h1 : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add x
      exact ((hd (x + t • v)).hasFDerivAt.comp_hasDerivAt t h1).const_mul _)
  have h2 : HasDerivAt (fun t : ℝ ↦ dct_coeff (fun x ↦ F (x + t • v)) ξ)
      (2 * Real.pi * Complex.I * (∑ i, (ξ i : ℂ) * (v i : ℂ)) * dct_char ξ ((0 : ℝ) • v) *
        dct_coeff F ξ) 0 := by
    have : (fun t : ℝ ↦ dct_coeff (fun x ↦ F (x + t • v)) ξ) =
        fun t ↦ dct_char ξ (t • v) * dct_coeff F ξ :=
      funext fun t ↦ dct_coeff_shift hF _ ξ
    rw [this]
    exact (dct_hasDerivAt_char ξ v 0).mul_const _
  have h3 := hint.2.unique h2
  simp only [zero_smul, add_zero] at h3
  rw [dct_coeff, h3]
  simp [dct_char]


/-- The directional derivative `x ↦ DF(x) v`. -/
def dct_D (v : ι → ℝ) (F : (ι → ℝ) → ℂ) (x : ι → ℝ) : ℂ := fderiv ℝ F x v

theorem dct_contDiff_D {F : (ι → ℝ) → ℂ} (hc : ContDiff ℝ ∞ F) (v : ι → ℝ) :
    ContDiff ℝ ∞ (dct_D v F) :=
  (hc.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem dct_coeff_iterate_D {F : (ι → ℝ) → ℂ} (hF : dct_Periodic F) (hc : ContDiff ℝ ∞ F)
    (v : ι → ℝ) (ξ : ι → ℤ) (m : ℕ) :
    dct_Periodic ((dct_D v)^[m] F) ∧ ContDiff ℝ ∞ ((dct_D v)^[m] F) ∧
      dct_coeff ((dct_D v)^[m] F) ξ =
        (2 * Real.pi * Complex.I * (∑ i, (ξ i : ℂ) * (v i : ℂ))) ^ m * dct_coeff F ξ := by
  induction m with
  | zero => simp [hF, hc]
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨dct_periodic_fderiv h1 v, dct_contDiff_D h2 v, ?_⟩
    change dct_coeff (fun x ↦ fderiv ℝ ((dct_D v)^[m] F) x v) ξ = _
    rw [dct_coeff_fderiv h1 (h2.of_le (by simp)) v ξ, h3, pow_succ]
    ring

theorem dct_exists_norm_eq {ξ : ι → ℤ} (h : ξ ≠ 0) : ∃ i, ‖ξ‖ = ‖ξ i‖ := by
  have hne : (Finset.univ : Finset ι).Nonempty := by
    obtain ⟨i, -⟩ := Function.ne_iff.mp h
    exact ⟨i, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne fun b ↦ ‖ξ b‖₊
  refine ⟨i, ?_⟩
  have := congrArg ((↑) : NNReal → ℝ) ((Pi.nnnorm_def ξ).trans hi)
  simpa using this

/-- Rapid decay of the Fourier coefficients of a smooth periodic function. -/
theorem dct_coeff_decay {F : (ι → ℝ) → ℂ} (hF : dct_Periodic F) (hc : ContDiff ℝ ∞ F)
    (m : ℕ) : ∃ C, ∀ ξ, ‖ξ‖ ^ m * ‖dct_coeff F ξ‖ ≤ C := by
  classical
  have hb : ∀ i : ι, ∃ C, ∀ ξ : ι → ℤ, ‖(ξ i : ℝ)‖ ^ m * ‖dct_coeff F ξ‖ ≤ C := by
    intro i
    obtain ⟨h1, h2, -⟩ := dct_coeff_iterate_D hF hc (Pi.single i 1) 0 m
    obtain ⟨B, hB⟩ := dct_exists_bound h1 h2.continuous
    refine ⟨B / (2 * Real.pi) ^ m, fun ξ ↦ ?_⟩
    have h3 := (dct_coeff_iterate_D hF hc (Pi.single i 1) ξ m).2.2
    have h4 := dct_norm_coeff_le hB ξ
    rw [h3, norm_mul, norm_pow] at h4
    have hsum : (∑ j, (ξ j : ℂ) * ((Pi.single i (1 : ℝ) : ι → ℝ) j : ℂ)) = (ξ i : ℂ) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · simp
    rw [hsum] at h4
    have h5 : ‖2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)‖ = 2 * Real.pi * ‖(ξ i : ℝ)‖ := by
      simp [abs_of_pos Real.pi_pos]
    rw [h5, mul_pow] at h4
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_pos (mul_pos two_pos Real.pi_pos) m]
  choose C hC using hb
  obtain ⟨C0, hC0⟩ := dct_exists_bound hF hc.continuous
  refine ⟨∑ i, max (C i) 0 + max C0 0, fun ξ ↦ ?_⟩
  have hs : 0 ≤ ∑ i, max (C i) 0 := Finset.sum_nonneg fun i _ ↦ le_max_right _ _
  by_cases hξ : ξ = 0
  · subst hξ
    rcases m with _ | m
    · simp only [pow_zero, one_mul]
      exact (dct_norm_coeff_le hC0 0).trans ((le_max_left _ _).trans (by linarith))
    · simp only [norm_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, zero_mul]
      positivity
  · obtain ⟨i, hi⟩ := dct_exists_norm_eq hξ
    have := hC i ξ
    rw [hi]
    have h6 : max (C i) 0 ≤ ∑ j, max (C j) 0 :=
      Finset.single_le_sum (f := fun j ↦ max (C j) 0) (fun j _ ↦ le_max_right _ _)
        (Finset.mem_univ i)
    have : ‖ξ i‖ = ‖(ξ i : ℝ)‖ := by simp [Int.norm_eq_abs]
    rw [this]
    linarith [le_max_left (C i) 0, le_max_right C0 0]


/-! ### Summability over `ℤ^ι` -/

theorem dct_summable_norm_inv_pow (N : ℕ) (hN : Fintype.card ι < N) :
    Summable fun ξ : ι → ℤ ↦ ‖ξ‖⁻¹ ^ N := by
  classical
  let b := Pi.basisFun ℝ ι
  let L0 := Submodule.span ℤ (Set.range b)
  have hrank : Module.finrank ℤ L0 = Fintype.card ι := by
    rw [ZLattice.rank ℝ L0, Module.finrank_fintype_fun_eq_card]
  have hmem : ∀ ξ : ι → ℤ, (fun i ↦ (ξ i : ℝ)) ∈ L0 := fun ξ ↦
    (b.mem_span_iff_repr_mem ℤ _).mpr fun i ↦ ⟨ξ i, by simp [b]⟩
  let j : (ι → ℤ) → L0 := fun ξ ↦ ⟨fun i ↦ (ξ i : ℝ), hmem ξ⟩
  have hj : Function.Injective j := by
    intro ξ η h
    funext i
    have := congrFun (congrArg Subtype.val h) i
    simp only [j] at this
    exact_mod_cast this
  have hnorm : ∀ ξ, ‖j ξ‖ = ‖ξ‖ := by
    intro ξ
    change ‖(fun i ↦ (ξ i : ℝ))‖ = ‖ξ‖
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ ?_)
      ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ ?_)
    · rw [Int.norm_cast_real]; exact norm_le_pi_norm ξ i
    · rw [← Int.norm_cast_real]; exact norm_le_pi_norm (fun i ↦ (ξ i : ℝ)) i
  have := (ZLattice.summable_norm_pow_inv L0 N (by rw [hrank]; exact hN)).comp_injective hj
  exact this.congr fun ξ ↦ by simp only [Function.comp_apply, hnorm]

/-- A sequence with `‖ξ‖^(d+1) ‖b ξ‖` bounded is summable. -/
theorem dct_summable_of_decay {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {b : (ι → ℤ) → E} {C : ℝ}
    (h : ∀ ξ, ‖ξ‖ ^ (Fintype.card ι + 1) * ‖b ξ‖ ≤ C) : Summable b := by
  refine Summable.of_norm_bounded_eventually
    ((dct_summable_norm_inv_pow (Fintype.card ι + 1) (Nat.lt_succ_self _)).mul_left C) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with ξ hξ
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have := h ξ
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact this

theorem dct_decay_mul_pow {a : (ι → ℤ) → ℂ} (ha : ∀ m, ∃ C, ∀ ξ, ‖ξ‖ ^ m * ‖a ξ‖ ≤ C)
    (c : ℝ) (hc : 0 ≤ c) (k : ℕ) :
    Summable fun ξ ↦ ‖a ξ‖ * (c * ‖ξ‖) ^ k := by
  obtain ⟨C, hC⟩ := ha (Fintype.card ι + 1 + k)
  refine dct_summable_of_decay (C := c ^ k * C) fun ξ ↦ ?_
  rw [Real.norm_of_nonneg (by positivity)]
  have := hC ξ
  calc ‖ξ‖ ^ (Fintype.card ι + 1) * (‖a ξ‖ * (c * ‖ξ‖) ^ k)
      = c ^ k * (‖ξ‖ ^ (Fintype.card ι + 1 + k) * ‖a ξ‖) := by ring
    _ ≤ c ^ k * C := by gcongr

/-! ### Smooth trigonometric series -/

/-- The derivative of the character `dct_char ξ`, divided by its value. -/
def dct_Lam (ξ : ι → ℤ) : (ι → ℝ) →L[ℝ] ℂ :=
  ∑ i, (2 * Real.pi * Complex.I * (ξ i : ℂ)) • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

theorem dct_Lam_apply (ξ : ι → ℤ) (v : ι → ℝ) :
    dct_Lam ξ v = 2 * Real.pi * Complex.I * ∑ i, (ξ i : ℂ) * (v i : ℂ) := by
  simp [dct_Lam, Finset.mul_sum, mul_assoc]

theorem dct_char_eq_exp (ξ : ι → ℤ) (x : ι → ℝ) : dct_char ξ x = Complex.exp (dct_Lam ξ x) := by
  rw [dct_char, dct_Lam_apply]

theorem dct_hasFDerivAt_char (ξ : ι → ℤ) (x : ι → ℝ) :
    HasFDerivAt (dct_char ξ) (dct_char ξ x • dct_Lam ξ) x := by
  have : dct_char ξ = fun y ↦ Complex.exp (dct_Lam ξ y) := funext (dct_char_eq_exp ξ)
  rw [this]
  exact (dct_Lam ξ).hasFDerivAt.cexp

theorem dct_contDiff_char (ξ : ι → ℤ) : ContDiff ℝ ∞ (dct_char ξ) := by
  have : dct_char ξ = fun y ↦ Complex.exp (dct_Lam ξ y) := funext (dct_char_eq_exp ξ)
  rw [this]
  exact Complex.contDiff_exp.comp (dct_Lam ξ).contDiff

theorem dct_norm_Lam_le (ξ : ι → ℤ) :
    ‖dct_Lam ξ‖ ≤ 2 * Real.pi * Fintype.card ι * ‖ξ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [dct_Lam_apply, norm_mul]
  have h1 : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by simp [abs_of_pos Real.pi_pos]
  rw [h1]
  have h2 : ‖∑ i, (ξ i : ℂ) * (v i : ℂ)‖ ≤ Fintype.card ι * (‖ξ‖ * ‖v‖) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i ∈ (Finset.univ : Finset ι), ‖(ξ i : ℂ) * (v i : ℂ)‖ ≤ ‖ξ‖ * ‖v‖ := by
      intro i _
      rw [norm_mul]
      have e1 : ‖(ξ i : ℂ)‖ = ‖ξ i‖ := by simp [Int.norm_eq_abs]
      have e2 : ‖(v i : ℂ)‖ = ‖v i‖ := by simp
      rw [e1, e2]
      exact mul_le_mul (norm_le_pi_norm ξ i) (norm_le_pi_norm v i) (norm_nonneg _)
        (norm_nonneg _)
    refine (Finset.sum_le_sum this).trans ?_
    simp
  calc 2 * Real.pi * ‖∑ i, (ξ i : ℂ) * (v i : ℂ)‖
      ≤ 2 * Real.pi * (Fintype.card ι * (‖ξ‖ * ‖v‖)) := by gcongr
    _ = 2 * Real.pi * Fintype.card ι * ‖ξ‖ * ‖v‖ := by ring

theorem dct_fderiv_term (b : ℂ) (ξ : ι → ℤ) :
    fderiv ℝ (fun x ↦ b * dct_char ξ x) = fun x ↦ (b * dct_char ξ x) • dct_Lam ξ := by
  funext x
  rw [((dct_hasFDerivAt_char ξ x).const_mul b).fderiv, smul_smul]

theorem dct_norm_iteratedFDeriv_term (b : ℂ) (ξ : ι → ℤ) (k : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ k (fun x ↦ b * dct_char ξ x) x‖ ≤ ‖b‖ * ‖dct_Lam ξ‖ ^ k := by
  induction k generalizing x with
  | zero => simp [norm_iteratedFDeriv_zero, dct_norm_char]
  | succ k ih =>
    rw [← norm_iteratedFDeriv_fderiv, dct_fderiv_term]
    let Sm : ℂ →L[ℝ] ((ι → ℝ) →L[ℝ] ℂ) := (ContinuousLinearMap.id ℝ ℂ).smulRight (dct_Lam ξ)
    have hSm : ‖Sm‖ ≤ ‖dct_Lam ξ‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun t ↦ ?_
      simp only [Sm, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, norm_smul]
      rw [mul_comm]
    have hfun : (fun x ↦ (b * dct_char ξ x) • dct_Lam ξ) = Sm ∘ fun x ↦ b * dct_char ξ x := by
      funext x; simp [Sm]
    rw [hfun]
    have hcd : ContDiff ℝ ∞ fun x ↦ b * dct_char ξ x := contDiff_const.mul (dct_contDiff_char ξ)
    refine (Sm.norm_iteratedFDeriv_comp_left (hcd.contDiffAt) (by simp)).trans ?_
    calc ‖Sm‖ * ‖iteratedFDeriv ℝ k (fun x ↦ b * dct_char ξ x) x‖
        ≤ ‖dct_Lam ξ‖ * (‖b‖ * ‖dct_Lam ξ‖ ^ k) := by gcongr; exact ih x
      _ = ‖b‖ * ‖dct_Lam ξ‖ ^ (k + 1) := by ring

/-- A rapidly decaying trigonometric series is smooth. -/
theorem dct_series_contDiff {a : (ι → ℤ) → ℂ} (ha : ∀ m, ∃ C, ∀ ξ, ‖ξ‖ ^ m * ‖a ξ‖ ≤ C) :
    ContDiff ℝ ∞ fun x ↦ ∑' ξ, a ξ * dct_char ξ x := by
  refine contDiff_tsum (v := fun k ξ ↦ ‖a ξ‖ * (2 * Real.pi * Fintype.card ι * ‖ξ‖) ^ k)
    (fun ξ ↦ contDiff_const.mul (dct_contDiff_char ξ)) (fun k _ ↦ ?_) (fun k ξ x _ ↦ ?_)
  · have := dct_decay_mul_pow ha (2 * Real.pi * Fintype.card ι) (by positivity) k
    simpa [mul_assoc] using this
  · refine (dct_norm_iteratedFDeriv_term (a ξ) ξ k x).trans ?_
    gcongr
    exact dct_norm_Lam_le ξ


/-- A rapidly decaying trigonometric series is differentiated termwise. -/
theorem dct_series_hasSum_fderiv {a : (ι → ℤ) → ℂ}
    (ha : ∀ m, ∃ C, ∀ ξ, ‖ξ‖ ^ m * ‖a ξ‖ ≤ C) (x v : ι → ℝ) :
    HasSum (fun ξ ↦ a ξ * dct_Lam ξ v * dct_char ξ x)
      (fderiv ℝ (fun y ↦ ∑' ξ, a ξ * dct_char ξ y) x v) := by
  have hu := dct_decay_mul_pow ha (2 * Real.pi * Fintype.card ι) (by positivity) 1
  have hbd : ∀ ξ y, ‖(a ξ * dct_char ξ y) • dct_Lam ξ‖ ≤
      ‖a ξ‖ * (2 * Real.pi * Fintype.card ι * ‖ξ‖) ^ 1 := by
    intro ξ y
    rw [norm_smul, norm_mul, dct_norm_char, mul_one, pow_one, mul_assoc]
    gcongr
    simpa [mul_assoc] using dct_norm_Lam_le ξ
  have hu' : Summable fun ξ ↦ ‖a ξ‖ * (2 * Real.pi * Fintype.card ι * ‖ξ‖) ^ 1 := by
    simpa [mul_assoc] using hu
  have h0 : Summable fun ξ ↦ a ξ * dct_char ξ 0 := by
    refine Summable.of_norm_bounded (dct_decay_mul_pow ha 1 zero_le_one 0) fun ξ ↦ ?_
    simp [dct_norm_char]
  have hd := hasFDerivAt_tsum hu' (fun ξ y ↦ (dct_hasFDerivAt_char ξ y).const_mul (a ξ))
    (fun ξ y ↦ by rw [smul_smul]; exact hbd ξ y) h0 x
  rw [hd.fderiv]
  have hs : Summable fun ξ ↦ a ξ • dct_char ξ x • dct_Lam ξ :=
    Summable.of_norm_bounded hu' fun ξ ↦ by rw [smul_smul]; exact hbd ξ x
  have e := (ContinuousLinearMap.apply ℝ ℂ v).map_tsum hs
  simp only [ContinuousLinearMap.apply_apply] at e
  rw [e]
  refine (hs.mapL (ContinuousLinearMap.apply ℝ ℂ v)).hasSum.congr_fun fun ξ ↦ ?_
  simp only [ContinuousLinearMap.apply_apply, smul_apply, smul_eq_mul]
  ring

theorem dct_char_periodic (ξ : ι → ℤ) (k : ι → ℤ) (x : ι → ℝ) :
    dct_char ξ (x + fun i ↦ (k i : ℝ)) = dct_char ξ x := by
  rw [dct_char_add]
  have : dct_char ξ (fun i ↦ (k i : ℝ)) = 1 := by
    rw [dct_char]
    have h : (2 * Real.pi * Complex.I * ∑ i, (ξ i : ℂ) * (((k i : ℝ)) : ℂ)) =
        ((∑ i, ξ i * k i : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  rw [this, mul_one]

theorem dct_series_periodic (a : (ι → ℤ) → ℂ) :
    dct_Periodic fun x ↦ ∑' ξ, a ξ * dct_char ξ x := by
  intro k x
  simp only [dct_char_periodic]

/-- Fourier inversion for a continuous periodic function with summable coefficients. -/
theorem dct_hasSum_coeff {F : (ι → ℝ) → ℂ} (hF : dct_Periodic F) (hc : Continuous F)
    (hs : Summable (dct_coeff F)) (x : ι → ℝ) :
    HasSum (fun ξ ↦ dct_coeff F ξ * dct_char ξ x) (F x) := by
  let f : C(UnitAddTorus ι, ℂ) := ⟨dct_desc F, dct_continuous_desc hF hc⟩
  have hcoef : ∀ ξ, mFourierCoeff f ξ = dct_coeff F ξ := fun ξ ↦
    dct_coeff_eq_mFourierCoeff hF ξ 0
  have hs' : Summable (mFourierCoeff f) := by
    exact hs.congr fun ξ ↦ (hcoef ξ).symm
  have := hasSum_mFourier_series_apply_of_summable hs' (dct_proj x)
  simp only [hcoef, dct_mFourier_proj, smul_eq_mul] at this
  convert this using 1
  exact (dct_desc_proj hF x).symm

theorem dct_integrableOn {G : (ι → ℝ) → ℂ} (hG : dct_Periodic G) (hc : Continuous G)
    (ξ : ι → ℤ) : IntegrableOn (fun x ↦ dct_char (-ξ) x * G x) (dct_cube 0) := by
  have hfin : volume (dct_cube (0 : ι → ℝ)) < ⊤ := by
    rw [dct_volume_cube]; exact ENNReal.one_lt_top
  have : IsFiniteMeasure (volume.restrict (dct_cube (0 : ι → ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨B, hB⟩ := dct_exists_bound hG hc
  refine Integrable.of_bound ?_ B (Eventually.of_forall fun x ↦ ?_)
  · exact ((dct_contDiff_char (-ξ)).continuous.mul hc).aestronglyMeasurable
  · rw [norm_mul, dct_norm_char, one_mul]; exact hB x

/-- The constant-coefficient operator `G ↦ (DG(u) + i DG(u'))/2`. -/
def dct_P (u u' : ι → ℝ) (G : (ι → ℝ) → ℂ) (x : ι → ℝ) : ℂ :=
  (fderiv ℝ G x u + Complex.I * fderiv ℝ G x u') / 2

/-- The symbol of `dct_P u u'`. -/
def dct_sym (u u' : ι → ℝ) (ξ : ι → ℤ) : ℂ := (dct_Lam ξ u + Complex.I * dct_Lam ξ u') / 2

theorem dct_coeff_P {G : (ι → ℝ) → ℂ} (hG : dct_Periodic G) (hc : ContDiff ℝ ∞ G)
    (u u' : ι → ℝ) (ξ : ι → ℤ) :
    dct_coeff (dct_P u u' G) ξ = dct_sym u u' ξ * dct_coeff G ξ := by
  have h1 := dct_integrableOn (dct_periodic_fderiv hG u)
    ((hc.continuous_fderiv (by simp)).clm_apply continuous_const) ξ
  have h2 := dct_integrableOn (dct_periodic_fderiv hG u')
    ((hc.continuous_fderiv (by simp)).clm_apply continuous_const) ξ
  have hu := dct_coeff_fderiv hG (hc.of_le (by simp)) u ξ
  have hu' := dct_coeff_fderiv hG (hc.of_le (by simp)) u' ξ
  rw [← dct_Lam_apply] at hu hu'
  have : dct_coeff (dct_P u u' G) ξ =
      (dct_coeff (fun x ↦ fderiv ℝ G x u) ξ + Complex.I * dct_coeff (fun x ↦ fderiv ℝ G x u') ξ)
        / 2 := by
    simp only [dct_coeff, dct_P]
    rw [← integral_const_mul, ← integral_add h1 (h2.const_mul _), ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    ring
  rw [this, hu, hu', dct_sym]
  ring

theorem dct_series_hasSum_P {a : (ι → ℤ) → ℂ}
    (ha : ∀ m, ∃ C, ∀ ξ, ‖ξ‖ ^ m * ‖a ξ‖ ≤ C) (u u' x : ι → ℝ) :
    HasSum (fun ξ ↦ a ξ * dct_sym u u' ξ * dct_char ξ x)
      (dct_P u u' (fun y ↦ ∑' ξ, a ξ * dct_char ξ y) x) := by
  have h := ((dct_series_hasSum_fderiv ha x u).add
    ((dct_series_hasSum_fderiv ha x u').mul_left Complex.I)).div_const 2
  refine h.congr_fun fun ξ ↦ ?_
  simp only [dct_sym]
  ring


/-! ### Solving the system coefficientwise -/

theorem dct_sym_eq (u u' : ι → ℝ) (ξ : ι → ℤ) :
    dct_sym u u' ξ = ((-(Real.pi * ∑ i, (ξ i : ℝ) * u' i) : ℝ) : ℂ) +
      ((Real.pi * ∑ i, (ξ i : ℝ) * u i : ℝ) : ℂ) * Complex.I := by
  simp only [dct_sym, dct_Lam_apply]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem dct_norm_sym_sq (u u' : ι → ℝ) (ξ : ι → ℤ) :
    ‖dct_sym u u' ξ‖ ^ 2 =
      Real.pi ^ 2 * ((∑ i, (ξ i : ℝ) * u i) ^ 2 + (∑ i, (ξ i : ℝ) * u' i) ^ 2) := by
  rw [dct_sym_eq, Complex.sq_norm, Complex.normSq_add_mul_I]
  ring

theorem dct_norm_sym_le (u u' : ι → ℝ) (ξ : ι → ℤ) :
    ‖dct_sym u u' ξ‖ ≤ Real.pi * Fintype.card ι * (‖u‖ + ‖u'‖) * ‖ξ‖ := by
  have h1 : ∀ v, ‖dct_Lam ξ v‖ ≤ 2 * Real.pi * Fintype.card ι * ‖ξ‖ * ‖v‖ := fun v ↦
    ((dct_Lam ξ).le_opNorm v).trans (by gcongr; exact dct_norm_Lam_le ξ)
  rw [dct_sym, norm_div, Complex.norm_two]
  have h2 := norm_add_le (dct_Lam ξ u) (Complex.I * dct_Lam ξ u')
  rw [norm_mul, Complex.norm_I, one_mul] at h2
  have := h1 u
  have := h1 u'
  rw [div_le_iff₀ two_pos]
  nlinarith

theorem dct_sym_lower {n : ℕ} (u u' : Fin n → ι → ℝ)
    (hu : ∀ ξ : ι → ℝ, (∀ j, ∑ i, ξ i * u j i = 0 ∧ ∑ i, ξ i * u' j i = 0) → ξ = 0) :
    ∃ c0 > 0, ∀ ξ : ι → ℤ, ξ ≠ 0 → c0 ≤ ∑ k, ‖dct_sym (u k) (u' k) ξ‖ ^ 2 := by
  let M : (ι → ℝ) →ₗ[ℝ] (Fin n → ℝ × ℝ) :=
    { toFun := fun ξ j ↦ (∑ i, ξ i * u j i, ∑ i, ξ i * u' j i)
      map_add' := by
        intro x y; funext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x; funext j; simp [Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker M = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun ξ h ↦ hu ξ fun j ↦ ?_
    have := congrFun h j
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  obtain ⟨K, hK0, hK⟩ := M.exists_antilipschitzWith hker
  refine ⟨Real.pi ^ 2 / (K : ℝ) ^ 2, by positivity, fun ξ hξ ↦ ?_⟩
  set ξr : ι → ℝ := fun i ↦ (ξ i : ℝ)
  set T := ∑ k, ((∑ i, ξr i * u k i) ^ 2 + (∑ i, ξr i * u' k i) ^ 2) with hT
  have hS : ∑ k, ‖dct_sym (u k) (u' k) ξ‖ ^ 2 = Real.pi ^ 2 * T := by
    simp only [dct_norm_sym_sq, hT, Finset.mul_sum, ξr]
  have h1 : 1 ≤ ‖ξr‖ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hξ
    have : (1 : ℝ) ≤ |(ξ i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
    exact this.trans (by simpa [ξr] using norm_le_pi_norm ξr i)
  have h2 : ‖ξr‖ ≤ K * ‖M ξr‖ := by
    simpa [dist_zero_right] using hK.le_mul_dist ξr 0
  have h3 : ‖M ξr‖ ≤ Real.sqrt T := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j ↦ ?_
    have hj : (∑ i, ξr i * u j i) ^ 2 + (∑ i, ξr i * u' j i) ^ 2 ≤ T :=
      Finset.single_le_sum (f := fun k ↦ (∑ i, ξr i * u k i) ^ 2 + (∑ i, ξr i * u' k i) ^ 2)
        (fun k _ ↦ by positivity) (Finset.mem_univ j)
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩ <;>
      refine (Real.norm_eq_abs _).trans_le (Real.abs_le_sqrt ?_) <;>
      simp only [M, LinearMap.coe_mk, AddHom.coe_mk] <;> nlinarith [sq_nonneg (∑ i, ξr i * u j i),
        sq_nonneg (∑ i, ξr i * u' j i)]
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have h4 : 1 ≤ K * Real.sqrt T := h1.trans (h2.trans (by gcongr))
  have h5 : 1 ≤ (K : ℝ) ^ 2 * T := by
    have hT0 : 0 ≤ T := by positivity
    have := mul_self_le_mul_self zero_le_one h4
    rw [one_mul, mul_mul_mul_comm, Real.mul_self_sqrt hT0] at this
    nlinarith
  rw [hS, div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]


theorem dct_sym_zero (u u' : ι → ℝ) : dct_sym u u' 0 = 0 := by
  simp [dct_sym, dct_Lam_apply]

/-- The `∂̄`-type system `F_j = c_j + P_j ψ` on the torus, for a first-order system whose symbols
have no common real zero but `0`. -/
theorem dct_torus_solve {n : ℕ} (u u' : Fin n → ι → ℝ)
    (hu : ∀ ξ : ι → ℝ, (∀ j, ∑ i, ξ i * u j i = 0 ∧ ∑ i, ξ i * u' j i = 0) → ξ = 0)
    (F : Fin n → (ι → ℝ) → ℂ) (hF : ∀ j, ContDiff ℝ ∞ (F j)) (hper : ∀ j, dct_Periodic (F j))
    (hcompat : ∀ j k x, dct_P (u k) (u' k) (F j) x = dct_P (u j) (u' j) (F k) x) :
    ∃ (c : Fin n → ℂ) (ψ : (ι → ℝ) → ℂ), ContDiff ℝ ∞ ψ ∧ dct_Periodic ψ ∧
      ∀ j x, F j x = c j + dct_P (u j) (u' j) ψ x := by
  set σ : Fin n → (ι → ℤ) → ℂ := fun j ξ ↦ dct_sym (u j) (u' j) ξ with hσ
  set W : Fin n → (ι → ℤ) → ℂ := fun j ξ ↦ dct_coeff (F j) ξ with hW
  have hrel : ∀ j k ξ, σ k ξ * W j ξ = σ j ξ * W k ξ := by
    intro j k ξ
    have := congrArg (fun G ↦ dct_coeff G ξ) (funext (hcompat j k))
    rwa [dct_coeff_P (hper j) (hF j), dct_coeff_P (hper k) (hF k)] at this
  set S : (ι → ℤ) → ℝ := fun ξ ↦ ∑ k, ‖σ k ξ‖ ^ 2 with hS
  set a : (ι → ℤ) → ℂ := fun ξ ↦ (∑ k, (starRingEnd ℂ) (σ k ξ) * W k ξ) / (S ξ : ℂ) with ha
  obtain ⟨c0, hc0, hlow⟩ := dct_sym_lower u u' hu
  have haσ : ∀ j ξ, a ξ * σ j ξ = if ξ = 0 then 0 else W j ξ := by
    intro j ξ
    split_ifs with hξ
    · subst hξ; simp [hσ, dct_sym_zero]
    · have hSpos : 0 < S ξ := hc0.trans_le (hlow ξ hξ)
      have hSne : (S ξ : ℂ) ≠ 0 := by exact_mod_cast hSpos.ne'
      simp only [ha]
      rw [div_mul_eq_mul_div, div_eq_iff hSne, Finset.sum_mul]
      have : ∀ k ∈ (Finset.univ : Finset (Fin n)),
          (starRingEnd ℂ) (σ k ξ) * W k ξ * σ j ξ = W j ξ * ((‖σ k ξ‖ ^ 2 : ℝ) : ℂ) := by
        intro k _
        rw [mul_assoc, mul_comm (W k ξ), ← hrel j k ξ, ← mul_assoc, Complex.conj_mul']
        push_cast
        ring
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
      simp [hS]
  -- decay of the solution's coefficients
  have hWdec : ∀ j m, ∃ C, ∀ ξ, ‖ξ‖ ^ m * ‖W j ξ‖ ≤ C := fun j m ↦
    dct_coeff_decay (hper j) (hF j) m
  set Kσ : ℝ := ∑ k, Real.pi * Fintype.card ι * (‖u k‖ + ‖u' k‖) with hKσ
  have hσle : ∀ k ξ, ‖σ k ξ‖ ≤ Kσ * ‖ξ‖ := by
    intro k ξ
    refine (dct_norm_sym_le (u k) (u' k) ξ).trans ?_
    gcongr
    exact Finset.single_le_sum (f := fun k ↦ Real.pi * Fintype.card ι * (‖u k‖ + ‖u' k‖))
      (fun k _ ↦ by positivity) (Finset.mem_univ k)
  have hKσ0 : 0 ≤ Kσ := Finset.sum_nonneg fun k _ ↦ by positivity
  have hadec : ∀ m, ∃ C, ∀ ξ, ‖ξ‖ ^ m * ‖a ξ‖ ≤ C := by
    intro m
    choose C hC using fun j ↦ hWdec j (m + 1)
    refine ⟨Kσ / c0 * ∑ k, C k + ‖a 0‖, fun ξ ↦ ?_⟩
    have hC0 : ∀ k, 0 ≤ C k := fun k ↦ (by positivity : (0 : ℝ) ≤ ‖(0 : ι → ℤ)‖ ^ (m + 1) *
      ‖W k 0‖).trans (hC k 0)
    have hsumC : 0 ≤ Kσ / c0 * ∑ k, C k := by
      have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) ↦ hC0 k
      positivity
    by_cases hξ : ξ = 0
    · subst hξ
      rcases m with _ | m
      · simp only [pow_zero, one_mul]; linarith
      · simp only [norm_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          not_false_eq_true, zero_pow, zero_mul]
        positivity
    · have hSpos : c0 ≤ S ξ := hlow ξ hξ
      have hSpos' : 0 < S ξ := hc0.trans_le hSpos
      have h1 : ‖a ξ‖ ≤ (∑ k, Kσ * ‖ξ‖ * ‖W k ξ‖) / c0 := by
        simp only [ha, norm_div, Complex.norm_real, Real.norm_of_nonneg hSpos'.le]
        rw [div_le_div_iff₀ hSpos' hc0]
        have h2 : ‖∑ k, (starRingEnd ℂ) (σ k ξ) * W k ξ‖ ≤ ∑ k, Kσ * ‖ξ‖ * ‖W k ξ‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
          rw [norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_right (hσle k ξ) (norm_nonneg _)
        have h3 : 0 ≤ ∑ k, Kσ * ‖ξ‖ * ‖W k ξ‖ := Finset.sum_nonneg fun k _ ↦ by positivity
        calc ‖∑ k, (starRingEnd ℂ) (σ k ξ) * W k ξ‖ * c0
            ≤ (∑ k, Kσ * ‖ξ‖ * ‖W k ξ‖) * c0 := by gcongr
          _ ≤ (∑ k, Kσ * ‖ξ‖ * ‖W k ξ‖) * S ξ := by gcongr
      have h4 : ‖ξ‖ ^ m * ‖a ξ‖ ≤ Kσ / c0 * ∑ k, ‖ξ‖ ^ (m + 1) * ‖W k ξ‖ := by
        calc ‖ξ‖ ^ m * ‖a ξ‖ ≤ ‖ξ‖ ^ m * ((∑ k, Kσ * ‖ξ‖ * ‖W k ξ‖) / c0) := by gcongr
          _ = Kσ / c0 * ∑ k, ‖ξ‖ ^ (m + 1) * ‖W k ξ‖ := by
            simp only [Finset.sum_div, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [pow_succ]
            ring
      refine h4.trans ?_
      have h5 : ∑ k, ‖ξ‖ ^ (m + 1) * ‖W k ξ‖ ≤ ∑ k, C k :=
        Finset.sum_le_sum fun k _ ↦ hC k ξ
      have : Kσ / c0 * ∑ k, ‖ξ‖ ^ (m + 1) * ‖W k ξ‖ ≤ Kσ / c0 * ∑ k, C k := by gcongr
      linarith [norm_nonneg (a 0)]
  refine ⟨fun j ↦ W j 0, fun x ↦ ∑' ξ, a ξ * dct_char ξ x, dct_series_contDiff hadec,
    dct_series_periodic a, fun j x ↦ ?_⟩
  obtain ⟨C, hC⟩ := hWdec j (Fintype.card ι + 1)
  have hWs : Summable (W j) := dct_summable_of_decay hC
  have h1 := dct_hasSum_coeff (hper j) (hF j).continuous hWs x
  have h2 := dct_series_hasSum_P hadec (u j) (u' j) x
  have h3 := h1.sub h2
  have h4 : HasSum (fun ξ : ι → ℤ ↦ if ξ = 0 then W j 0 else 0) (W j 0) := hasSum_ite_eq (0 : ι → ℤ) (W j 0)
  have h5 : (fun ξ ↦ dct_coeff (F j) ξ * dct_char ξ x - a ξ * dct_sym (u j) (u' j) ξ *
      dct_char ξ x) = fun ξ : ι → ℤ ↦ if ξ = 0 then W j 0 else 0 := by
    funext ξ
    have := haσ j ξ
    simp only [hσ] at this
    rw [this]
    split_ifs with hξ
    · subst hξ; simp [dct_char, hW]
    · simp [hW]
  rw [h5] at h3
  have := h3.unique h4
  simp only at this ⊢
  linear_combination this

end HodgeLean.Foundations

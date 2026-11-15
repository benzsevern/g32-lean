import HodgeLean.Adapters.ThetaExistenceDefs

/-! # Proof obligations for the theta-existence specification -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open scoped Manifold CategoryTheory.MonObj

namespace HodgeLean.Adapters

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- A Hermitian form as a continuous real-bilinear map (finite dimension makes it continuous).

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 (a Hermitian form is
real bilinear); continuity of linear maps on finite-dimensional spaces. -/
def hermitianCLM (H : HermitianForm (V := V)) : V →L[ℝ] V →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ LinearMap.toContinuousLinearMap
        { toFun := H.toFun x
          map_add' := H.add_right x
          map_smul' := fun r y ↦ hermitian_real_smul_right H r x y }
      map_add' := fun x y ↦ by ext z; simp [H.add_left]
      map_smul' := fun r x ↦ by ext z; simp [hermitian_real_smul_left] }

theorem hermitianCLM_apply (H : HermitianForm (V := V)) (x y : V) :
    hermitianCLM H x y = H.toFun x y := rfl

example (H : HermitianForm (V := V)) (x y : V) : hermitianCLM H x y = H.toFun x y := rfl

theorem hermitian_norm_le (H : HermitianForm (V := V)) (x y : V) :
    ‖H.toFun x y‖ ≤ ‖hermitianCLM H‖ * ‖x‖ * ‖y‖ := by
  rw [← hermitianCLM_apply]
  exact (hermitianCLM H).le_opNorm₂ x y

theorem exists_hermitian_re_lower (H : HermitianForm (V := V)) (hH : H.IsPositiveDefinite) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : V, c * ‖x‖ ^ 2 ≤ (H.toFun x x).re := by
  have hcont : Continuous fun x : V ↦ (H.toFun x x).re :=
    Complex.continuous_re.comp ((hermitianCLM H).continuous₂.comp
      (continuous_id.prodMk continuous_id))
  have hhom : ∀ (r : ℝ) (x : V), (H.toFun (r • x) (r • x)).re = r ^ 2 * (H.toFun x x).re := by
    intro r x
    rw [hermitian_real_smul_left, hermitian_real_smul_right, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul, sq]
  rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun x ↦ ?_⟩
    by_cases hx : x = 0
    · simp [hx, hermitian_zero_left]
    · have : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
        simp [norm_smul, hx]
      simp [he] at this
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hne hcont.continuousOn
    have hu0 : u ≠ 0 := by
      rintro rfl; simp at hu
    refine ⟨(H.toFun u u).re, hH u hu0, fun x ↦ ?_⟩
    by_cases hx : x = 0
    · simp [hx, hermitian_zero_left]
    · have hxs : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
        simp [norm_smul, hx]
      have h1 := hmin hxs
      simp only [Set.mem_ofPred_eq, hhom] at h1
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have : ‖x‖ ^ 2 * (‖x‖⁻¹ ^ 2 * (H.toFun x x).re) = (H.toFun x x).re := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖x‖)]

theorem exp_le_rpow (a b : ℝ) (ha : 0 < a) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (b * t - a * t ^ 2) ≤
      (Real.exp (b ^ 2 / (2 * a)) * n.factorial / (a / 2) ^ n) * t ^ (-(2 * n : ℝ)) := by
  have h1 : b * t - a * t ^ 2 ≤ b ^ 2 / (2 * a) + -((a / 2) * t ^ 2) := by
    have : 0 ≤ (a * t - b) ^ 2 / (2 * a) := by positivity
    have e : (a * t - b) ^ 2 / (2 * a) = a / 2 * t ^ 2 - b * t + b ^ 2 / (2 * a) := by
      field_simp; ring
    linarith
  have h2 : ((a / 2) * t ^ 2) ^ n / n.factorial ≤ Real.exp ((a / 2) * t ^ 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have hpos : 0 < ((a / 2) * t ^ 2) ^ n := by positivity
  have h3 : Real.exp (-((a / 2) * t ^ 2)) ≤ n.factorial / ((a / 2) * t ^ 2) ^ n := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    exact h2
  have h4 : t ^ (-(2 * n : ℝ)) = ((t ^ 2) ^ n)⁻¹ := by
    rw [Real.rpow_neg ht.le, ← pow_mul, ← Real.rpow_natCast]
    push_cast; ring_nf
  calc Real.exp (b * t - a * t ^ 2) ≤ Real.exp (b ^ 2 / (2 * a) + -((a / 2) * t ^ 2)) :=
        Real.exp_le_exp.mpr h1
    _ = Real.exp (b ^ 2 / (2 * a)) * Real.exp (-((a / 2) * t ^ 2)) := Real.exp_add _ _
    _ ≤ Real.exp (b ^ 2 / (2 * a)) * (n.factorial / ((a / 2) * t ^ 2) ^ n) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = _ := by rw [h4, mul_pow]; field_simp

theorem summable_exp_lattice (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (a b : ℝ) (ha : 0 < a) :
    Summable fun l : L ↦ Real.exp (b * ‖l‖ - a * ‖l‖ ^ 2) := by
  set n := Module.finrank ℤ L + 1
  have hs : Summable fun l : L ↦ ‖l‖ ^ (-(2 * n : ℝ)) :=
    ZLattice.summable_norm_rpow L _ (by simp only [n]; push_cast; linarith)
  refine Summable.of_norm_bounded_eventually (hs.mul_left
    (Real.exp (b ^ 2 / (2 * a)) * n.factorial / (a / 2) ^ n)) ?_
  have : {l : L | l ≠ 0} ∈ Filter.cofinite := by
    simp [Filter.mem_cofinite]
  filter_upwards [this] with l hl
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_le_rpow a b ha n (norm_pos_iff.mpr hl)

omit [FiniteDimensional ℂ V] in
theorem norm_inv_holFactor (D : Datum (V := V)) (l : D.lattice) (v : V) :
    ‖(holFactor D l v)⁻¹‖ =
      Real.exp (-(Real.pi * (D.hermitian.toFun l v).re +
        Real.pi / 2 * (D.hermitian.toFun l l).re)) := by
  rw [holFactor, norm_inv, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp, ← Real.exp_neg]
  simp

theorem norm_inv_holFactor_le (D : Datum (V := V)) {c : ℝ}
    (hc : ∀ x : V, c * ‖x‖ ^ 2 ≤ (D.hermitian.toFun x x).re) (l : D.lattice) (v : V) :
    ‖(holFactor D l v)⁻¹‖ ≤ Real.exp ((Real.pi * ‖hermitianCLM D.hermitian‖ * ‖v‖) * ‖l‖ -
        (Real.pi / 2 * c) * ‖l‖ ^ 2) := by
  rw [norm_inv_holFactor]
  refine Real.exp_le_exp.mpr ?_
  have h1 := hermitian_norm_le D.hermitian l v
  have h2 := (Complex.abs_re_le_norm (D.hermitian.toFun l v)).trans h1
  have h3 := hc l
  rw [Submodule.norm_coe] at *
  have := neg_abs_le (D.hermitian.toFun l v).re
  nlinarith [Real.pi_pos]

theorem spec_summable_inv_holFactor_aux (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) (v : V) :
    Summable (fun l : D.lattice ↦ (holFactor D l v)⁻¹) := by
  obtain ⟨c, hc, hle⟩ := exists_hermitian_re_lower D.hermitian hH
  exact Summable.of_norm_bounded (summable_exp_lattice D.lattice _ _ (by positivity))
    (norm_inv_holFactor_le D hle · v)

theorem spec_poincareTheta_add_aux (D : Datum (V := V)) (l : D.lattice) (v : V) :
    poincareTheta D (v + l) = holFactor D l v * poincareTheta D v := by
  have h : ∀ k : D.lattice,
      (holFactor D k (v + l))⁻¹ = holFactor D l v * (holFactor D (k + l) v)⁻¹ := by
    intro k
    have := holFactor_ne_zero D l v
    rw [spec_holFactor_cocycle]; field_simp
  unfold poincareTheta
  simp_rw [h]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight l).tsum_eq (fun k => (holFactor D k v)⁻¹)

/-- `H(l, ·)` as a continuous complex-linear functional.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 (`H` is complex
linear in the argument where this repository puts it second). -/
def hermitianRight (H : HermitianForm (V := V)) (l : V) : V →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := H.toFun l
      map_add' := H.add_right l
      map_smul' := fun c y ↦ H.smul_right c l y }

theorem hermitianRight_apply (H : HermitianForm (V := V)) (l x : V) :
    hermitianRight H l x = H.toFun l x := rfl

example (H : HermitianForm (V := V)) (l x : V) : hermitianRight H l x = H.toFun l x := rfl

theorem norm_hermitianRight_le (H : HermitianForm (V := V)) (l : V) :
    ‖hermitianRight H l‖ ≤ ‖hermitianCLM H‖ * ‖l‖ :=
  (hermitianRight H l).opNorm_le_bound (by positivity) (hermitian_norm_le H l)

theorem hasFDerivAt_inv_holFactor (D : Datum (V := V)) (l : D.lattice) (v : V) :
    HasFDerivAt (fun x ↦ (holFactor D l x)⁻¹)
      ((holFactor D l v)⁻¹ • (-(Real.pi : ℂ) • hermitianRight D.hermitian l)) v := by
  have e : ∀ x, (holFactor D l x)⁻¹ = (D.semicharacter l : ℂ)⁻¹ *
      Complex.exp (-((Real.pi : ℂ) • hermitianRight D.hermitian l x +
        (Real.pi / 2) * D.hermitian.toFun l l)) := by
    intro x
    simp only [holFactor, mul_inv, Complex.exp_neg, hermitianRight_apply, smul_eq_mul]
  have h := ((((hermitianRight D.hermitian l).hasFDerivAt (x := v)).const_smul
    (Real.pi : ℂ)).add_const ((Real.pi / 2) * D.hermitian.toFun l l)).neg.cexp.const_mul
    ((D.semicharacter l : ℂ)⁻¹)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ e x)).congr_fderiv ?_
  ext
  simp only [smul_apply, neg_apply, smul_eq_mul, e v,
    Pi.neg_apply, Pi.smul_apply]
  ring

theorem spec_differentiable_poincareTheta_aux (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) :
    Differentiable ℂ (poincareTheta D) := by
  obtain ⟨c, hc, hle⟩ := exists_hermitian_re_lower D.hermitian hH
  set K := ‖hermitianCLM D.hermitian‖
  intro v₀
  set B := Real.pi * K * (‖v₀‖ + 1)
  have hu : Summable fun l : D.lattice ↦
      Real.pi * K * Real.exp ((B + 1) * ‖l‖ - (Real.pi / 2 * c) * ‖l‖ ^ 2) :=
    (summable_exp_lattice D.lattice _ _ (by positivity)).mul_left _
  have hbd : ∀ (l : D.lattice) x, x ∈ Metric.ball v₀ 1 →
      ‖(holFactor D l x)⁻¹ • (-(Real.pi : ℂ) • hermitianRight D.hermitian l)‖ ≤
        Real.pi * K * Real.exp ((B + 1) * ‖l‖ - (Real.pi / 2 * c) * ‖l‖ ^ 2) := by
    intro l x hx
    have hx' : ‖x‖ ≤ ‖v₀‖ + 1 := by
      have := mem_ball_iff_norm.mp hx
      have := norm_le_norm_add_norm_sub' x v₀
      linarith
    have h1 := norm_inv_holFactor_le D hle l x
    have h2 : Real.exp ((Real.pi * K * ‖x‖) * ‖l‖ - (Real.pi / 2 * c) * ‖l‖ ^ 2) ≤
        Real.exp (B * ‖l‖ - (Real.pi / 2 * c) * ‖l‖ ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      have : Real.pi * K * ‖x‖ ≤ B :=
        mul_le_mul_of_nonneg_left hx' (by positivity)
      nlinarith [norm_nonneg l]
    have h3 := norm_hermitianRight_le D.hermitian (l : V)
    have h4 : ‖(l : V)‖ * Real.exp (B * ‖l‖ - (Real.pi / 2 * c) * ‖l‖ ^ 2) ≤
        Real.exp ((B + 1) * ‖l‖ - (Real.pi / 2 * c) * ‖l‖ ^ 2) := by
      have : (B + 1) * ‖l‖ - (Real.pi / 2 * c) * ‖l‖ ^ 2 =
          ‖l‖ + (B * ‖l‖ - (Real.pi / 2 * c) * ‖l‖ ^ 2) := by ring
      rw [this, Real.exp_add]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have := Real.add_one_le_exp ‖l‖
      rw [Submodule.norm_coe]
      linarith
    rw [norm_smul, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    calc ‖(holFactor D l x)⁻¹‖ * (Real.pi * ‖hermitianRight D.hermitian l‖)
        ≤ Real.exp (B * ‖l‖ - (Real.pi / 2 * c) * ‖l‖ ^ 2) * (Real.pi * (K * ‖(l : V)‖)) := by
          gcongr
          exact h1.trans h2
      _ = Real.pi * K * (‖(l : V)‖ * Real.exp (B * ‖l‖ - (Real.pi / 2 * c) * ‖l‖ ^ 2)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  exact (hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball v₀ 1).isPreconnected
    (fun l x _ ↦ hasFDerivAt_inv_holFactor D l x) hbd (Metric.mem_ball_self one_pos)
    (spec_summable_inv_holFactor_aux D hH v₀) (Metric.mem_ball_self one_pos)).differentiableAt

theorem spec_poincareTheta_mem_sections_aux (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) :
    poincareTheta D ∈ sections D :=
  ⟨spec_differentiable_poincareTheta_aux D hH, spec_poincareTheta_add_aux D⟩

omit [FiniteDimensional ℂ V] in
/-- The imaginary part of a Hermitian form is additive in its first argument. -/
theorem imaginary_add_left (H : HermitianForm (V := V)) (x y w : V) :
    H.imaginary (x + y) w = H.imaginary x w + H.imaginary y w := by
  simp only [HermitianForm.imaginary, H.add_left, Complex.add_im]

omit [FiniteDimensional ℂ V] in
/-- The imaginary part of a Hermitian form is additive in its second argument. -/
theorem imaginary_add_right (H : HermitianForm (V := V)) (x y w : V) :
    H.imaginary w (x + y) = H.imaginary w x + H.imaginary w y := by
  simp only [HermitianForm.imaginary, H.add_right, Complex.add_im]

omit [FiniteDimensional ℂ V] in
/-- The imaginary part of a Hermitian form is real-homogeneous in its first argument. -/
theorem imaginary_smul_left (H : HermitianForm (V := V)) (r : ℝ) (x w : V) :
    H.imaginary (r • x) w = r * H.imaginary x w := by
  rw [HermitianForm.imaginary, HermitianForm.imaginary, ← Complex.coe_smul, H.smul_left,
    Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul]

omit [FiniteDimensional ℂ V] in
/-- The imaginary part of a Hermitian form is real-homogeneous in its second argument. -/
theorem imaginary_smul_right (H : HermitianForm (V := V)) (r : ℝ) (x w : V) :
    H.imaginary w (r • x) = r * H.imaginary w x := by
  rw [HermitianForm.imaginary, HermitianForm.imaginary, ← Complex.coe_smul, H.smul_right,
    Complex.im_ofReal_mul]

omit [FiniteDimensional ℂ V] in
/-- The imaginary part of a Hermitian form is alternating. -/
theorem imaginary_antisymm (H : HermitianForm (V := V)) (x w : V) :
    H.imaginary x w = -H.imaginary w x := by
  rw [HermitianForm.imaginary, HermitianForm.imaginary, ← H.conj_symm, Complex.star_def,
    Complex.conj_im]

/-- `∫₀¹ e^{2πi n x} dx` is `1` for `n = 0` and `0` otherwise. -/
theorem integral_Ioc_exp_two_pi_int (n : ℤ) :
    ∫ x in Set.Ioc (0 : ℝ) 1, Complex.exp (((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I) =
      if n = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hn
  · subst hn
    simp
  · have hc : 2 * (Real.pi : ℂ) * Complex.I * n ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hn]
    have e : ∀ x : ℝ, Complex.exp (((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((2 * Real.pi * Complex.I * n) * x) := by
      intro x
      push_cast
      ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one,
        show 2 * (Real.pi : ℂ) * Complex.I * n = n * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h1]
    simp

open MeasureTheory in
/-- An absolutely summable Fourier series on `(ℝ/ℤ)^ι` that vanishes identically has zero
constant term: integrate termwise over `[0,1]^ι`. -/
theorem fourier_const_eq_zero {ιd κ : Type*} [Fintype ιd] [Countable κ] (n : κ → ιd → ℤ) (k0 : κ)
    (hn : ∀ k, (∀ j, n k j = 0) ↔ k = k0) (c : κ → ℂ) (hc : Summable c)
    (h : ∀ t : ιd → ℝ, ∑' k, c k *
      ∏ j, Complex.exp (((2 * Real.pi * n k j * t j : ℝ) : ℂ) * Complex.I) = 0) :
    c k0 = 0 := by
  classical
  let mu : Measure (ιd → ℝ) := Measure.pi fun _ ↦ volume.restrict (Set.Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  let F : κ → (ιd → ℝ) → ℂ := fun k t ↦
    c k * ∏ j, Complex.exp (((2 * Real.pi * n k j * t j : ℝ) : ℂ) * Complex.I)
  have hnorm : ∀ k t, ‖F k t‖ = ‖c k‖ := by
    intro k t
    simp only [F, norm_mul, norm_prod, Complex.norm_exp_ofReal_mul_I, Finset.prod_const_one,
      mul_one]
  have hcont : ∀ k, Continuous (F k) := fun k ↦ by fun_prop
  have hint : ∀ k, Integrable (F k) mu := fun k ↦
    (integrable_const ‖c k‖).mono' (hcont k).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t ↦ (hnorm k t).le)
  have hsum : Summable fun k ↦ ∫ t, ‖F k t‖ ∂mu := by
    simp_rw [hnorm, integral_const, smul_eq_mul]
    exact hc.norm.mul_left _
  have hval : ∀ k, ∫ t, F k t ∂mu = if k = k0 then c k0 else 0 := by
    intro k
    simp only [F, mu]
    rw [integral_const_mul, integral_fintype_prod_eq_prod
      (fun j x ↦ Complex.exp (((2 * Real.pi * n k j * x : ℝ) : ℂ) * Complex.I))]
    simp_rw [integral_Ioc_exp_two_pi_int, Finset.prod_boole]
    simp only [Finset.mem_univ, forall_const, hn k]
    split_ifs with hk <;> simp [hk]
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp only [hval, F, h, integral_zero] at key
  rw [tsum_ite_eq] at key
  exact key

theorem spec_exists_fourier_ne_zero_aux (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (H : HermitianForm (V := V)) (hE : IsNondegenerate H.imaginary)
    (c : L → ℂ) (hc : Summable c) (h0 : c 0 ≠ 0) :
    ∃ w : V, ∑' l : L, c l * (Circle.exp (2 * Real.pi * H.imaginary l w) : ℂ) ≠ 0 := by
  classical
  have := ZLattice.module_free ℝ L
  have := ZLattice.module_finite ℝ L
  let b := Module.Free.chooseBasis ℤ L
  let bR := b.ofZLatticeBasis ℝ L
  let ψ : V → V →ₗ[ℝ] ℝ := fun w ↦
    { toFun := fun v ↦ H.imaginary v w
      map_add' := fun x y ↦ imaginary_add_left H x y w
      map_smul' := fun r x ↦ imaginary_smul_left H r x w }
  let Φ : V →ₗ[ℝ] (Module.Free.ChooseBasisIndex ℤ L → ℝ) :=
    { toFun := fun w j ↦ H.imaginary (bR j) w
      map_add' := fun x y ↦ funext fun j ↦ imaginary_add_right H x y (bR j)
      map_smul' := fun r x ↦ funext fun j ↦ imaginary_smul_right H r x (bR j) }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hψ : ψ w = 0 := bR.ext fun j ↦ congrFun hw j
    refine hE w fun v ↦ ?_
    rw [imaginary_antisymm]
    have := LinearMap.congr_fun hψ v
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at this
    rw [this, neg_zero]
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis bR])).1 hinj
  have hexp : ∀ (l : L) (w : V),
      H.imaginary l w = ∑ j, (b.repr l j : ℝ) * Φ w j := by
    intro l w
    have hl : (l : V) = ∑ j, (b.repr l j : ℝ) • bR j := by
      conv_lhs => rw [← bR.sum_repr (l : V)]
      simp only [bR, Module.Basis.ofZLatticeBasis_repr_apply]
    have := congrArg (ψ w) hl
    simp only [map_sum, map_smul, smul_eq_mul] at this
    exact this
  by_contra hall
  push Not at hall
  refine h0 (fourier_const_eq_zero (fun l j ↦ b.repr l j) 0 ?_ c hc fun t ↦ ?_)
  · intro l
    rw [← b.repr.map_eq_zero_iff, Finsupp.ext_iff]
    rfl
  · obtain ⟨w, rfl⟩ := hsurj t
    rw [← hall w]
    refine tsum_congr fun l ↦ ?_
    rw [Circle.coe_exp, hexp, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul,
      Complex.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    congr 2
    push_cast
    ring

omit [FiniteDimensional ℂ V] in
/-- The imaginary part of a Hermitian form is odd in its second argument. -/
theorem imaginary_neg_right (H : HermitianForm (V := V)) (x y : V) :
    H.imaginary x (-y) = -H.imaginary x y := by
  have h := H.smul_right (-1) x y
  rw [neg_one_smul, neg_one_mul] at h
  rw [HermitianForm.imaginary, HermitianForm.imaginary, h, Complex.neg_im]

theorem spec_exists_twist_poincareTheta_ne_zero_aux (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) :
    ∃ w : V, poincareTheta (D.twist w) ≠ 0 := by
  have hE : IsNondegenerate D.hermitian.imaginary := by
    intro v hv
    by_contra hne
    have h := hv (Complex.I • v)
    rw [HermitianForm.imaginary, D.hermitian.smul_right, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_add] at h
    exact (hH v hne).ne' h
  have hc := spec_summable_inv_holFactor_aux D hH 0
  have h0 : (holFactor D 0 0)⁻¹ ≠ 0 := by
    rw [spec_holFactor_zero, inv_one]; exact one_ne_zero
  obtain ⟨w, hw⟩ := spec_exists_fourier_ne_zero_aux D.lattice D.hermitian hE _ hc h0
  refine ⟨-w, fun hP ↦ hw ?_⟩
  have h := congrFun hP 0
  rw [Pi.zero_apply, poincareTheta] at h
  rw [← h]
  refine tsum_congr fun l ↦ ?_
  have him : D.hermitian.imaginary l (-w) = -D.hermitian.imaginary l w :=
    imaginary_neg_right _ _ _
  have e : holFactor (D.twist (-w)) l 0 =
      holFactor D l 0 * ((Circle.exp (2 * Real.pi * D.hermitian.imaginary l w))⁻¹ : Circle) := by
    simp only [holFactor, Datum.twist, Circle.coe_mul, him, mul_neg, Circle.exp_neg]
    ring
  rw [e, mul_inv, Circle.coe_inv, inv_inv]

omit [FiniteDimensional ℂ V] in
/-- Twisting by `w` and then by `-w` returns the datum. -/
theorem twist_twist_neg (D : Datum (V := V)) (w : V) : (D.twist w).twist (-w) = D := by
  cases D
  simp only [Datum.twist]
  congr 1
  funext l
  rw [imaginary_neg_right, mul_neg, Circle.exp_neg, mul_assoc, mul_inv_cancel, mul_one]

theorem spec_sections_ne_bot_aux (D : Datum (V := V)) (hH : D.hermitian.IsPositiveDefinite) :
    sections D ≠ ⊥ := by
  obtain ⟨w, hw⟩ := spec_exists_twist_poincareTheta_ne_zero_aux D hH
  have hmem := spec_poincareTheta_mem_sections_aux (D.twist w) hH
  have htr := spec_sections_translate (D.twist w) (-w) _ hmem
  rw [twist_twist_neg] at htr
  intro hbot
  have h := (Submodule.eq_bot_iff _).1 hbot _ htr
  apply hw
  funext u
  have hu := congrFun h (u + w)
  simp only [Pi.zero_apply, add_neg_cancel_right, mul_eq_zero, Complex.exp_ne_zero,
    false_or] at hu
  exact hu

end General

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

theorem spec_sectionsOnX_ne_bot_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (hH : H.IsPositiveDefinite) :
    sectionsOnX X (holFactor (datumOfX X H E hE χ hχ)) Set.univ ≠ ⊥ := by
  have hne := spec_sections_ne_bot_aux (datumOfX X H E hE χ hχ) hH
  rw [Ne, Submodule.eq_bot_iff, not_forall] at hne ⊢
  obtain ⟨θ, hθ⟩ := hne
  rw [Classical.not_imp] at hθ
  obtain ⟨⟨hdiff, hfe⟩, hθ0⟩ := hθ
  refine ⟨fun x ↦ θ x, ?_⟩
  rw [Classical.not_imp]
  refine ⟨⟨⟨θ, hdiff.differentiableOn, fun _ ↦ rfl⟩, fun l x ↦ hfe l x⟩, fun h ↦ hθ0 ?_⟩
  funext v
  exact congrFun h ⟨v, Set.mem_univ _⟩

end HodgeLean.Adapters

import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticDefs
import HodgeLean.Foundations.Program.HurwitzTransport
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.MetricSpace.Contracting

/-! # Regularity of nonvanishing continuous roots -/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

theorem b6a_one_sub_scaled_ne_zero (a δ : ℂ) (r : ℝ) (hr : 0 < r)
    (ha : ‖a‖ ≤ 1) (hδ : ‖δ‖ < r) :
    1 - a * (δ / (r : ℂ)) ≠ 0 := by
  intro hzero
  have hprod : a * (δ / (r : ℂ)) = 1 := by
    linear_combination -hzero
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  have hquot : ‖δ / (r : ℂ)‖ < 1 := by
    rw [norm_div, hrnorm, div_lt_one hr]
    exact hδ
  have hlt : ‖a * (δ / (r : ℂ))‖ < 1 := by
    rw [norm_mul]
    calc
      ‖a‖ * ‖δ / (r : ℂ)‖ ≤ 1 * ‖δ / (r : ℂ)‖ :=
        mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ < 1 := by simpa using hquot
  rw [hprod, norm_one] at hlt
  exact lt_irrefl 1 hlt

noncomputable def b6a_scaledRoot (n : ℕ) (a δ : ℂ) (r : ℝ) : ℂ :=
  (1 - a * (δ / (r : ℂ))) ^ ((n : ℂ)⁻¹)

theorem b6a_scaledRoot_pow (n : ℕ) (hn : 0 < n) (a δ : ℂ) (r : ℝ) :
    b6a_scaledRoot n a δ r ^ n = 1 - a * (δ / (r : ℂ)) := by
  exact Complex.cpow_nat_inv_pow _ (Nat.ne_of_gt hn)

theorem b6a_scaledRoot_ne_zero (n : ℕ) (hn : 0 < n) (a δ : ℂ) (r : ℝ)
    (hr : 0 < r) (ha : ‖a‖ ≤ 1) (hδ : ‖δ‖ < r) :
    b6a_scaledRoot n a δ r ≠ 0 := by
  intro hzero
  have hpow := b6a_scaledRoot_pow n hn a δ r
  rw [hzero, zero_pow hn.ne'] at hpow
  exact b6a_one_sub_scaled_ne_zero a δ r hr ha hδ hpow.symm

noncomputable def b6a_phasePower (n : ℕ) (w : ℂ) : ℂ :=
  if w = 0 then 0 else ((‖w‖ : ℂ) ^ n) / w ^ n

theorem b6a_phasePower_norm_le_one (n : ℕ) (w : ℂ) :
    ‖b6a_phasePower n w‖ ≤ 1 := by
  by_cases hw : w = 0
  · simp [b6a_phasePower, hw]
  · rw [b6a_phasePower, if_neg hw, norm_div, norm_pow, norm_pow]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w)]
    rw [div_self (pow_ne_zero n (norm_ne_zero_iff.mpr hw))]

noncomputable def b6a_movingRoot (n : ℕ) (w δ : ℂ) (r : ℝ) : ℂ :=
  w * b6a_scaledRoot n (b6a_phasePower n w) δ r

theorem b6a_movingRoot_pow (n : ℕ) (hn : 0 < n) (w δ : ℂ) (r : ℝ) :
    b6a_movingRoot n w δ r ^ n =
      w ^ n - ((‖w‖ : ℂ) ^ n) * (δ / (r : ℂ)) := by
  by_cases hw : w = 0
  · subst w
    simp [b6a_movingRoot, hn.ne']
  · rw [b6a_movingRoot, mul_pow, b6a_scaledRoot_pow n hn, b6a_phasePower,
      if_neg hw]
    field_simp [pow_ne_zero n hw]

theorem b6a_norm_cast_pow (w : ℂ) (n : ℕ) :
    (‖w‖ : ℂ) ^ n = ((‖w‖ ^ n : ℝ) : ℂ) := by
  exact (Complex.ofReal_pow ‖w‖ n).symm

theorem b6a_plane_near_branch (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (i : Fin 10) (n : ℕ) (w : ℂ) (hw : ‖w‖ ^ n < b6t_radius b) :
    b6t_plane b t (b i + w ^ n) - t i =
      w ^ n - ((‖w‖ : ℂ) ^ n) * ((t i - b i) / (b6t_radius b : ℂ)) := by
  have hr : 0 < b6t_radius b := (b6t_discs_aux b hb).1
  have hzi : b i + w ^ n ∈ Metric.closedBall (b i) (b6t_radius b) := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_pow]
    exact hw.le
  rw [b6t_plane, Finset.sum_eq_single i]
  · rw [dist_eq_norm, add_sub_cancel_left, norm_pow,
      max_eq_right (sub_nonneg.mpr (div_le_one hr |>.2 hw.le)), b6a_norm_cast_pow]
    rw [RCLike.real_smul_eq_coe_mul]
    push_cast
    field_simp [ne_of_gt hr]
    ring_nf
    congr 1 <;> ac_rfl
  · intro j _ hji
    have hjnot : b i + w ^ n ∉ Metric.closedBall (b j) (b6t_radius b) :=
      fun hj ↦ Set.disjoint_left.mp ((b6t_discs_aux b hb).2.2 (Ne.symm hji)) hzi hj
    have hjdist : b6t_radius b < dist (b i + w ^ n) (b j) := by
      simpa [Metric.mem_closedBall, not_le] using hjnot
    have hneg : 1 - dist (b i + w ^ n) (b j) / b6t_radius b < 0 := by
      exact sub_neg.mpr ((lt_div_iff₀ hr).2 (by simpa using hjdist))
    simp [max_eq_left hneg.le]
  · simp

theorem b6a_phasePower_continuousAt (n : ℕ) (w : ℂ) (hw : w ≠ 0) :
    ContinuousAt (b6a_phasePower n) w := by
  have hnorm : ContinuousAt (fun z : ℂ ↦ (‖z‖ : ℂ)) w := by fun_prop
  apply ((hnorm.pow n).div (continuousAt_id.pow n) (pow_ne_zero n hw)).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hw] with z hz
  simp [b6a_phasePower, hz]

theorem b6a_scaledRoot_continuousAt (n : ℕ) (a δ : ℂ) (r : ℝ) (hr : 0 < r)
    (ha : ‖a‖ ≤ 1) (hδ : ‖δ‖ < r) :
    ContinuousAt (fun p : ℂ × ℂ ↦ b6a_scaledRoot n p.1 p.2 r) (a, δ) := by
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  have hquot : ‖δ / (r : ℂ)‖ < 1 := by
    rw [norm_div, hrnorm, div_lt_one hr]
    exact hδ
  have hprod : ‖a * (δ / (r : ℂ))‖ < 1 := by
    rw [norm_mul]
    calc
      ‖a‖ * ‖δ / (r : ℂ)‖ ≤ 1 * ‖δ / (r : ℂ)‖ :=
        mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ < 1 := by simpa using hquot
  have hre : 0 < (1 - a * (δ / (r : ℂ))).re := by
    change 0 < 1 - (a * (δ / (r : ℂ))).re
    exact sub_pos.mpr ((le_abs_self _).trans
      (Complex.abs_re_le_norm _) |>.trans_lt hprod)
  unfold b6a_scaledRoot
  apply ContinuousAt.cpow
  · fun_prop
  · exact continuousAt_const
  · exact Or.inl hre

theorem b6a_scaledRoot_norm_le_two (n : ℕ) (hn : 0 < n) (a δ : ℂ) (r : ℝ)
    (hr : 0 < r) (ha : ‖a‖ ≤ 1) (hδ : ‖δ‖ ≤ r) :
    ‖b6a_scaledRoot n a δ r‖ ≤ 2 := by
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  have hquot : ‖δ / (r : ℂ)‖ ≤ 1 := by
    rw [norm_div, hrnorm, div_le_one hr]
    exact hδ
  have hbase : ‖1 - a * (δ / (r : ℂ))‖ ≤ 2 := by
    have hmul : ‖a‖ * ‖δ / (r : ℂ)‖ ≤ 1 := by
      calc
        ‖a‖ * ‖δ / (r : ℂ)‖ ≤ 1 * ‖δ / (r : ℂ)‖ :=
          mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ ≤ 1 := by simpa using hquot
    calc
      ‖1 - a * (δ / (r : ℂ))‖ ≤ ‖(1 : ℂ)‖ + ‖a * (δ / (r : ℂ))‖ :=
        norm_sub_le _ _
      _ ≤ 1 + 1 := by
        rw [norm_one, norm_mul]
        linarith
      _ = 2 := by norm_num
  rw [b6a_scaledRoot, Complex.norm_cpow_inv_nat]
  have hexp : (n⁻¹ : ℝ) ≤ 1 := by
    apply (inv_le_one₀ (by exact_mod_cast hn)).2
    exact_mod_cast hn
  by_cases hsmall : ‖1 - a * (δ / (r : ℂ))‖ ≤ 1
  · exact (Real.rpow_le_one (norm_nonneg _) hsmall (by positivity)).trans (by norm_num)
  · have hone : 1 ≤ ‖1 - a * (δ / (r : ℂ))‖ := le_of_lt (lt_of_not_ge hsmall)
    calc
      ‖1 - a * (δ / (r : ℂ))‖ ^ (n⁻¹ : ℝ) ≤
          ‖1 - a * (δ / (r : ℂ))‖ ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hone hexp
      _ = ‖1 - a * (δ / (r : ℂ))‖ := Real.rpow_one _
      _ ≤ 2 := hbase

theorem b6a_scaledRoot_norm_lower (n : ℕ) (a δ : ℂ) (r : ℝ)
    (hr : 0 < r) (ha : ‖a‖ ≤ 1) (hδ : ‖δ‖ < r) :
    (1 - ‖δ / (r : ℂ)‖) ^ (n⁻¹ : ℝ) ≤ ‖b6a_scaledRoot n a δ r‖ := by
  have hq : ‖δ / (r : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_lt_one hr]
    exact hδ
  have hbase : 1 - ‖δ / (r : ℂ)‖ ≤ ‖1 - a * (δ / (r : ℂ))‖ := by
    calc
      1 - ‖δ / (r : ℂ)‖ ≤ 1 - ‖a‖ * ‖δ / (r : ℂ)‖ := by
        gcongr
        exact mul_le_of_le_one_left (norm_nonneg _) ha
      _ = ‖(1 : ℂ)‖ - ‖a * (δ / (r : ℂ))‖ := by rw [norm_one, norm_mul]
      _ ≤ ‖1 - a * (δ / (r : ℂ))‖ := norm_sub_norm_le _ _
  rw [b6a_scaledRoot, Complex.norm_cpow_inv_nat]
  exact Real.rpow_le_rpow (sub_nonneg.mpr hq.le) hbase (by positivity)

theorem b6a_movingRoot_norm_lower (n : ℕ) (w δ : ℂ) (r : ℝ)
    (hr : 0 < r) (hδ : ‖δ‖ < r) :
    ‖w‖ * (1 - ‖δ / (r : ℂ)‖) ^ (n⁻¹ : ℝ) ≤ ‖b6a_movingRoot n w δ r‖ := by
  rw [b6a_movingRoot, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (b6a_scaledRoot_norm_lower n (b6a_phasePower n w) δ r hr
      (b6a_phasePower_norm_le_one n w) hδ) (norm_nonneg _)

theorem b6a_movingRoot_continuousAt_of_ne_zero (n : ℕ) (w δ : ℂ) (r : ℝ)
    (hr : 0 < r) (hw : w ≠ 0) (hδ : ‖δ‖ < r) :
    ContinuousAt (fun p : ℂ × ℂ ↦ b6a_movingRoot n p.1 p.2 r) (w, δ) := by
  unfold b6a_movingRoot
  apply continuous_fst.continuousAt.mul
  have hphase : ContinuousAt
      (fun p : ℂ × ℂ ↦ b6a_phasePower n p.1) (w, δ) :=
    (b6a_phasePower_continuousAt n w hw).comp' continuous_fst.continuousAt
  have hinner : ContinuousAt
      (fun p : ℂ × ℂ ↦ (b6a_phasePower n p.1, p.2)) (w, δ) :=
    hphase.prodMk continuous_snd.continuousAt
  have houter := b6a_scaledRoot_continuousAt n (b6a_phasePower n w) δ r hr
    (b6a_phasePower_norm_le_one n w) hδ
  have hc : ContinuousAt
      ((fun z : ℂ × ℂ ↦ b6a_scaledRoot n z.1 z.2 r) ∘
        (fun p : ℂ × ℂ ↦ (b6a_phasePower n p.1, p.2))) (w, δ) :=
    Filter.Tendsto.comp houter hinner
  simpa [Function.comp_def] using hc

theorem b6a_movingRoot_continuousAt_zero (n : ℕ) (hn : 0 < n) (δ : ℂ) (r : ℝ)
    (hr : 0 < r) (hδ : ‖δ‖ < r) :
    ContinuousAt (fun p : ℂ × ℂ ↦ b6a_movingRoot n p.1 p.2 r) (0, δ) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let d := min (r - ‖δ‖) (ε / 2)
  have hd : 0 < d := lt_min (sub_pos.mpr hδ) (half_pos hε)
  refine ⟨d, hd, ?_⟩
  rintro ⟨w, δ'⟩ hwd
  rw [Prod.dist_eq, max_lt_iff] at hwd
  have hw : ‖w‖ < d := by
    simpa [dist_eq_norm] using hwd.1
  have hδdist : dist δ' δ < d := by
    exact hwd.2
  have hδ' : ‖δ'‖ ≤ r := by
    exact (calc
      ‖δ'‖ ≤ ‖δ‖ + ‖δ' - δ‖ := by
        simpa [sub_add_cancel] using norm_add_le δ (δ' - δ)
      _ < ‖δ‖ + d := by
        gcongr
        simpa [dist_eq_norm] using hδdist
      _ ≤ ‖δ‖ + (r - ‖δ‖) := by
        gcongr
        exact min_le_left _ _
      _ = r := by ring).le
  have hroot := b6a_scaledRoot_norm_le_two n hn (b6a_phasePower n w) δ' r hr
    (b6a_phasePower_norm_le_one n w) hδ'
  rw [show b6a_movingRoot n 0 δ r = 0 by simp [b6a_movingRoot], dist_zero_right,
    b6a_movingRoot, norm_mul]
  calc
    ‖w‖ * ‖b6a_scaledRoot n (b6a_phasePower n w) δ' r‖ ≤ ‖w‖ * 2 :=
      mul_le_mul_of_nonneg_left hroot (norm_nonneg _)
    _ < d * 2 := by gcongr
    _ ≤ (ε / 2) * 2 := by gcongr; exact min_le_right _ _
    _ = ε := by ring

theorem b6a_movingRoot_continuousAt (n : ℕ) (hn : 0 < n) (w δ : ℂ) (r : ℝ)
    (hr : 0 < r) (hδ : ‖δ‖ < r) :
    ContinuousAt (fun p : ℂ × ℂ ↦ b6a_movingRoot n p.1 p.2 r) (w, δ) := by
  by_cases hw : w = 0
  · subst w
    exact b6a_movingRoot_continuousAt_zero n hn δ r hr hδ
  · exact b6a_movingRoot_continuousAt_of_ne_zero n w δ r hr hw hδ

theorem b6a_radialDeform_injective (δ : ℂ) (r : ℝ) (hr : 0 < r) (hδ : ‖δ‖ < r) :
    Function.Injective (fun z : ℂ ↦ z - (‖z‖ : ℂ) * (δ / (r : ℂ))) := by
  intro z₁ z₂ heq
  have hdiff : z₁ - z₂ = ((‖z₁‖ - ‖z₂‖ : ℝ) : ℂ) * (δ / (r : ℂ)) := by
    push_cast
    linear_combination heq
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  have hq : ‖δ / (r : ℂ)‖ < 1 := by
    rw [norm_div, hrnorm, div_lt_one hr]
    exact hδ
  have hle : ‖z₁ - z₂‖ ≤ ‖z₁ - z₂‖ * ‖δ / (r : ℂ)‖ := by
    calc
      ‖z₁ - z₂‖ = ‖((‖z₁‖ - ‖z₂‖ : ℝ) : ℂ) * (δ / (r : ℂ))‖ :=
        congrArg norm hdiff
      _ = |‖z₁‖ - ‖z₂‖| * ‖δ / (r : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖z₁ - z₂‖ * ‖δ / (r : ℂ)‖ := by
        gcongr
        exact abs_norm_sub_norm_le z₁ z₂
  have hz : ‖z₁ - z₂‖ = 0 := by
    by_contra hz
    have hzpos : 0 < ‖z₁ - z₂‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have := mul_lt_mul_of_pos_left hq hzpos
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem b6a_radialDeform_surjective (δ : ℂ) (r : ℝ) (hr : 0 < r) (hδ : ‖δ‖ < r) :
    Function.Surjective (fun z : ℂ ↦ z - (‖z‖ : ℂ) * (δ / (r : ℂ))) := by
  intro y
  let c : ℂ := δ / (r : ℂ)
  let K : NNReal := ⟨‖c‖, norm_nonneg c⟩
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  have hK : K < 1 := by
    change ‖δ / (r : ℂ)‖ < 1
    rw [norm_div, hrnorm, div_lt_one hr]
    exact hδ
  let F : ℂ → ℂ := fun z ↦ y + (‖z‖ : ℂ) * c
  have hLip : LipschitzWith K F := by
    apply LipschitzWith.of_dist_le_mul
    intro z₁ z₂
    dsimp [F]
    rw [dist_eq_norm, dist_eq_norm]
    rw [add_sub_add_left_eq_sub, ← sub_mul, norm_mul]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    change |‖z₁‖ - ‖z₂‖| * ‖c‖ ≤ (K : ℝ) * ‖z₁ - z₂‖
    rw [show (K : ℝ) = ‖c‖ by rfl]
    rw [mul_comm]
    gcongr
    exact abs_norm_sub_norm_le z₁ z₂
  have hcontract : ContractingWith K F := ⟨hK, hLip⟩
  obtain ⟨z, hz, _, _⟩ := hcontract.exists_fixedPoint 0 (by simp)
  refine ⟨z, ?_⟩
  change z - (‖z‖ : ℂ) * c = y
  dsimp [F] at hz
  linear_combination hz.symm

theorem b6a_movingRoot_injective (n : ℕ) (hn : 0 < n) (δ : ℂ) (r : ℝ)
    (hr : 0 < r) (hδ : ‖δ‖ < r) :
    Function.Injective (fun w : ℂ ↦ b6a_movingRoot n w δ r) := by
  intro w₁ w₂ heq
  have hp := congrArg (fun z : ℂ ↦ z ^ n) heq
  rw [b6a_movingRoot_pow n hn, b6a_movingRoot_pow n hn] at hp
  have hpowers : w₁ ^ n = w₂ ^ n := by
    apply b6a_radialDeform_injective δ r hr hδ
    change w₁ ^ n - (‖w₁ ^ n‖ : ℂ) * (δ / (r : ℂ)) =
      w₂ ^ n - (‖w₂ ^ n‖ : ℂ) * (δ / (r : ℂ))
    rw [norm_pow, norm_pow]
    rw [b6a_norm_cast_pow, b6a_norm_cast_pow] at hp
    exact hp
  by_cases hw₁ : w₁ = 0
  · subst w₁
    apply Eq.symm
    have hzero : w₂ ^ n = 0 := hpowers.symm.trans (zero_pow hn.ne')
    by_contra hw₂
    exact pow_ne_zero n hw₂ hzero
  have hw₂ : w₂ ≠ 0 := by
    intro hw₂
    rw [hw₂, zero_pow hn.ne'] at hpowers
    exact pow_ne_zero n hw₁ hpowers
  have hnormpow : ‖w₁‖ ^ n = ‖w₂‖ ^ n := by
    simpa [norm_pow] using congrArg norm hpowers
  have hphase : b6a_phasePower n w₁ = b6a_phasePower n w₂ := by
    simp only [b6a_phasePower, hw₁, hw₂, if_false]
    rw [hpowers]
    congr 1
    exact_mod_cast hnormpow
  change w₁ * b6a_scaledRoot n (b6a_phasePower n w₁) δ r =
    w₂ * b6a_scaledRoot n (b6a_phasePower n w₂) δ r at heq
  rw [hphase] at heq
  exact mul_right_cancel₀
    (b6a_scaledRoot_ne_zero n hn (b6a_phasePower n w₂) δ r hr
      (b6a_phasePower_norm_le_one n w₂) hδ) heq

theorem b6a_phasePower_root_mul (n : ℕ) (η w : ℂ) (hηpow : η ^ n = 1)
    (hηnorm : ‖η‖ = 1) :
    b6a_phasePower n (η * w) = b6a_phasePower n w := by
  by_cases hw : w = 0
  · subst w
    simp [b6a_phasePower]
  have hη : η ≠ 0 := norm_ne_zero_iff.mp (by rw [hηnorm]; norm_num)
  simp only [b6a_phasePower, hw, mul_ne_zero hη hw, if_false]
  rw [norm_mul, hηnorm, one_mul, mul_pow, hηpow, one_mul]

theorem b6a_movingRoot_root_mul (n : ℕ) (η w δ : ℂ) (r : ℝ)
    (hηpow : η ^ n = 1) (hηnorm : ‖η‖ = 1) :
    b6a_movingRoot n (η * w) δ r = η * b6a_movingRoot n w δ r := by
  rw [b6a_movingRoot, b6a_phasePower_root_mul n η w hηpow hηnorm, b6a_movingRoot]
  ring

theorem b6a_movingRoot_surjective (n : ℕ) (hn : 0 < n) (δ : ℂ) (r : ℝ)
    (hr : 0 < r) (hδ : ‖δ‖ < r) :
    Function.Surjective (fun w : ℂ ↦ b6a_movingRoot n w δ r) := by
  intro y
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp [b6a_movingRoot]⟩
  obtain ⟨z, hz⟩ := b6a_radialDeform_surjective δ r hr hδ (y ^ n)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z hn
  let a := b6a_movingRoot n w δ r
  have hapow : a ^ n = y ^ n := by
    dsimp [a]
    rw [b6a_movingRoot_pow n hn, hw, b6a_norm_cast_pow]
    rw [← hw] at hz
    change w ^ n - (‖w ^ n‖ : ℂ) * (δ / (r : ℂ)) = y ^ n at hz
    rw [norm_pow] at hz
    rw [← hw]
    exact hz
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, zero_pow hn.ne'] at hapow
    exact pow_ne_zero n hy hapow.symm
  let η := y / a
  have hηpow : η ^ n = 1 := by
    dsimp [η]
    rw [div_pow, hapow, div_self (pow_ne_zero n hy)]
  have hηnorm : ‖η‖ = 1 := by
    let u : NNReal := ⟨‖η‖, norm_nonneg η⟩
    have hupow : u ^ n = 1 := by
      apply Subtype.ext
      change ‖η‖ ^ n = 1
      rw [← norm_pow, hηpow, norm_one]
    have hu : u = 1 := by
      apply pow_left_injective hn.ne'
      simpa using hupow
    exact congrArg (fun x : NNReal ↦ (x : ℝ)) hu
  refine ⟨η * w, ?_⟩
  change b6a_movingRoot n (η * w) δ r = y
  rw [b6a_movingRoot_root_mul n η w δ r hηpow hηnorm]
  change η * a = y
  exact div_mul_cancel₀ y ha

theorem b6a_movingRoot_isProperMap (n : ℕ) (hn : 0 < n) (δ : ℂ) (r : ℝ)
    (hr : 0 < r) (hδ : ‖δ‖ < r) :
    IsProperMap (fun w : ℂ ↦ b6a_movingRoot n w δ r) := by
  apply isProperMap_iff_tendsto_cocompact.mpr
  constructor
  · apply continuous_iff_continuousAt.2
    intro w
    have hin : ContinuousAt (fun z : ℂ ↦ (z, δ)) w :=
      continuousAt_id.prodMk continuousAt_const
    have hc : ContinuousAt
        ((fun p : ℂ × ℂ ↦ b6a_movingRoot n p.1 p.2 r) ∘ fun z : ℂ ↦ (z, δ)) w :=
      Filter.Tendsto.comp (b6a_movingRoot_continuousAt n hn w δ r hr hδ) hin
    simpa [Function.comp_def] using hc
  · apply Filter.tendsto_cocompact_cocompact_of_norm
    intro ε
    let c := (1 - ‖δ / (r : ℂ)‖) ^ (n⁻¹ : ℝ)
    have hq : ‖δ / (r : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_lt_one hr]
      exact hδ
    have hc : 0 < c := Real.rpow_pos_of_pos (sub_pos.mpr hq) _
    refine ⟨ε / c, fun w hw ↦ ?_⟩
    have hlower := b6a_movingRoot_norm_lower n w δ r hr hδ
    have hmul : ε < ‖w‖ * c := (div_lt_iff₀ hc).mp hw
    exact hmul.trans_le hlower

theorem b6a_movingRoot_isHomeomorph (n : ℕ) (hn : 0 < n) (δ : ℂ) (r : ℝ)
    (hr : 0 < r) (hδ : ‖δ‖ < r) :
    IsHomeomorph (fun w : ℂ ↦ b6a_movingRoot n w δ r) :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.2
    ⟨(b6a_movingRoot_isProperMap n hn δ r hr hδ).continuous,
      (b6a_movingRoot_isProperMap n hn δ r hr hδ).isClosedMap,
      ⟨b6a_movingRoot_injective n hn δ r hr hδ,
        b6a_movingRoot_surjective n hn δ r hr hδ⟩⟩

theorem b6a_totalMovingRoot_continuous (n : ℕ) (hn : 0 < n) (r s : ℝ)
    (hr : 0 < r) (hsr : s < r) :
    Continuous (fun p : {δ : ℂ // ‖δ‖ ≤ s} × ℂ ↦
      (p.1, b6a_movingRoot n p.2 p.1.val r)) := by
  apply continuous_iff_continuousAt.2
  intro p
  have hδ : ‖p.1.val‖ < r := p.1.property.trans_lt hsr
  have hinner : ContinuousAt
      (fun q : {δ : ℂ // ‖δ‖ ≤ s} × ℂ ↦ (q.2, q.1.val)) p :=
    continuous_snd.continuousAt.prodMk
      (continuous_subtype_val.comp continuous_fst).continuousAt
  have hroot : ContinuousAt
      (fun q : {δ : ℂ // ‖δ‖ ≤ s} × ℂ ↦ b6a_movingRoot n q.2 q.1.val r) p := by
    have hc : ContinuousAt
        ((fun z : ℂ × ℂ ↦ b6a_movingRoot n z.1 z.2 r) ∘
          fun q : {δ : ℂ // ‖δ‖ ≤ s} × ℂ ↦ (q.2, q.1.val)) p :=
      Filter.Tendsto.comp (b6a_movingRoot_continuousAt n hn p.2 p.1.val r hr hδ) hinner
    simpa [Function.comp_def] using hc
  exact continuous_fst.continuousAt.prodMk hroot

theorem b6a_totalMovingRoot_bijective (n : ℕ) (hn : 0 < n) (r s : ℝ)
    (hr : 0 < r) (hsr : s < r) :
    Function.Bijective (fun p : {δ : ℂ // ‖δ‖ ≤ s} × ℂ ↦
      (p.1, b6a_movingRoot n p.2 p.1.val r)) := by
  constructor
  · rintro ⟨δ₁, w₁⟩ ⟨δ₂, w₂⟩ heq
    have hδ : δ₁ = δ₂ := congrArg Prod.fst heq
    subst δ₂
    apply Prod.ext
    · rfl
    · dsimp
      apply b6a_movingRoot_injective n hn δ₁.val r hr (δ₁.property.trans_lt hsr)
      exact congrArg Prod.snd heq
  · rintro ⟨δ, v⟩
    obtain ⟨w, hw⟩ := b6a_movingRoot_surjective n hn δ.val r hr
      (δ.property.trans_lt hsr) v
    exact ⟨(δ, w), by simp [hw]⟩

theorem b6a_totalMovingRoot_isProperMap (n : ℕ) (hn : 0 < n) (r s : ℝ)
    (hr : 0 < r) (hs : 0 ≤ s) (hsr : s < r) :
    IsProperMap (fun p : {δ : ℂ // ‖δ‖ ≤ s} × ℂ ↦
      (p.1, b6a_movingRoot n p.2 p.1.val r)) := by
  let F : {δ : ℂ // ‖δ‖ ≤ s} × ℂ → {δ : ℂ // ‖δ‖ ≤ s} × ℂ :=
    fun p ↦ (p.1, b6a_movingRoot n p.2 p.1.val r)
  have hparamCompact : IsCompact {δ : ℂ | ‖δ‖ ≤ s} := by
    have heq : {δ : ℂ | ‖δ‖ ≤ s} = Metric.closedBall 0 s := by
      ext δ
      simp [dist_zero_right]
    rw [heq]
    exact isCompact_closedBall _ _
  letI : CompactSpace {δ : ℂ // ‖δ‖ ≤ s} :=
    isCompact_iff_compactSpace.mp hparamCompact
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨b6a_totalMovingRoot_continuous n hn r s hr hsr, ?_⟩
  intro K hK
  let δzero : {δ : ℂ // ‖δ‖ ≤ s} := ⟨0, by simpa using hs⟩
  let pzero : {δ : ℂ // ‖δ‖ ≤ s} × ℂ := (δzero, 0)
  obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall
    pzero
  let c := (1 - s / r) ^ (n⁻¹ : ℝ)
  have hsr' : s / r < 1 := (div_lt_one hr).2 hsr
  have hc : 0 < c := Real.rpow_pos_of_pos (sub_pos.mpr hsr') _
  have hclosed : IsClosed (F ⁻¹' K) :=
    hK.isClosed.preimage (b6a_totalMovingRoot_continuous n hn r s hr hsr)
  apply (isCompact_univ.prod (isCompact_closedBall (0 : ℂ) (B / c))).of_isClosed_subset hclosed
  intro p hp
  have hFB : dist (F p) pzero ≤ B := by
    have := hB hp
    simpa [Metric.mem_closedBall] using this
  have hrootB : ‖b6a_movingRoot n p.2 p.1.val r‖ ≤ B := by
    rw [Prod.dist_eq] at hFB
    have hsnd := (le_max_right (dist (F p).1 pzero.1)
      (dist (F p).2 pzero.2)).trans hFB
    simpa [F, pzero, δzero, b6a_movingRoot, dist_zero_right] using hsnd
  have hq : ‖p.1.val / (r : ℂ)‖ ≤ s / r := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact div_le_div_of_nonneg_right p.1.property hr.le
  have hcδ : c ≤ (1 - ‖p.1.val / (r : ℂ)‖) ^ (n⁻¹ : ℝ) := by
    apply Real.rpow_le_rpow
    · exact sub_nonneg.mpr hsr'.le
    · linarith
    · positivity
  have hlower := b6a_movingRoot_norm_lower n p.2 p.1.val r hr
    (p.1.property.trans_lt hsr)
  have hw : ‖p.2‖ ≤ B / c := by
    apply (le_div_iff₀ hc).2
    exact (mul_le_mul_of_nonneg_left hcδ (norm_nonneg _)).trans (hlower.trans hrootB)
  exact ⟨Set.mem_univ p.1, by simpa [Metric.mem_closedBall, dist_zero_left]⟩

theorem b6a_totalMovingRoot_isHomeomorph (n : ℕ) (hn : 0 < n) (r s : ℝ)
    (hr : 0 < r) (hs : 0 ≤ s) (hsr : s < r) :
    IsHomeomorph (fun p : {δ : ℂ // ‖δ‖ ≤ s} × ℂ ↦
      (p.1, b6a_movingRoot n p.2 p.1.val r)) :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.2
    ⟨b6a_totalMovingRoot_continuous n hn r s hr hsr,
      (b6a_totalMovingRoot_isProperMap n hn r s hr hs hsr).isClosedMap,
      b6a_totalMovingRoot_bijective n hn r s hr hsr⟩

noncomputable def b6a_totalMovingRootHomeomorph (n : ℕ) (hn : 0 < n) (r s : ℝ)
    (hr : 0 < r) (hs : 0 ≤ s) (hsr : s < r) :
    ({δ : ℂ // ‖δ‖ ≤ s} × ℂ) ≃ₜ ({δ : ℂ // ‖δ‖ ≤ s} × ℂ) :=
  IsHomeomorph.homeomorph _ (b6a_totalMovingRoot_isHomeomorph n hn r s hr hs hsr)

@[simp] theorem b6a_totalMovingRootHomeomorph_apply (n : ℕ) (hn : 0 < n)
    (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) (hsr : s < r)
    (p : {δ : ℂ // ‖δ‖ ≤ s} × ℂ) :
    b6a_totalMovingRootHomeomorph n hn r s hr hs hsr p =
      (p.1, b6a_movingRoot n p.2 p.1.val r) := rfl

noncomputable def b6a_baseChangeHomeomorph {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] (e : D × ℂ ≃ₜ D × ℂ) (hfst : ∀ p, (e p).1 = p.1)
    (d : X → D) (hd : Continuous d) : X × ℂ ≃ₜ X × ℂ where
  toFun p := (p.1, (e (d p.1, p.2)).2)
  invFun p := (p.1, (e.symm (d p.1, p.2)).2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · dsimp
      have he : (d p.1, (e (d p.1, p.2)).2) = e (d p.1, p.2) := by
        apply Prod.ext
        · exact (hfst (d p.1, p.2)).symm
        · rfl
      rw [he, e.symm_apply_apply]
  right_inv p := by
    apply Prod.ext
    · rfl
    · dsimp
      have hinvfst : ∀ q, (e.symm q).1 = q.1 := by
        intro q
        have h := congrArg Prod.fst (e.apply_symm_apply q)
        exact (hfst (e.symm q)).symm.trans h
      have he : (d p.1, (e.symm (d p.1, p.2)).2) = e.symm (d p.1, p.2) := by
        apply Prod.ext
        · exact (hinvfst (d p.1, p.2)).symm
        · rfl
      rw [he, e.apply_symm_apply]
  continuous_toFun := continuous_fst.prodMk
    (e.continuous.comp ((hd.comp continuous_fst).prodMk continuous_snd) |>.snd)
  continuous_invFun := continuous_fst.prodMk
    (e.symm.continuous.comp ((hd.comp continuous_fst).prodMk continuous_snd) |>.snd)

@[simp] theorem b6a_baseChangeHomeomorph_apply {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] (e : D × ℂ ≃ₜ D × ℂ) (hfst : ∀ p, (e p).1 = p.1)
    (d : X → D) (hd : Continuous d) (p : X × ℂ) :
    b6a_baseChangeHomeomorph e hfst d hd p = (p.1, (e (d p.1, p.2)).2) := rfl

def b6a_rootLocalRadius (b : Fin 10 → ℂ) (t : b6t_polydisc b) (i : Fin 10) : ℝ :=
  (‖t.val i - b i‖ + b6t_radius b) / 2

theorem b6a_rootLocalRadius_nonneg (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : b6t_polydisc b) (i : Fin 10) :
    0 ≤ b6a_rootLocalRadius b t i := by
  have hr := (b6t_discs_aux b hb).1
  exact div_nonneg (add_nonneg (norm_nonneg _) hr.le) (by norm_num)

theorem b6a_rootLocalRadius_lt (b : Fin 10 → ℂ) (t : b6t_polydisc b) (i : Fin 10) :
    b6a_rootLocalRadius b t i < b6t_radius b := by
  have ht := t.property i
  rw [Metric.mem_ball, dist_eq_norm] at ht
  dsimp [b6a_rootLocalRadius]
  linarith

theorem b6a_norm_sub_lt_rootLocalRadius (b : Fin 10 → ℂ) (t : b6t_polydisc b)
    (i : Fin 10) :
    ‖t.val i - b i‖ < b6a_rootLocalRadius b t i := by
  have ht := b6a_rootLocalRadius_lt b t i
  dsimp [b6a_rootLocalRadius] at ht ⊢
  linarith

def b6a_rootParamOpen (b : Fin 10 → ℂ) (t : b6t_polydisc b) (i : Fin 10) :
    TopologicalSpace.Opens (b6t_polydisc b) where
  carrier := {u | ‖u.val i - b i‖ < b6a_rootLocalRadius b t i}
  is_open' := by
    exact isOpen_lt (((continuous_apply i).comp continuous_subtype_val).sub
      continuous_const |>.norm) continuous_const

theorem b6a_mem_rootParamOpen (b : Fin 10 → ℂ) (t : b6t_polydisc b) (i : Fin 10) :
    t ∈ b6a_rootParamOpen b t i :=
  b6a_norm_sub_lt_rootLocalRadius b t i

def b6a_rootDisplacement (b : Fin 10 → ℂ) (t : b6t_polydisc b) (i : Fin 10)
    (u : b6a_rootParamOpen b t i) :
    {δ : ℂ // ‖δ‖ ≤ b6a_rootLocalRadius b t i} :=
  ⟨u.val.val i - b i, (u.property).le⟩

theorem b6a_rootDisplacement_continuous (b : Fin 10 → ℂ) (t : b6t_polydisc b)
    (i : Fin 10) :
    Continuous (b6a_rootDisplacement b t i) := by
  exact (((continuous_apply i).comp
    (continuous_subtype_val.comp continuous_subtype_val)).sub continuous_const).subtype_mk _

noncomputable def b6a_localMovingRootHomeomorph (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : b6t_polydisc b) (i : Fin 10) (n : ℕ) (hn : 0 < n) :
    (b6a_rootParamOpen b t i × ℂ) ≃ₜ (b6a_rootParamOpen b t i × ℂ) :=
  b6a_baseChangeHomeomorph
    (b6a_totalMovingRootHomeomorph n hn (b6t_radius b) (b6a_rootLocalRadius b t i)
      (b6t_discs_aux b hb).1 (b6a_rootLocalRadius_nonneg b hb t i)
      (b6a_rootLocalRadius_lt b t i))
    (fun _ ↦ rfl) (b6a_rootDisplacement b t i)
    (b6a_rootDisplacement_continuous b t i)

@[simp] theorem b6a_localMovingRootHomeomorph_apply (b : Fin 10 → ℂ)
    (hb : b ∈ b6_chart) (t : b6t_polydisc b) (i : Fin 10) (n : ℕ) (hn : 0 < n)
    (p : b6a_rootParamOpen b t i × ℂ) :
    b6a_localMovingRootHomeomorph b hb t i n hn p =
      (p.1, b6a_movingRoot n p.2 (p.1.val.val i - b i) (b6t_radius b)) := rfl

noncomputable def b6a_movingRootHom (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : b6t_polydisc b) (i : Fin 10) (n : ℕ) (hn : 0 < n) :
    OpenPartialHomeomorph (b6t_polydisc b × ℂ) (b6t_polydisc b × ℂ) := by
  let S := b6a_rootParamOpen b t i
  have hS : Nonempty S := ⟨⟨t, b6a_mem_rootParamOpen b t i⟩⟩
  let J := S.openPartialHomeomorphSubtypeCoe hS
  exact (J.prod (OpenPartialHomeomorph.refl ℂ)).symm.trans
    ((b6a_localMovingRootHomeomorph b hb t i n hn).toOpenPartialHomeomorph.trans
      (J.prod (OpenPartialHomeomorph.refl ℂ)))

theorem b6a_movingRootHom_source (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : b6t_polydisc b) (i : Fin 10) (n : ℕ) (hn : 0 < n) :
    (b6a_movingRootHom b hb t i n hn).source =
      (b6a_rootParamOpen b t i : Set (b6t_polydisc b)) ×ˢ (Set.univ : Set ℂ) := by
  ext p
  simp [b6a_movingRootHom]

theorem b6a_mem_movingRootHom_source (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : b6t_polydisc b) (i : Fin 10) (n : ℕ) (hn : 0 < n) (w : ℂ) :
    (t, w) ∈ (b6a_movingRootHom b hb t i n hn).source := by
  rw [b6a_movingRootHom_source]
  exact ⟨b6a_mem_rootParamOpen b t i, Set.mem_univ w⟩

theorem b6a_rootSubtype_inverse_coe (b : Fin 10 → ℂ) (t : b6t_polydisc b)
    (i : Fin 10) (u : b6a_rootParamOpen b t i) :
    ((b6a_rootParamOpen b t i).openPartialHomeomorphSubtypeCoe
        ⟨⟨t, b6a_mem_rootParamOpen b t i⟩⟩).symm u.val = u := by
  exact OpenPartialHomeomorph.left_inv _ (by simp)

theorem b6a_movingRootHom_apply (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : b6t_polydisc b) (i : Fin 10) (n : ℕ) (hn : 0 < n)
    (p : b6a_rootParamOpen b t i × ℂ) :
    b6a_movingRootHom b hb t i n hn (p.1.val, p.2) =
      (p.1.val, b6a_movingRoot n p.2 (p.1.val.val i - b i) (b6t_radius b)) := by
  simp [b6a_movingRootHom, b6a_rootSubtype_inverse_coe]

def b6a_rootCoordOpen (b : Fin 10 → ℂ) (n : ℕ) : Set ℂ :=
  {w | ‖w‖ ^ n < b6t_radius b}

theorem b6a_rootCoordOpen_isOpen (b : Fin 10 → ℂ) (n : ℕ) :
    IsOpen (b6a_rootCoordOpen b n) := by
  exact isOpen_lt (continuous_norm.pow n) continuous_const

theorem contDiffOn_of_continuousOn_pow_eq {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Set E) (hs : IsOpen s) (h r : E → ℂ) (hh : ContDiffOn ℂ ω h s)
    (hr : ContinuousOn r s) (e : ℕ) (he : 0 < e)
    (hne : ∀ q ∈ s, r q ≠ 0) (hpow : ∀ q ∈ s, r q ^ e = h q) :
    ContDiffOn ℂ ω r s := by
  intro q hq
  have hs_q : s ∈ 𝓝 q := hs.mem_nhds hq
  have hhq : ContDiffAt ℂ ω h q := (hh q hq).contDiffAt hs_q
  have hrq : ContinuousAt r q := (hr q hq).continuousAt hs_q
  let p : ℂ → ℂ := fun z ↦ z ^ e
  have hp : ContDiffAt ℂ ω p (r q) := by
    dsimp [p]
    fun_prop
  have hcoef : (e : ℂ) * r q ^ (e - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt he)) (pow_ne_zero _ (hne q hq))
  let d : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ
    (Units.mk0 ((e : ℂ) * r q ^ (e - 1)) hcoef)
  have hpd : HasFDerivAt p (d : ℂ →L[ℂ] ℂ) (r q) := by
    dsimp [p, d]
    exact (hasDerivAt_pow e (r q)).hasFDerivAt_equiv hcoef
  let l : ℂ → ℂ := hp.localInverse hpd (by simp)
  have hl : ContDiffAt ℂ ω l (h q) := by
    rw [← hpow q hq]
    exact hp.to_localInverse hpd (by simp)
  have hlh : ContDiffAt ℂ ω (l ∘ h) q := hl.comp q hhq
  apply ContDiffAt.contDiffWithinAt
  apply hlh.congr_of_eventuallyEq
  have hleft : ∀ᶠ z in 𝓝 (r q), l (p z) = z := by
    exact hp.hasStrictFDerivAt' hpd (by simp) |>.eventually_left_inverse
  filter_upwards [hrq hleft, hs_q] with x hx hxs
  rw [Function.comp_apply, ← hpow x hxs]
  exact hx.symm

end HodgeLean.Foundations.Program

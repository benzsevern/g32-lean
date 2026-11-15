module

public import HodgeLean.Foundations.Program.KernelFramesCert

/-! Explicit rational forms of the base frames and of the nine base numerators.
HC no distance; AV milestone no distance. -/
@[expose] public section

noncomputable section
namespace HodgeLean.Foundations.Program
open Matrix

local notation "𝕩" => (RatFunc.X : RatFunc ℚ)

theorem b65k_X_sub_ne (p : ℚ) : (RatFunc.X : RatFunc ℚ) - RatFunc.C p ≠ 0 := by
  have := (map_ne_zero_iff (algebraMap (Polynomial ℚ) (RatFunc ℚ))
    (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ))).2 (Polynomial.X_sub_C_ne_zero p)
  simpa using this

theorem b65k_fibre_five : b65k_fibrePoly 5 = (Polynomial.C (-10) * Polynomial.X^0 + Polynomial.C 15 * Polynomial.X^1 + Polynomial.C (-51/4) * Polynomial.X^2 + Polynomial.C (53/4) * Polynomial.X^3 + Polynomial.C (-69/4) * Polynomial.X^4 + Polynomial.C (27/4) * Polynomial.X^5 + Polynomial.C 1 * Polynomial.X^6) := by
  apply IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)
  simp only [b65k_fibrePoly, map_sub, map_inv₀, map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat, map_neg, map_div₀, map_one]
  ring

theorem b65k_fibre_five_ne : b65k_fibrePoly 5 ≠ 0 := by
  intro h
  have := congrArg (fun p : Polynomial ℚ => p.coeff 6) h
  rw [b65k_fibre_five] at this
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul] at this

theorem b65k_fibre_five_mapne : algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ))).2 b65k_fibre_five_ne

theorem b65k_fibre_five_map : algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) =
    ((-10) + 15 * 𝕩 + (-51/4) * 𝕩^2 + (53/4) * 𝕩^3 + (-69/4) * 𝕩^4 + (27/4) * 𝕩^5 + 𝕩^6) := by
  rw [b65k_fibre_five]
  simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat, map_neg, map_div₀, map_one]
  ring

theorem b65k_fibre_five_deriv : algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5).derivative =
    (15 + (-51/2) * 𝕩 + (159/4) * 𝕩^2 + (-69) * 𝕩^3 + (135/4) * 𝕩^4 + 6 * 𝕩^5) := by
  rw [b65k_fibre_five]
  simp only [map_add, Polynomial.derivative_C_mul_X_pow]
  simp only [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat, map_neg, map_div₀, map_one, map_natCast]
  norm_num

theorem b65k_companion_five : b65k_companion 5 = Matrix.of ![![0, 0, 0, 0, 0, 10], ![1, 0, 0, 0, 0, (-15)], ![0, 1, 0, 0, 0, (51/4)], ![0, 0, 1, 0, 0, (-53/4)], ![0, 0, 0, 1, 0, (69/4)], ![0, 0, 0, 0, 1, (-27/4)]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [b65k_companion, b65k_fibre_five, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul]

theorem b65k_trace_five_0 : Matrix.trace (b65k_companion 5 ^ 0) = 6 := by
  rw [b65k_companion_five]
  decide +kernel

theorem b65k_trace_five_1 : Matrix.trace (b65k_companion 5 ^ 1) = (-27/4) := by
  rw [b65k_companion_five]
  decide +kernel

theorem b65k_trace_five_2 : Matrix.trace (b65k_companion 5 ^ 2) = (1281/16) := by
  rw [b65k_companion_five]
  decide +kernel

theorem b65k_trace_five_3 : Matrix.trace (b65k_companion 5 ^ 3) = (-44583/64) := by
  rw [b65k_companion_five]
  decide +kernel

theorem b65k_trace_five_4 : Matrix.trace (b65k_companion 5 ^ 4) = (1593249/256) := by
  rw [b65k_companion_five]
  decide +kernel

theorem b65k_trace_five_5 : Matrix.trace (b65k_companion 5 ^ 5) = (-56573847/1024) := by
  rw [b65k_companion_five]
  decide +kernel

theorem b65k_rootSum_five_0 : b65k_rootSum 5 0 = (15 + (-51/2) * 𝕩 + (159/4) * 𝕩^2 + (-69) * 𝕩^3 + (135/4) * 𝕩^4 + 6 * 𝕩^5) / algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) := by
  have hP := b65k_fibre_five_mapne
  rw [eq_div_iff hP, b65k_rootSum, b65k_fibre_five_deriv]
  simp only [Finset.sum_range_zero, sub_zero]
  field_simp

theorem b65k_rootSum_five_1 : b65k_rootSum 5 1 = (60 + (-75) * 𝕩 + 51 * 𝕩^2 + (-159/4) * 𝕩^3 + (69/2) * 𝕩^4 + (-27/4) * 𝕩^5) / algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) := by
  have hP := b65k_fibre_five_mapne
  rw [eq_div_iff hP, b65k_rootSum, b65k_fibre_five_deriv]
  simp only [Finset.sum_range_succ, b65k_trace_five_0]
  simp only [Finset.sum_range_zero, map_ofNat]
  field_simp
  all_goals rw [b65k_fibre_five_map]; ring

theorem b65k_rootSum_five_2 : b65k_rootSum 5 2 = ((-135/2) + (645/4) * 𝕩 + (-2577/16) * 𝕩^2 + (2247/16) * 𝕩^3 + (-2499/16) * 𝕩^4 + (1281/16) * 𝕩^5) / algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) := by
  have hP := b65k_fibre_five_mapne
  rw [eq_div_iff hP, b65k_rootSum, b65k_fibre_five_deriv]
  simp only [Finset.sum_range_succ, b65k_trace_five_0, b65k_trace_five_1]
  simp only [Finset.sum_range_zero, map_ofNat, map_neg, map_div₀]
  field_simp
  all_goals rw [b65k_fibre_five_map]; ring

theorem b65k_rootSum_five_3 : b65k_rootSum 5 3 = ((6405/8) + (-20295/16) * 𝕩 + (75651/64) * 𝕩^2 + (-78201/64) * 𝕩^3 + (97377/64) * 𝕩^4 + (-44583/64) * 𝕩^5) / algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) := by
  have hP := b65k_fibre_five_mapne
  rw [eq_div_iff hP, b65k_rootSum, b65k_fibre_five_deriv]
  simp only [Finset.sum_range_succ, b65k_trace_five_0, b65k_trace_five_1, b65k_trace_five_2]
  simp only [Finset.sum_range_zero, map_ofNat, map_neg, map_div₀]
  field_simp
  all_goals rw [b65k_fibre_five_map]; ring

theorem b65k_rootSum_five_4 : b65k_rootSum 5 4 = ((-222915/32) + (719985/64) * 𝕩 + (-2598453/256) * 𝕩^2 + (2665503/256) * 𝕩^3 + (-3389031/256) * 𝕩^4 + (1593249/256) * 𝕩^5) / algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) := by
  have hP := b65k_fibre_five_mapne
  rw [eq_div_iff hP, b65k_rootSum, b65k_fibre_five_deriv]
  simp only [Finset.sum_range_succ, b65k_trace_five_0, b65k_trace_five_1, b65k_trace_five_2, b65k_trace_five_3]
  simp only [Finset.sum_range_zero, map_ofNat, map_neg, map_div₀]
  field_simp
  all_goals rw [b65k_fibre_five_map]; ring

theorem b65k_rootSum_five_5 : b65k_rootSum 5 5 = ((7966245/128) + (-25682055/256) * 𝕩 + (92775459/1024) * 𝕩^2 + (-94836009/1024) * 𝕩^3 + (120596193/1024) * 𝕩^4 + (-56573847/1024) * 𝕩^5) / algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) := by
  have hP := b65k_fibre_five_mapne
  rw [eq_div_iff hP, b65k_rootSum, b65k_fibre_five_deriv]
  simp only [Finset.sum_range_succ, b65k_trace_five_0, b65k_trace_five_1, b65k_trace_five_2, b65k_trace_five_3, b65k_trace_five_4]
  simp only [Finset.sum_range_zero, map_ofNat, map_neg, map_div₀]
  field_simp
  all_goals rw [b65k_fibre_five_map]; ring

theorem b65k_fibre_seven : b65k_fibrePoly (-7) = (Polynomial.C (-7) * Polynomial.X^0 + Polynomial.C (21/2) * Polynomial.X^1 + Polynomial.C (123/8) * Polynomial.X^2 + Polynomial.C (-185/8) * Polynomial.X^3 + Polynomial.C (33/8) * Polynomial.X^4 + Polynomial.C (9/8) * Polynomial.X^5 + Polynomial.C 1 * Polynomial.X^6) := by
  apply IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)
  simp only [b65k_fibrePoly, map_sub, map_inv₀, map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat, map_neg, map_div₀, map_one]
  ring

theorem b65k_fibre_seven_ne : b65k_fibrePoly (-7) ≠ 0 := by
  intro h
  have := congrArg (fun p : Polynomial ℚ => p.coeff 6) h
  rw [b65k_fibre_seven] at this
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul] at this

theorem b65k_fibre_seven_mapne : algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ))).2 b65k_fibre_seven_ne

theorem b65k_fibre_seven_map : algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) =
    ((-7) + (21/2) * 𝕩 + (123/8) * 𝕩^2 + (-185/8) * 𝕩^3 + (33/8) * 𝕩^4 + (9/8) * 𝕩^5 + 𝕩^6) := by
  rw [b65k_fibre_seven]
  simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat, map_neg, map_div₀, map_one]
  ring

theorem b65k_fibre_seven_deriv : algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)).derivative =
    ((21/2) + (123/4) * 𝕩 + (-555/8) * 𝕩^2 + (33/2) * 𝕩^3 + (45/8) * 𝕩^4 + 6 * 𝕩^5) := by
  rw [b65k_fibre_seven]
  simp only [map_add, Polynomial.derivative_C_mul_X_pow]
  simp only [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat, map_neg, map_div₀, map_one, map_natCast]
  norm_num

theorem b65k_companion_seven : b65k_companion (-7) = Matrix.of ![![0, 0, 0, 0, 0, 7], ![1, 0, 0, 0, 0, (-21/2)], ![0, 1, 0, 0, 0, (-123/8)], ![0, 0, 1, 0, 0, (185/8)], ![0, 0, 0, 1, 0, (-33/8)], ![0, 0, 0, 0, 1, (-9/8)]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [b65k_companion, b65k_fibre_seven, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul]

theorem b65k_trace_seven_0 : Matrix.trace (b65k_companion (-7) ^ 0) = 6 := by
  rw [b65k_companion_seven]
  decide +kernel

theorem b65k_trace_seven_1 : Matrix.trace (b65k_companion (-7) ^ 1) = (-9/8) := by
  rw [b65k_companion_seven]
  decide +kernel

theorem b65k_trace_seven_2 : Matrix.trace (b65k_companion (-7) ^ 2) = (-447/64) := by
  rw [b65k_companion_seven]
  decide +kernel

theorem b65k_trace_seven_3 : Matrix.trace (b65k_companion (-7) ^ 3) = (41919/512) := by
  rw [b65k_companion_seven]
  decide +kernel

theorem b65k_trace_seven_4 : Matrix.trace (b65k_companion (-7) ^ 4) = (-617727/4096) := by
  rw [b65k_companion_seven]
  decide +kernel

theorem b65k_trace_seven_5 : Matrix.trace (b65k_companion (-7) ^ 5) = (-11953089/32768) := by
  rw [b65k_companion_seven]
  decide +kernel

theorem b65k_rootSum_seven_0 : b65k_rootSum (-7) 0 = ((21/2) + (123/4) * 𝕩 + (-555/8) * 𝕩^2 + (33/2) * 𝕩^3 + (45/8) * 𝕩^4 + 6 * 𝕩^5) / algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) := by
  have hP := b65k_fibre_seven_mapne
  rw [eq_div_iff hP, b65k_rootSum, b65k_fibre_seven_deriv]
  simp only [Finset.sum_range_zero, sub_zero]
  field_simp

theorem b65k_rootSum_seven_1 : b65k_rootSum (-7) 1 = (42 + (-105/2) * 𝕩 + (-123/2) * 𝕩^2 + (555/8) * 𝕩^3 + (-33/4) * 𝕩^4 + (-9/8) * 𝕩^5) / algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) := by
  have hP := b65k_fibre_seven_mapne
  rw [eq_div_iff hP, b65k_rootSum, b65k_fibre_seven_deriv]
  simp only [Finset.sum_range_succ, b65k_trace_seven_0]
  simp only [Finset.sum_range_zero, map_ofNat]
  field_simp
  all_goals rw [b65k_fibre_seven_map]; ring

theorem b65k_rootSum_seven_2 : b65k_rootSum (-7) 2 = ((-63/8) + (861/16) * 𝕩 + (-2253/64) * 𝕩^2 + (-5601/64) * 𝕩^3 + (4737/64) * 𝕩^4 + (-447/64) * 𝕩^5) / algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) := by
  have hP := b65k_fibre_seven_mapne
  rw [eq_div_iff hP, b65k_rootSum, b65k_fibre_seven_deriv]
  simp only [Finset.sum_range_succ, b65k_trace_seven_0, b65k_trace_seven_1]
  simp only [Finset.sum_range_zero, map_ofNat, map_neg, map_div₀]
  field_simp
  all_goals rw [b65k_fibre_seven_map]; ring

theorem b65k_rootSum_seven_3 : b65k_rootSum (-7) 3 = ((-3129/64) + (8379/128) * 𝕩 + (82533/512) * 𝕩^2 + (-100719/512) * 𝕩^3 + (-30057/512) * 𝕩^4 + (41919/512) * 𝕩^5) / algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) := by
  have hP := b65k_fibre_seven_mapne
  rw [eq_div_iff hP, b65k_rootSum, b65k_fibre_seven_deriv]
  simp only [Finset.sum_range_succ, b65k_trace_seven_0, b65k_trace_seven_1, b65k_trace_seven_2]
  simp only [Finset.sum_range_zero, map_ofNat, map_neg, map_div₀]
  field_simp
  all_goals rw [b65k_fibre_seven_map]; ring

theorem b65k_rootSum_seven_4 : b65k_rootSum (-7) 4 = ((293433/512) + (-930363/1024) * 𝕩 + (-4887909/4096) * 𝕩^2 + (8415279/4096) * 𝕩^3 + (-2189079/4096) * 𝕩^4 + (-617727/4096) * 𝕩^5) / algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) := by
  have hP := b65k_fibre_seven_mapne
  rw [eq_div_iff hP, b65k_rootSum, b65k_fibre_seven_deriv]
  simp only [Finset.sum_range_succ, b65k_trace_seven_0, b65k_trace_seven_1, b65k_trace_seven_2, b65k_trace_seven_3]
  simp only [Finset.sum_range_zero, map_ofNat, map_neg, map_div₀]
  field_simp
  all_goals rw [b65k_fibre_seven_map]; ring

theorem b65k_rootSum_seven_5 : b65k_rootSum (-7) 5 = ((-4324089/4096) + (17667195/8192) * 𝕩 + (46208805/32768) * 𝕩^2 + (-153382767/32768) * 𝕩^3 + (87707223/32768) * 𝕩^4 + (-11953089/32768) * 𝕩^5) / algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) := by
  have hP := b65k_fibre_seven_mapne
  rw [eq_div_iff hP, b65k_rootSum, b65k_fibre_seven_deriv]
  simp only [Finset.sum_range_succ, b65k_trace_seven_0, b65k_trace_seven_1, b65k_trace_seven_2, b65k_trace_seven_3, b65k_trace_seven_4]
  simp only [Finset.sum_range_zero, map_ofNat, map_neg, map_div₀]
  field_simp
  all_goals rw [b65k_fibre_seven_map]; ring

theorem b65k_rBase_0_0 : b65k_rBase 0 0 = ((-21767823360/378301) * 𝕩 + (36279705600/378301) * 𝕩^2 + (-604661760/378301) * 𝕩^3 + (-19349176320/378301) * 𝕩^4 + (3627970560/378301) * 𝕩^5 + (2418647040/378301) * 𝕩^6 + (-604661760/378301) * 𝕩^7) / (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  rw [eq_div_iff hEr, b65k_rBase, b65k_principal, b65k_rKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder]
  norm_num [b65k_rKernelLit]
  field_simp
  ring

theorem b65k_rBase_0_1 : b65k_rBase 0 1 = ((-604661760/22253) * 𝕩 + (1007769600/22253) * 𝕩^2 + (-16796160/22253) * 𝕩^3 + (-537477120/22253) * 𝕩^4 + (100776960/22253) * 𝕩^5 + (67184640/22253) * 𝕩^6 + (-16796160/22253) * 𝕩^7) / (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  rw [eq_div_iff hEr, b65k_rBase, b65k_principal, b65k_rKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder]
  norm_num [b65k_rKernelLit]
  field_simp
  ring

theorem b65k_rBase_0_2 : b65k_rBase 0 2 = (108 * 𝕩 + (-180) * 𝕩^2 + 3 * 𝕩^3 + 96 * 𝕩^4 + (-18) * 𝕩^5 + (-12) * 𝕩^6 + 3 * 𝕩^7) / (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  rw [eq_div_iff hEr, b65k_rBase, b65k_principal, b65k_rKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder]
  norm_num [b65k_rKernelLit]
  field_simp
  ring

theorem b65k_rBase_0_3 : b65k_rBase 0 3 = 0 := by
  rw [b65k_rBase, b65k_principal, b65k_rKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder]
  norm_num [b65k_rKernelLit]

theorem b65k_rBase_1_0 : b65k_rBase 1 0 = ((-21767823360/378301) * 𝕩 + (21767823360/378301) * 𝕩^2 + (9069926400/378301) * 𝕩^3 + (-10077696000/378301) * 𝕩^4 + (1209323520/378301) * 𝕩^6 + (-201553920/378301) * 𝕩^7) / (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  rw [eq_div_iff hEr, b65k_rBase, b65k_principal, b65k_rKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder]
  norm_num [b65k_rKernelLit]
  field_simp
  ring

theorem b65k_rBase_1_1 : b65k_rBase 1 1 = ((-604661760/22253) * 𝕩 + (604661760/22253) * 𝕩^2 + (251942400/22253) * 𝕩^3 + (-279936000/22253) * 𝕩^4 + (33592320/22253) * 𝕩^6 + (-5598720/22253) * 𝕩^7) / (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  rw [eq_div_iff hEr, b65k_rBase, b65k_principal, b65k_rKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder]
  norm_num [b65k_rKernelLit]
  field_simp
  ring

theorem b65k_rBase_1_2 : b65k_rBase 1 2 = (108 * 𝕩 + (-108) * 𝕩^2 + (-45) * 𝕩^3 + 50 * 𝕩^4 + (-6) * 𝕩^6 + 𝕩^7) / (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  rw [eq_div_iff hEr, b65k_rBase, b65k_principal, b65k_rKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder]
  norm_num [b65k_rKernelLit]
  field_simp
  ring

theorem b65k_rBase_1_3 : b65k_rBase 1 3 = 0 := by
  rw [b65k_rBase, b65k_principal, b65k_rKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder]
  norm_num [b65k_rKernelLit]

theorem b65k_rBase_2_0 : b65k_rBase 2 0 = ((-21767823360/378301) * 𝕩 + (54419558400/378301) * 𝕩^2 + (-3627970560/34391) * 𝕩^3 + (806215680/378301) * 𝕩^4 + (9674588160/378301) * 𝕩^5 + (-3627970560/378301) * 𝕩^6 + (403107840/378301) * 𝕩^7) / (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  rw [eq_div_iff hEr, b65k_rBase, b65k_principal, b65k_rKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder]
  norm_num [b65k_rKernelLit]
  field_simp
  ring

theorem b65k_rBase_2_1 : b65k_rBase 2 1 = ((-604661760/22253) * 𝕩 + (1511654400/22253) * 𝕩^2 + (-100776960/2023) * 𝕩^3 + (22394880/22253) * 𝕩^4 + (268738560/22253) * 𝕩^5 + (-100776960/22253) * 𝕩^6 + (11197440/22253) * 𝕩^7) / (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  rw [eq_div_iff hEr, b65k_rBase, b65k_principal, b65k_rKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder]
  norm_num [b65k_rKernelLit]
  field_simp
  ring

theorem b65k_rBase_2_2 : b65k_rBase 2 2 = (108 * 𝕩 + (-270) * 𝕩^2 + 198 * 𝕩^3 + (-4) * 𝕩^4 + (-48) * 𝕩^5 + 18 * 𝕩^6 + (-2) * 𝕩^7) / (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  rw [eq_div_iff hEr, b65k_rBase, b65k_principal, b65k_rKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder]
  norm_num [b65k_rKernelLit]
  field_simp
  ring

theorem b65k_rBase_2_3 : b65k_rBase 2 3 = 0 := by
  rw [b65k_rBase, b65k_principal, b65k_rKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder]
  norm_num [b65k_rKernelLit]

theorem b65k_qBase_0_0 : b65k_qBase 0 0 =
    ((0) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((-2648107/2239488) * 𝕩^2 + (97979959/22394880) * 𝕩^3 + (-526973293/67184640) * 𝕩^4 + (28633980991/2418647040) * 𝕩^5 + (-2338278481/179159040) * 𝕩^6 + (2364759551/537477120) * 𝕩^7 + (8773178491/1612431360) * 𝕩^8 + (-23311285921/4837294080) * 𝕩^9 + (1411441031/4837294080) * 𝕩^10 + (3619962269/4837294080) * 𝕩^11 + (-950670413/4837294080) * 𝕩^12 + (-29129177/4837294080) * 𝕩^13 + (2648107/604661760) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((18536749/22394880) * 𝕩^2 + (34425391/44789760) * 𝕩^3 + (-1321405393/134369280) * 𝕩^4 + (69563122783/4837294080) * 𝕩^5 + (-1289628109/358318080) * 𝕩^6 + (-6056220709/1074954240) * 𝕩^7 + (9376946887/3224862720) * 𝕩^8 + (5002274123/9674588160) * 𝕩^9 + (-2306501197/9674588160) * 𝕩^10 + (-1051298479/9674588160) * 𝕩^11 + (-18536749/1934917632) * 𝕩^12 + (256866379/9674588160) * 𝕩^13 + (-2648107/604661760) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5)) / ((𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [eq_div_iff (by positivity), b65k_qBase, b65k_principal, b65k_qKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  norm_num only [b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  norm_num [b65k_qKernelLit, b65k_left, b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  field_simp
  ring

theorem b65k_qBase_0_1 : b65k_qBase 0 1 =
    (((155771/1555200) * 𝕩^2 + (155771/3110400) * 𝕩^3 + (-155771/583200) * 𝕩^4 + (2025023/20995200) * 𝕩^5 + (155771/3499200) * 𝕩^6 + (-155771/5598720) * 𝕩^7 + (155771/41990400) * 𝕩^8) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((-155771/116640) * 𝕩^2 + (5763527/1166400) * 𝕩^3 + (-30998429/3499200) * 𝕩^4 + (1684351823/125971200) * 𝕩^5 + (-137545793/9331200) * 𝕩^6 + (139103503/27993600) * 𝕩^7 + (516069323/83980800) * 𝕩^8 + (-1371252113/251942400) * 𝕩^9 + (83025943/251942400) * 𝕩^10 + (212938957/251942400) * 𝕩^11 + (-55921789/251942400) * 𝕩^12 + (-1713481/251942400) * 𝕩^13 + (155771/31492800) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((7632779/4665600) * 𝕩^2 + (14175161/9331200) * 𝕩^3 + (-544108103/27993600) * 𝕩^4 + (28643638793/1007769600) * 𝕩^5 + (-531023339/74649600) * 𝕩^6 + (-2493737939/223948800) * 𝕩^7 + (3861095777/671846400) * 𝕩^8 + (2059759933/2015539200) * 𝕩^9 + (-949735787/2015539200) * 𝕩^10 + (-432887609/2015539200) * 𝕩^11 + (-7632779/403107840) * 𝕩^12 + (105768509/2015539200) * 𝕩^13 + (-1090397/125971200) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5)) / ((𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [eq_div_iff (by positivity), b65k_qBase, b65k_principal, b65k_qKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  norm_num only [b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  norm_num [b65k_qKernelLit, b65k_left, b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  field_simp
  ring

theorem b65k_qBase_0_2 : b65k_qBase 0 2 =
    (((126/5) * 𝕩^2 + (63/5) * 𝕩^3 + (-336/5) * 𝕩^4 + (364/15) * 𝕩^5 + (56/5) * 𝕩^6 + (-7) * 𝕩^7 + (14/15) * 𝕩^8) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    (924 * 𝕩^2 + (-17094/5) * 𝕩^3 + (30646/5) * 𝕩^4 + (-832601/90) * 𝕩^5 + (203973/20) * 𝕩^6 + (-68761/20) * 𝕩^7 + (-255101/60) * 𝕩^8 + (677831/180) * 𝕩^9 + (-41041/180) * 𝕩^10 + (-105259/180) * 𝕩^11 + (27643/180) * 𝕩^12 + (847/180) * 𝕩^13 + (-154/45) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((-2352/5) * 𝕩^2 + (-2184/5) * 𝕩^3 + (27944/5) * 𝕩^4 + (-367766/45) * 𝕩^5 + (10227/5) * 𝕩^6 + (16009/5) * 𝕩^7 + (-24787/15) * 𝕩^8 + (-13223/45) * 𝕩^9 + (6097/45) * 𝕩^10 + (2779/45) * 𝕩^11 + (49/9) * 𝕩^12 + (-679/45) * 𝕩^13 + (112/45) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5)) / ((𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [eq_div_iff (by positivity), b65k_qBase, b65k_principal, b65k_qKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  norm_num only [b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  norm_num [b65k_qKernelLit, b65k_left, b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  field_simp
  ring

theorem b65k_qBase_0_3 : b65k_qBase 0 3 =
    (((-22253/311040) * 𝕩 + (1846999/9331200) * 𝕩^2 + (-823361/6998400) * 𝕩^3 + (-4517359/55987200) * 𝕩^4 + (6920683/83980800) * 𝕩^5 + (-22253/27993600) * 𝕩^6 + (-22253/1866240) * 𝕩^7 + (378301/167961600) * 𝕩^8) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((4161311/11197440) * 𝕩^2 + (-153968507/111974400) * 𝕩^3 + (828100889/335923200) * 𝕩^4 + (-44996255843/12093235200) * 𝕩^5 + (3674437613/895795200) * 𝕩^6 + (-3716050723/2687385600) * 𝕩^7 + (-13786423343/8062156800) * 𝕩^8 + (36632020733/24186470400) * 𝕩^9 + (-2217978763/24186470400) * 𝕩^10 + (-5688512137/24186470400) * 𝕩^11 + (1493910649/24186470400) * 𝕩^12 + (45774421/24186470400) * 𝕩^13 + (-4161311/3023308800) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((18536749/111974400) * 𝕩^2 + (34425391/223948800) * 𝕩^3 + (-1321405393/671846400) * 𝕩^4 + (69563122783/24186470400) * 𝕩^5 + (-1289628109/1791590400) * 𝕩^6 + (-6056220709/5374771200) * 𝕩^7 + (9376946887/16124313600) * 𝕩^8 + (5002274123/48372940800) * 𝕩^9 + (-2306501197/48372940800) * 𝕩^10 + (-1051298479/48372940800) * 𝕩^11 + (-18536749/9674588160) * 𝕩^12 + (256866379/48372940800) * 𝕩^13 + (-2648107/3023308800) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5)) / ((𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [eq_div_iff (by positivity), b65k_qBase, b65k_principal, b65k_qKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  norm_num only [b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  norm_num [b65k_qKernelLit, b65k_left, b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  field_simp
  ring

theorem b65k_qBase_1_0 : b65k_qBase 1 0 =
    ((0) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((29311896383/559872000) * 𝕩^2 + (-30620061241/248832000) * 𝕩^3 + (72423078343/33592320000) * 𝕩^4 + (227641401433061/1209323520000) * 𝕩^5 + (-5126790762247/48372940800) * 𝕩^6 + (-88072350006949/1209323520000) * 𝕩^7 + (75591292094549/1209323520000) * 𝕩^8 + (629033984887/80621568000) * 𝕩^9 + (-15109651011917/1209323520000) * 𝕩^10 + (126651013489/241864704000) * 𝕩^11 + (1060855497163/1209323520000) * 𝕩^12 + (-17395414883/201553920000) * 𝕩^13 + (-283347449/25194240000) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((-205183274681/5598720000) * 𝕩^2 + (297755799187/2488320000) * 𝕩^3 + (-6197044391153/67184640000) * 𝕩^4 + (-153602622973723/2418647040000) * 𝕩^5 + (215809447508501/2418647040000) * 𝕩^6 + (26521080248663/2418647040000) * 𝕩^7 + (-76332057658087/2418647040000) * 𝕩^8 + (-815434236617/806215680000) * 𝕩^9 + (13453265379631/2418647040000) * 𝕩^10 + (-12554675287/2418647040000) * 𝕩^11 + (-1146680645033/2418647040000) * 𝕩^12 + (7226684003/403107840000) * 𝕩^13 + (283347449/25194240000) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5)) / ((𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [eq_div_iff (by positivity), b65k_qBase, b65k_principal, b65k_qKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  norm_num only [b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  norm_num [b65k_qKernelLit, b65k_left, b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  field_simp
  ring

theorem b65k_qBase_1_1 : b65k_qBase 1 1 =
    (((-1724229199/388800000) * 𝕩^2 + (1590889223/259200000) * 𝕩^3 + (-824184361/1166400000) * 𝕩^4 + (-3898480817/2624400000) * 𝕩^5 + (1324209271/2624400000) * 𝕩^6 + (-124149487/20995200000) * 𝕩^7 + (-16667497/1749600000) * 𝕩^8) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((1724229199/29160000) * 𝕩^2 + (-1801180073/12960000) * 𝕩^3 + (4260181079/1749600000) * 𝕩^4 + (13390670672533/62985600000) * 𝕩^5 + (-301575927191/2519424000) * 𝕩^6 + (-5180726470997/62985600000) * 𝕩^7 + (4446546593797/62985600000) * 𝕩^8 + (37001999111/4199040000) * 𝕩^9 + (-888803000701/62985600000) * 𝕩^10 + (7450059617/12597120000) * 𝕩^11 + (62403264539/62985600000) * 𝕩^12 + (-1023259699/10497600000) * 𝕩^13 + (-16667497/1312200000) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((-84487230751/1166400000) * 𝕩^2 + (122605329077/518400000) * 𝕩^3 + (-2551724161063/13996800000) * 𝕩^4 + (-63248138871533/503884800000) * 𝕩^5 + (88862713679971/503884800000) * 𝕩^6 + (10920444808273/503884800000) * 𝕩^7 + (-31430847270977/503884800000) * 𝕩^8 + (-335767038607/167961600000) * 𝕩^9 + (5539579862201/503884800000) * 𝕩^10 + (-5169572177/503884800000) * 𝕩^11 + (-472162618543/503884800000) * 𝕩^12 + (2975693413/83980800000) * 𝕩^13 + (116672479/5248800000) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5)) / ((𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [eq_div_iff (by positivity), b65k_qBase, b65k_principal, b65k_qKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  norm_num only [b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  norm_num [b65k_qKernelLit, b65k_left, b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  field_simp
  ring

theorem b65k_qBase_1_2 : b65k_qBase 1 2 =
    (((-697347/625) * 𝕩^2 + (1930257/1250) * 𝕩^3 + (-111111/625) * 𝕩^4 + (-700756/1875) * 𝕩^5 + (238028/1875) * 𝕩^6 + (-5579/3750) * 𝕩^7 + (-1498/625) * 𝕩^8) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((-5113878/125) * 𝕩^2 + (24039477/250) * 𝕩^3 + (-2105873/1250) * 𝕩^4 + (-6619214371/45000) * 𝕩^5 + (149073617/1800) * 𝕩^6 + (2560912739/45000) * 𝕩^7 + (-2197996339/45000) * 𝕩^8 + (-18290657/3000) * 𝕩^9 + (439348987/45000) * 𝕩^10 + (-3682679/9000) * 𝕩^11 + (-30846893/45000) * 𝕩^12 + (505813/7500) * 𝕩^13 + (16478/1875) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((13017144/625) * 𝕩^2 + (-42502698/625) * 𝕩^3 + (32762506/625) * 𝕩^4 + (406032823/11250) * 𝕩^5 + (-570470201/11250) * 𝕩^6 + (-70105763/11250) * 𝕩^7 + (201775987/11250) * 𝕩^8 + (2155517/3750) * 𝕩^9 + (-35562331/11250) * 𝕩^10 + (33187/11250) * 𝕩^11 + (3031133/11250) * 𝕩^12 + (-19103/1875) * 𝕩^13 + (-11984/1875) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5)) / ((𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [eq_div_iff (by positivity), b65k_qBase, b65k_principal, b65k_qKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  norm_num only [b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  norm_num [b65k_qKernelLit, b65k_left, b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  field_simp
  ring

theorem b65k_qBase_1_3 : b65k_qBase 1 3 =
    (((-155771/248832) * 𝕩 + (316593431/583200000) * 𝕩^2 + (20357645231/27993600000) * 𝕩^3 + (-2141606467/3499200000) * 𝕩^4 + (-6931831753/41990400000) * 𝕩^5 + (2859933307/20995200000) * 𝕩^6 + (218546713/83980800000) * 𝕩^7 + (-40478207/6998400000) * 𝕩^8) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((-46061551459/2799360000) * 𝕩^2 + (48117239093/1244160000) * 𝕩^3 + (-113807694539/167961600000) * 𝕩^4 + (-357722202251953/6046617600000) * 𝕩^5 + (8056385483531/241864704000) * 𝕩^6 + (138399407153777/6046617600000) * 𝕩^7 + (-118786316148577/6046617600000) * 𝕩^8 + (-988481976251/403107840000) * 𝕩^9 + (23743737304441/6046617600000) * 𝕩^10 + (-199023021197/1209323520000) * 𝕩^11 + (-1667058638399/6046617600000) * 𝕩^12 + (27335651959/1007769600000) * 𝕩^13 + (445260277/125971200000) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((-205183274681/27993600000) * 𝕩^2 + (297755799187/12441600000) * 𝕩^3 + (-6197044391153/335923200000) * 𝕩^4 + (-153602622973723/12093235200000) * 𝕩^5 + (215809447508501/12093235200000) * 𝕩^6 + (26521080248663/12093235200000) * 𝕩^7 + (-76332057658087/12093235200000) * 𝕩^8 + (-815434236617/4031078400000) * 𝕩^9 + (13453265379631/12093235200000) * 𝕩^10 + (-12554675287/12093235200000) * 𝕩^11 + (-1146680645033/12093235200000) * 𝕩^12 + (7226684003/2015539200000) * 𝕩^13 + (283347449/125971200000) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5)) / ((𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [eq_div_iff (by positivity), b65k_qBase, b65k_principal, b65k_qKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  norm_num only [b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  norm_num [b65k_qKernelLit, b65k_left, b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  field_simp
  ring

theorem b65k_qBase_2_0 : b65k_qBase 2 0 =
    ((0) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((-323696655359/4478976000) * 𝕩^2 + (1212030629579/5971968000) * 𝕩^3 + (-11979180729439/268738560000) * 𝕩^4 + (-3701562306541253/9674588160000) * 𝕩^5 + (161178232147471/386983526400) * 𝕩^6 + (-200213013523523/9674588160000) * 𝕩^7 + (-1687581156307277/9674588160000) * 𝕩^8 + (143212065466547/1934917632000) * 𝕩^9 + (118594049961541/9674588160000) * 𝕩^10 + (-25544092948297/1934917632000) * 𝕩^11 + (17684966846701/9674588160000) * 𝕩^12 + (1421268156077/4837294080000) * 𝕩^13 + (-4271396591/67184640000) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((2265876587513/44789760000) * 𝕩^2 + (-11937610745753/59719680000) * 𝕩^3 + (139905496068569/537477120000) * 𝕩^4 + (-1309710036378821/19349176320000) * 𝕩^5 + (-2046630908695373/19349176320000) * 𝕩^6 + (1043650330231201/19349176320000) * 𝕩^7 + (447006004087951/19349176320000) * 𝕩^8 + (-197328224016077/19349176320000) * 𝕩^9 + (-153210756099863/19349176320000) * 𝕩^10 + (60781716623551/19349176320000) * 𝕩^11 + (16809089567809/19349176320000) * 𝕩^12 + (-5134020094357/9674588160000) * 𝕩^13 + (4271396591/67184640000) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5)) / ((𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [eq_div_iff (by positivity), b65k_qBase, b65k_principal, b65k_qKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  norm_num only [b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  norm_num [b65k_qKernelLit, b65k_left, b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  field_simp
  ring

theorem b65k_qBase_2_1 : b65k_qBase 2 1 =
    (((19040979727/3110400000) * 𝕩^2 + (-25071186679/2073600000) * 𝕩^3 + (59744876653/9331200000) * 𝕩^4 + (17730010991/20995200000) * 𝕩^5 + (-37131600583/20995200000) * 𝕩^6 + (91403463151/167961600000) * 𝕩^7 + (-251258623/4665600000) * 𝕩^8) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((-19040979727/233280000) * 𝕩^2 + (71295919387/311040000) * 𝕩^3 + (-704657689967/13996800000) * 𝕩^4 + (-217738959208309/503884800000) * 𝕩^5 + (9481072479263/20155392000) * 𝕩^6 + (-11777236089619/503884800000) * 𝕩^7 + (-99269479782781/503884800000) * 𝕩^8 + (8424239145091/100776960000) * 𝕩^9 + (6976120585973/503884800000) * 𝕩^10 + (-1502593702841/100776960000) * 𝕩^11 + (1040292167453/503884800000) * 𝕩^12 + (83604009181/251942400000) * 𝕩^13 + (-251258623/3499200000) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((933008006623/9331200000) * 𝕩^2 + (-4915486777663/12441600000) * 𝕩^3 + (57608145439999/111974400000) * 𝕩^4 + (-539292367920691/4031078400000) * 𝕩^5 + (-842730374168683/4031078400000) * 𝕩^6 + (429738371271671/4031078400000) * 𝕩^7 + (184061295800921/4031078400000) * 𝕩^8 + (-81252798124267/4031078400000) * 𝕩^9 + (-63086781923473/4031078400000) * 𝕩^10 + (25027765668521/4031078400000) * 𝕩^11 + (6921389822039/4031078400000) * 𝕩^12 + (-2114008274147/2015539200000) * 𝕩^13 + (1758810361/13996800000) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5)) / ((𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [eq_div_iff (by positivity), b65k_qBase, b65k_principal, b65k_qKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  norm_num only [b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  norm_num [b65k_qKernelLit, b65k_left, b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  field_simp
  ring

theorem b65k_qBase_2_2 : b65k_qBase 2 2 =
    (((7700931/5000) * 𝕩^2 + (-30419361/10000) * 𝕩^3 + (8054403/5000) * 𝕩^4 + (796747/3750) * 𝕩^5 + (-1668611/3750) * 𝕩^6 + (4107467/30000) * 𝕩^7 + (-33873/2500) * 𝕩^8) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((28236747/500) * 𝕩^2 + (-317184021/2000) * 𝕩^3 + (348323129/10000) * 𝕩^4 + (107631714883/360000) * 𝕩^5 + (-4686639881/14400) * 𝕩^6 + (5821668853/360000) * 𝕩^7 + (49070429947/360000) * 𝕩^8 + (-4164230917/72000) * 𝕩^9 + (-3448403651/360000) * 𝕩^10 + (742755167/72000) * 𝕩^11 + (-514232411/360000) * 𝕩^12 + (-41326747/180000) * 𝕩^13 + (124201/2500) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((-17968839/625) * 𝕩^2 + (284002677/2500) * 𝕩^3 + (-369825869/2500) * 𝕩^4 + (3462084521/90000) * 𝕩^5 + (5410059473/90000) * 𝕩^6 + (-2758782901/90000) * 𝕩^7 + (-1181614651/90000) * 𝕩^8 + (521616977/90000) * 𝕩^9 + (404996963/90000) * 𝕩^10 + (-160670251/90000) * 𝕩^11 + (-44433109/90000) * 𝕩^12 + (13571257/45000) * 𝕩^13 + (-22582/625) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5)) / ((𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [eq_div_iff (by positivity), b65k_qBase, b65k_principal, b65k_qKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  norm_num only [b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  norm_num [b65k_qKernelLit, b65k_left, b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  field_simp
  ring

theorem b65k_qBase_2_3 : b65k_qBase 2 3 =
    (((3582733/3317760) * 𝕩 + (-3734209171/1555200000) * 𝕩^2 + (66989162779/74649600000) * 𝕩^3 + (239909593/172800000) * 𝕩^4 + (-350320678631/335923200000) * 𝕩^5 + (-12296718511/167961600000) * 𝕩^6 + (123799380551/671846400000) * 𝕩^7 + (-610199513/18662400000) * 𝕩^8) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((508666172707/22394880000) * 𝕩^2 + (-1904619560767/29859840000) * 𝕩^3 + (18824426860547/1343692800000) * 𝕩^4 + (5816740767421969/48372940800000) * 𝕩^5 + (-253280079088883/1934917632000) * 𝕩^6 + (314620449822679/48372940800000) * 𝕩^7 + (2651913245625721/48372940800000) * 𝕩^8 + (-225047531447431/9674588160000) * 𝕩^9 + (-186362078510993/48372940800000) * 𝕩^10 + (40140717490181/9674588160000) * 𝕩^11 + (-27790662187673/48372940800000) * 𝕩^12 + (-2233421388121/24186470400000) * 𝕩^13 + (6712194643/335923200000) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7)) +
    ((2265876587513/223948800000) * 𝕩^2 + (-11937610745753/298598400000) * 𝕩^3 + (139905496068569/2687385600000) * 𝕩^4 + (-1309710036378821/96745881600000) * 𝕩^5 + (-2046630908695373/96745881600000) * 𝕩^6 + (1043650330231201/96745881600000) * 𝕩^7 + (447006004087951/96745881600000) * 𝕩^8 + (-197328224016077/96745881600000) * 𝕩^9 + (-153210756099863/96745881600000) * 𝕩^10 + (60781716623551/96745881600000) * 𝕩^11 + (16809089567809/96745881600000) * 𝕩^12 + (-5134020094357/48372940800000) * 𝕩^13 + (4271396591/335923200000) * 𝕩^14) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5)) / ((𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly 5) * algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_fibrePoly (-7))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [eq_div_iff (by positivity), b65k_qBase, b65k_principal, b65k_qKernel_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, b65k_fixed, b65k_poleIndex,
    b65k_poleOrder, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  norm_num only [b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  norm_num [b65k_qKernelLit, b65k_left, b65k_rootSum_five_0, b65k_rootSum_five_1, b65k_rootSum_five_2, b65k_rootSum_five_3, b65k_rootSum_five_4, b65k_rootSum_five_5, b65k_rootSum_seven_0, b65k_rootSum_seven_1, b65k_rootSum_seven_2, b65k_rootSum_seven_3, b65k_rootSum_seven_4, b65k_rootSum_seven_5]
  field_simp
  ring

theorem b65k_product_0_0 : b65k_baseProduct 0 0 = (567 * 𝕩 + (-5481/4) * 𝕩^2 + (5733/4) * 𝕩^3 + (-11025/16) * 𝕩^4 + (-7245/16) * 𝕩^5 + (5103/8) * 𝕩^6 + (-441/8) * 𝕩^7 + (-1449/16) * 𝕩^8 + (315/16) * 𝕩^9) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [b65k_baseProduct, b65k_baseDenominator]
  simp only [map_mul, RatFunc.algebraMap_X, Fin.sum_univ_four]
  rw [b65k_qBase_0_0, b65k_qBase_0_1, b65k_qBase_0_2, b65k_qBase_0_3, b65k_rBase_0_0, b65k_rBase_0_1, b65k_rBase_0_2, b65k_rBase_0_3]
  field_simp
  rw [b65k_fibre_five_map, b65k_fibre_seven_map]
  ring

theorem b65k_product_0_1 : b65k_baseProduct 0 1 = ((19845/4) * 𝕩 + (-3515211/125) * 𝕩^2 + (68218857/2000) * 𝕩^3 + (4772439/2000) * 𝕩^4 + (-7379757/400) * 𝕩^5 + (708561/200) * 𝕩^6 + (4392927/2000) * 𝕩^7 + (-1299249/2000) * 𝕩^8 + (49077/2000) * 𝕩^9) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [b65k_baseProduct, b65k_baseDenominator]
  simp only [map_mul, RatFunc.algebraMap_X, Fin.sum_univ_four]
  rw [b65k_qBase_1_0, b65k_qBase_1_1, b65k_qBase_1_2, b65k_qBase_1_3, b65k_rBase_0_0, b65k_rBase_0_1, b65k_rBase_0_2, b65k_rBase_0_3]
  field_simp
  rw [b65k_fibre_five_map, b65k_fibre_seven_map]
  ring

theorem b65k_product_0_2 : b65k_baseProduct 0 2 = ((-273861/32) * 𝕩 + (52764453/1000) * 𝕩^2 + (-1364041161/16000) * 𝕩^3 + (451308753/16000) * 𝕩^4 + (112224861/3200) * 𝕩^5 + (-38394153/1600) * 𝕩^6 + (-16658271/16000) * 𝕩^7 + (54172377/16000) * 𝕩^8 + (-9265221/16000) * 𝕩^9) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [b65k_baseProduct, b65k_baseDenominator]
  simp only [map_mul, RatFunc.algebraMap_X, Fin.sum_univ_four]
  rw [b65k_qBase_2_0, b65k_qBase_2_1, b65k_qBase_2_2, b65k_qBase_2_3, b65k_rBase_0_0, b65k_rBase_0_1, b65k_rBase_0_2, b65k_rBase_0_3]
  field_simp
  rw [b65k_fibre_five_map, b65k_fibre_seven_map]
  ring

theorem b65k_product_1_0 : b65k_baseProduct 1 0 = (567 * 𝕩 + (-3969/4) * 𝕩^2 + (3591/4) * 𝕩^3 + (-4305/16) * 𝕩^4 + (-7875/16) * 𝕩^5 + (2373/8) * 𝕩^6 + (231/8) * 𝕩^7 + (-693/16) * 𝕩^8 + (105/16) * 𝕩^9) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [b65k_baseProduct, b65k_baseDenominator]
  simp only [map_mul, RatFunc.algebraMap_X, Fin.sum_univ_four]
  rw [b65k_qBase_0_0, b65k_qBase_0_1, b65k_qBase_0_2, b65k_qBase_0_3, b65k_rBase_1_0, b65k_rBase_1_1, b65k_rBase_1_2, b65k_rBase_1_3]
  field_simp
  rw [b65k_fibre_five_map, b65k_fibre_seven_map]
  ring

theorem b65k_product_1_1 : b65k_baseProduct 1 1 = ((19845/4) * 𝕩 + (-6203547/250) * 𝕩^2 + (37338273/2000) * 𝕩^3 + (19371093/2000) * 𝕩^4 + (-3823701/400) * 𝕩^5 + (2667/20) * 𝕩^6 + (2297757/2000) * 𝕩^7 + (-465801/2000) * 𝕩^8 + (16359/2000) * 𝕩^9) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [b65k_baseProduct, b65k_baseDenominator]
  simp only [map_mul, RatFunc.algebraMap_X, Fin.sum_univ_four]
  rw [b65k_qBase_1_0, b65k_qBase_1_1, b65k_qBase_1_2, b65k_qBase_1_3, b65k_rBase_1_0, b65k_rBase_1_1, b65k_rBase_1_2, b65k_rBase_1_3]
  field_simp
  rw [b65k_fibre_five_map, b65k_fibre_seven_map]
  ring

theorem b65k_product_1_2 : b65k_baseProduct 1 2 = ((-273861/32) * 𝕩 + (94118031/2000) * 𝕩^2 + (-892507329/16000) * 𝕩^3 + (13481811/16000) * 𝕩^4 + (84833973/3200) * 𝕩^5 + (-1468131/160) * 𝕩^6 + (-35490861/16000) * 𝕩^7 + (24234273/16000) * 𝕩^8 + (-3088407/16000) * 𝕩^9) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [b65k_baseProduct, b65k_baseDenominator]
  simp only [map_mul, RatFunc.algebraMap_X, Fin.sum_univ_four]
  rw [b65k_qBase_2_0, b65k_qBase_2_1, b65k_qBase_2_2, b65k_qBase_2_3, b65k_rBase_1_0, b65k_rBase_1_1, b65k_rBase_1_2, b65k_rBase_1_3]
  field_simp
  rw [b65k_fibre_five_map, b65k_fibre_seven_map]
  ring

theorem b65k_product_2_0 : b65k_baseProduct 2 0 = (567 * 𝕩 + (-7371/4) * 𝕩^2 + (22491/8) * 𝕩^3 + (-5145/2) * 𝕩^4 + (8505/8) * 𝕩^5 + (1029/4) * 𝕩^6 + (-3171/8) * 𝕩^7 + 126 * 𝕩^8 + (-105/8) * 𝕩^9) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [b65k_baseProduct, b65k_baseDenominator]
  simp only [map_mul, RatFunc.algebraMap_X, Fin.sum_univ_four]
  rw [b65k_qBase_0_0, b65k_qBase_0_1, b65k_qBase_0_2, b65k_qBase_0_3, b65k_rBase_2_0, b65k_rBase_2_1, b65k_rBase_2_2, b65k_rBase_2_3]
  field_simp
  rw [b65k_fibre_five_map, b65k_fibre_seven_map]
  ring

theorem b65k_product_2_1 : b65k_baseProduct 2 1 = ((19845/4) * 𝕩 + (-32256063/1000) * 𝕩^2 + (14902839/250) * 𝕩^3 + (-9697317/250) * 𝕩^4 + (29967/200) * 𝕩^5 + (1923537/200) * 𝕩^6 + (-1896657/500) * 𝕩^7 + (257439/500) * 𝕩^8 + (-16359/1000) * 𝕩^9) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [b65k_baseProduct, b65k_baseDenominator]
  simp only [map_mul, RatFunc.algebraMap_X, Fin.sum_univ_four]
  rw [b65k_qBase_1_0, b65k_qBase_1_1, b65k_qBase_1_2, b65k_qBase_1_3, b65k_rBase_2_0, b65k_rBase_2_1, b65k_rBase_2_2, b65k_rBase_2_3]
  field_simp
  rw [b65k_fibre_five_map, b65k_fibre_seven_map]
  ring

theorem b65k_product_2_2 : b65k_baseProduct 2 2 = ((-273861/32) * 𝕩 + (479169999/8000) * 𝕩^2 + (-265577697/2000) * 𝕩^3 + (246037491/2000) * 𝕩^4 + (-57346191/1600) * 𝕩^5 + (-28425201/1600) * 𝕩^6 + (63362061/4000) * 𝕩^7 + (-16749747/4000) * 𝕩^8 + (3088407/8000) * 𝕩^9) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h3 : (RatFunc.X : RatFunc ℚ) - 3 ≠ 0 := by simpa using b65k_X_sub_ne 3
  have h1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by simpa using b65k_X_sub_ne 1
  have h2 : (RatFunc.X : RatFunc ℚ) + 2 ≠ 0 := by simpa using b65k_X_sub_ne (-2)
  have hEr : (𝕩^2 * (𝕩 - 3)^3 * (𝕩 - 1)^2 * (𝕩 + 2)^2) ≠ 0 := by
    have := pow_ne_zero 2 hX; have := pow_ne_zero 3 h3; have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2; positivity
  have hP5 := b65k_fibre_five_mapne
  have hP7 := b65k_fibre_seven_mapne
  rw [b65k_baseProduct, b65k_baseDenominator]
  simp only [map_mul, RatFunc.algebraMap_X, Fin.sum_univ_four]
  rw [b65k_qBase_2_0, b65k_qBase_2_1, b65k_qBase_2_2, b65k_qBase_2_3, b65k_rBase_2_0, b65k_rBase_2_1, b65k_rBase_2_2, b65k_rBase_2_3]
  field_simp
  rw [b65k_fibre_five_map, b65k_fibre_seven_map]
  ring

/-- Coefficients of the nine base numerators, in the order s⁰ through s⁹.
Source: G32 v0.16, Lemma numerators, Subsection 5.5(7). -/
def b65k_numCoeff : Fin 3 → Fin 3 → Fin 10 → ℚ :=
  ![![![0, 567, (-5481/4), (5733/4), (-11025/16), (-7245/16), (5103/8), (-441/8), (-1449/16), (315/16)], ![0, (19845/4), (-3515211/125), (68218857/2000), (4772439/2000), (-7379757/400), (708561/200), (4392927/2000), (-1299249/2000), (49077/2000)], ![0, (-273861/32), (52764453/1000), (-1364041161/16000), (451308753/16000), (112224861/3200), (-38394153/1600), (-16658271/16000), (54172377/16000), (-9265221/16000)]], ![![0, 567, (-3969/4), (3591/4), (-4305/16), (-7875/16), (2373/8), (231/8), (-693/16), (105/16)], ![0, (19845/4), (-6203547/250), (37338273/2000), (19371093/2000), (-3823701/400), (2667/20), (2297757/2000), (-465801/2000), (16359/2000)], ![0, (-273861/32), (94118031/2000), (-892507329/16000), (13481811/16000), (84833973/3200), (-1468131/160), (-35490861/16000), (24234273/16000), (-3088407/16000)]], ![![0, 567, (-7371/4), (22491/8), (-5145/2), (8505/8), (1029/4), (-3171/8), 126, (-105/8)], ![0, (19845/4), (-32256063/1000), (14902839/250), (-9697317/250), (29967/200), (1923537/200), (-1896657/500), (257439/500), (-16359/1000)], ![0, (-273861/32), (479169999/8000), (-265577697/2000), (246037491/2000), (-57346191/1600), (-28425201/1600), (63362061/4000), (-16749747/4000), (3088407/8000)]]]

/-- The base numerator with the literal coefficients.
Source: G32 v0.16, Lemma numerators, Subsection 5.5(7). -/
def b65k_numPoly (a b : Fin 3) : Polynomial ℚ :=
  ∑ j : Fin 10, Polynomial.C (b65k_numCoeff a b j) * Polynomial.X ^ j.val

theorem b65k_productPoly_0_0 :
    b65k_baseProduct 0 0 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_numPoly 0 0) := by
  rw [b65k_product_0_0, b65k_numPoly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat, map_neg, map_div₀, b65k_numCoeff,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
  norm_num
  ring

theorem b65k_productPoly_0_1 :
    b65k_baseProduct 0 1 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_numPoly 0 1) := by
  rw [b65k_product_0_1, b65k_numPoly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat, map_neg, map_div₀, b65k_numCoeff,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
  norm_num
  ring

theorem b65k_productPoly_0_2 :
    b65k_baseProduct 0 2 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_numPoly 0 2) := by
  rw [b65k_product_0_2, b65k_numPoly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, b65k_numCoeff,
    Matrix.cons_val_zero, Fin.val_zero, Fin.val_succ]
  norm_num
  ring

theorem b65k_productPoly_1_0 :
    b65k_baseProduct 1 0 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_numPoly 1 0) := by
  rw [b65k_product_1_0, b65k_numPoly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat, map_neg, map_div₀, b65k_numCoeff,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
  norm_num
  ring

theorem b65k_productPoly_1_1 :
    b65k_baseProduct 1 1 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_numPoly 1 1) := by
  rw [b65k_product_1_1, b65k_numPoly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat, map_neg, map_div₀, b65k_numCoeff,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
  norm_num
  ring

theorem b65k_productPoly_1_2 :
    b65k_baseProduct 1 2 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_numPoly 1 2) := by
  rw [b65k_product_1_2, b65k_numPoly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, b65k_numCoeff,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, Fin.val_succ]
  norm_num
  ring

theorem b65k_productPoly_2_0 :
    b65k_baseProduct 2 0 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_numPoly 2 0) := by
  rw [b65k_product_2_0, b65k_numPoly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, b65k_numCoeff,
    Fin.val_zero, Fin.val_succ]
  norm_num
  ring

theorem b65k_productPoly_2_1 :
    b65k_baseProduct 2 1 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_numPoly 2 1) := by
  rw [b65k_product_2_1, b65k_numPoly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, b65k_numCoeff,
    Fin.val_zero, Fin.val_succ]
  norm_num
  ring

theorem b65k_productPoly_2_2 :
    b65k_baseProduct 2 2 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (b65k_numPoly 2 2) := by
  rw [b65k_product_2_2, b65k_numPoly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, b65k_numCoeff,
    Fin.val_zero, Fin.val_succ]
  norm_num
  ring

end HodgeLean.Foundations.Program

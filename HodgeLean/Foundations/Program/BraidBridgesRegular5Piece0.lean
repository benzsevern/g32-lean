import HodgeLean.Foundations.Program.BraidBridgesInterval
import HodgeLean.Foundations.Program.BraidBridgesRegular4Piece2

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

def b65x_certN_5_0 : b65x_CPoly := (C (291668908382000) + X * (0), C (0) + X * (0))
def b65x_certD_5_0 : b65x_CPoly := (C (2228834950000000) + X * (C (-2273299727518203) + X * (0)), C (-4112139000000000) + X * (C (4185003759160770) + X * (0)))

def b65x_certP5_5_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_5_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_5_0 (b65x_cpScale 3 b65x_certD_5_0)) 4))
    (b65x_cpScale (5) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_5_0 b65x_certD_5_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_5_0 (b65x_cpScale 2 b65x_certD_5_0)) 3)))

def b65x_certP7_5_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_5_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_5_0 (b65x_cpScale 3 b65x_certD_5_0)) 4))
    (b65x_cpScale (-7) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_5_0 b65x_certD_5_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_5_0 (b65x_cpScale 2 b65x_certD_5_0)) 3)))

def b65x_certFactors_5_0 : Fin 6 → b65x_CPoly :=
  ![b65x_certD_5_0,
    b65x_cpSub b65x_certN_5_0 (b65x_cpScale 3 b65x_certD_5_0),
    b65x_cpSub b65x_certN_5_0 b65x_certD_5_0,
    b65x_cpAdd b65x_certN_5_0 (b65x_cpScale 2 b65x_certD_5_0),
    b65x_certP5_5_0, b65x_certP7_5_0]

def b65x_regPoly_5_0_0 : ℚ[X] :=
  C (21877392389662502500000000000000) + X * (C (-44552254115419314389249700000000) + X * (C (22682148115324112195824403342109) + X * (0)))

def b65x_regCoeff_5_0_0_0 : Fin 3 → ℚ :=
  ![(21877392389662502500000000000000), (21478657721615347805375150000000), (21087209443135493417325003342109/4)]

theorem b65x_regIdentity_5_0_0_0 (x : ℝ) :
    (b65x_regPoly_5_0_0.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_0_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_0, b65x_regCoeff_5_0_0_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_0_0 : ∀ i, 0 < b65x_regCoeff_5_0_0_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_0_0]

def b65x_regCoeff_5_0_0_1 : Fin 3 → ℚ :=
  ![(21087209443135493417325003342109/4), (20304312886175784641224710026327/4), (19550561887485277091423230078981/16)]

theorem b65x_regIdentity_5_0_0_1 (x : ℝ) :
    (b65x_regPoly_5_0_0.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_0_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_0, b65x_regCoeff_5_0_0_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_0_1 : ∀ i, 0 < b65x_regCoeff_5_0_0_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_0_1]

def b65x_regCoeff_5_0_0_2 : Fin 3 → ℚ :=
  ![(19550561887485277091423230078981/16), (18043059890104261991820270184289/16), (16652140125800051797412563763341/64)]

theorem b65x_regIdentity_5_0_0_2 (x : ℝ) :
    (b65x_regPoly_5_0_0.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_0_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_0, b65x_regCoeff_5_0_0_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_0_2 : ∀ i, 0 < b65x_regCoeff_5_0_0_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_0_2]

def b65x_regCoeff_5_0_0_3 : Fin 3 → ℚ :=
  ![(16652140125800051797412563763341/64), (13870300597191631408597150921445/64), (11554790000890430640562751974525/256)]

theorem b65x_regIdentity_5_0_0_3 (x : ℝ) :
    (b65x_regPoly_5_0_0.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_0_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_0, b65x_regCoeff_5_0_0_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_0_3 : ∀ i, 0 < b65x_regCoeff_5_0_0_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_0_3]

def b65x_regCoeff_5_0_0_4 : Fin 3 → ℚ :=
  ![(11554790000890430640562751974525/256), (6923768808288029104493954080685/256), (4158063344914506051549211766749/1024)]

theorem b65x_regIdentity_5_0_0_4 (x : ℝ) :
    (b65x_regPoly_5_0_0.comp (C (15/16) + C ((31/32) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_0_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_0, b65x_regCoeff_5_0_0_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_0_4 : ∀ i, 0 < b65x_regCoeff_5_0_0_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_0_4]

def b65x_regCoeff_5_0_0_5 : Fin 3 → ℚ :=
  ![(4158063344914506051549211766749/1024), (6942779107996472048758150672375/2048), (11695367460663791761102220453125/16384)]

theorem b65x_regIdentity_5_0_0_5 (x : ℝ) :
    (b65x_regPoly_5_0_0.comp (C (31/32) + C ((125/128) - (31/32)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_0_5).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_0, b65x_regCoeff_5_0_0_5, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_0_5 : ∀ i, 0 < b65x_regCoeff_5_0_0_5 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_0_5]

def b65x_regCoeff_5_0_0_6 : Fin 3 → ℚ :=
  ![(11695367460663791761102220453125/16384), (7314985950005487088274058669875/16384), (5160622072690893504511756209109/65536)]

theorem b65x_regIdentity_5_0_0_6 (x : ℝ) :
    (b65x_regPoly_5_0_0.comp (C (125/128) + C ((251/256) - (125/128)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_0_6).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_0, b65x_regCoeff_5_0_0_6, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_0_6 : ∀ i, 0 < b65x_regCoeff_5_0_0_6 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_0_6]

def b65x_regCoeff_5_0_0_7 : Fin 3 → ℚ :=
  ![(5160622072690893504511756209109/65536), (851894318061706336987151287577/65536), (5447237096807363525725983655981/262144)]

theorem b65x_regIdentity_5_0_0_7 (x : ℝ) :
    (b65x_regPoly_5_0_0.comp (C (251/256) + C ((503/512) - (251/256)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_0_7).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_0, b65x_regCoeff_5_0_0_7, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_0_7 : ∀ i, 0 < b65x_regCoeff_5_0_0_7 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_0_7]

def b65x_regCoeff_5_0_0_8 : Fin 3 → ℚ :=
  ![(5447237096807363525725983655981/262144), (1148835694686414297184708092101/16384), (556504408335927772266464830621/4096)]

theorem b65x_regIdentity_5_0_0_8 (x : ℝ) :
    (b65x_regPoly_5_0_0.comp (C (503/512) + C ((63/64) - (503/512)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_0_8).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_0, b65x_regCoeff_5_0_0_8, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_0_8 : ∀ i, 0 < b65x_regCoeff_5_0_0_8 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_0_8]

def b65x_regCoeff_5_0_0_9 : Fin 3 → ℚ :=
  ![(556504408335927772266464830621/4096), (60307874692764619581460552867/32), (7286389567300306574703342109)]

theorem b65x_regIdentity_5_0_0_9 (x : ℝ) :
    (b65x_regPoly_5_0_0.comp (C (63/64) + C ((1) - (63/64)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_0_9).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_0, b65x_regCoeff_5_0_0_9, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_0_9 : ∀ i, 0 < b65x_regCoeff_5_0_0_9 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_0_9]

theorem b65x_regPoly_positive_5_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_5_0_0.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_5_0_0_0 b65x_regIdentity_5_0_0_0
      b65x_regCoeff_positive_5_0_0_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_5_0_0_1 b65x_regIdentity_5_0_0_1
      b65x_regCoeff_positive_5_0_0_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_5_0_0_2 b65x_regIdentity_5_0_0_2
      b65x_regCoeff_positive_5_0_0_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      2 b65x_regCoeff_5_0_0_3 b65x_regIdentity_5_0_0_3
      b65x_regCoeff_positive_5_0_0_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h4 : t ≤ (31/32 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (15/16) (31/32) (by norm_num)
      2 b65x_regCoeff_5_0_0_4 b65x_regIdentity_5_0_0_4
      b65x_regCoeff_positive_5_0_0_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h5 : t ≤ (125/128 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (31/32) (125/128) (by norm_num)
      2 b65x_regCoeff_5_0_0_5 b65x_regIdentity_5_0_0_5
      b65x_regCoeff_positive_5_0_0_5 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h6 : t ≤ (251/256 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (125/128) (251/256) (by norm_num)
      2 b65x_regCoeff_5_0_0_6 b65x_regIdentity_5_0_0_6
      b65x_regCoeff_positive_5_0_0_6 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h7 : t ≤ (503/512 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (251/256) (503/512) (by norm_num)
      2 b65x_regCoeff_5_0_0_7 b65x_regIdentity_5_0_0_7
      b65x_regCoeff_positive_5_0_0_7 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h8 : t ≤ (63/64 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (503/512) (63/64) (by norm_num)
      2 b65x_regCoeff_5_0_0_8 b65x_regIdentity_5_0_0_8
      b65x_regCoeff_positive_5_0_0_8 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (63/64) (1) (by norm_num)
    2 b65x_regCoeff_5_0_0_9 b65x_regIdentity_5_0_0_9
    b65x_regCoeff_positive_5_0_0_9 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_5_0_0 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_5_0 0)).eval₂ (Rat.castHom ℝ) t =
      (1 : ℝ) * b65x_regPoly_5_0_0.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_5_0, b65x_certP5_5_0, b65x_certP7_5_0,
    b65x_certN_5_0, b65x_certD_5_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_5_0_0,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_5_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_5_0 0)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_5_0_0]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_5_0_0 t ht)

def b65x_regPoly_5_0_1 : ℚ[X] :=
  C (193081111118098372704457924000000) + X * (C (-396991981939071835612981634724000) + X * (C (204139333037917009762419630078981) + X * (0)))

def b65x_regCoeff_5_0_1_0 : Fin 3 → ℚ :=
  ![(193081111118098372704457924000000), (187666231266660827602425030638000), (182479813632166829354288056630981/4)]

theorem b65x_regIdentity_5_0_1_0 (x : ℝ) :
    (b65x_regPoly_5_0_1.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_1_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_1, b65x_regCoeff_5_0_1_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_1_0 : ∀ i, 0 < b65x_regCoeff_5_0_1_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_1_0]

def b65x_regCoeff_5_0_1_1 : Fin 3 → ℚ :=
  ![(182479813632166829354288056630981/4), (172106978363178832858014108616943/4), (162647991961965023777323838022829/16)]

theorem b65x_regIdentity_5_0_1_1 (x : ℝ) :
    (b65x_regPoly_5_0_1.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_1_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_1, b65x_regCoeff_5_0_1_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_1_1 : ∀ i, 0 < b65x_regCoeff_5_0_1_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_1_1]

def b65x_regCoeff_5_0_1_2 : Fin 3 → ℚ :=
  ![(162647991961965023777323838022829/16), (143730019159537405615943296834601/16), (128467441828206537116897465326069/64)]

theorem b65x_regIdentity_5_0_1_2 (x : ℝ) :
    (b65x_regPoly_5_0_1.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_1_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_1, b65x_regCoeff_5_0_1_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_1_2 : ∀ i, 0 < b65x_regCoeff_5_0_1_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_1_2]

def b65x_regCoeff_5_0_1_3 : Fin 3 → ℚ :=
  ![(128467441828206537116897465326069/64), (97942287165544800118805802309005/64), (82038714387270061770052978010725/256)]

theorem b65x_regIdentity_5_0_1_3 (x : ℝ) :
    (b65x_regPoly_5_0_1.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_1_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_1, b65x_regCoeff_5_0_1_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_1_3 : ∀ i, 0 < b65x_regCoeff_5_0_1_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_1_3]

def b65x_regCoeff_5_0_1_4 : Fin 3 → ℚ :=
  ![(82038714387270061770052978010725/256), (50231568830720585072547329414165/256), (76910750811719102972397035692741/1024)]

theorem b65x_regIdentity_5_0_1_4 (x : ℝ) :
    (b65x_regPoly_5_0_1.comp (C (15/16) + C ((31/32) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_1_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_1, b65x_regCoeff_5_0_1_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_1_4 : ∀ i, 0 < b65x_regCoeff_5_0_1_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_1_4]

def b65x_regCoeff_5_0_1_5 : Fin 3 → ℚ :=
  ![(76910750811719102972397035692741/1024), (1667448873812407368740606642411/16), (228462216943546853895919354981)]

theorem b65x_regIdentity_5_0_1_5 (x : ℝ) :
    (b65x_regPoly_5_0_1.comp (C (31/32) + C ((1) - (31/32)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_1_5).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_1, b65x_regCoeff_5_0_1_5, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_1_5 : ∀ i, 0 < b65x_regCoeff_5_0_1_5 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_1_5]

theorem b65x_regPoly_positive_5_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_5_0_1.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_5_0_1_0 b65x_regIdentity_5_0_1_0
      b65x_regCoeff_positive_5_0_1_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_5_0_1_1 b65x_regIdentity_5_0_1_1
      b65x_regCoeff_positive_5_0_1_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_5_0_1_2 b65x_regIdentity_5_0_1_2
      b65x_regCoeff_positive_5_0_1_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      2 b65x_regCoeff_5_0_1_3 b65x_regIdentity_5_0_1_3
      b65x_regCoeff_positive_5_0_1_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h4 : t ≤ (31/32 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (15/16) (31/32) (by norm_num)
      2 b65x_regCoeff_5_0_1_4 b65x_regIdentity_5_0_1_4
      b65x_regCoeff_positive_5_0_1_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (31/32) (1) (by norm_num)
    2 b65x_regCoeff_5_0_1_5 b65x_regIdentity_5_0_1_5
    b65x_regCoeff_positive_5_0_1_5 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_5_0_1 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_5_0 1)).eval₂ (Rat.castHom ℝ) t =
      (1 : ℝ) * b65x_regPoly_5_0_1.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_5_0, b65x_certP5_5_0, b65x_certP7_5_0,
    b65x_certN_5_0, b65x_certD_5_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_5_0_1,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_5_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_5_0 1)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_5_0_1]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_5_0_1 t ht)

def b65x_regPoly_5_0_2 : ℚ[X] :=
  C (20662299428118950908057924000000) + X * (C (-43226152415518649759161144908000) + X * (C (22682148115324112195824403342109) + X * (0)))

def b65x_regCoeff_5_0_2_0 : Fin 3 → ℚ :=
  ![(20662299428118950908057924000000), (19711522648478576936535275546000), (18879040996762616309733809526109/4)]

theorem b65x_regIdentity_5_0_2_0 (x : ℝ) :
    (b65x_regPoly_5_0_2.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_2_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_2, b65x_regCoeff_5_0_2_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_2_0 : ∀ i, 0 < b65x_regCoeff_5_0_2_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_2_0]

def b65x_regCoeff_5_0_2_1 : Fin 3 → ℚ :=
  ![(18879040996762616309733809526109/4), (17214077693330695056130877486327/4), (16022294901596427181412675182981/16)]

theorem b65x_regIdentity_5_0_2_1 (x : ℝ) :
    (b65x_regPoly_5_0_2.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_2_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_2, b65x_regCoeff_5_0_2_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_2_1 : ∀ i, 0 < b65x_regCoeff_5_0_2_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_2_1]

def b65x_regCoeff_5_0_2_2 : Fin 3 → ℚ :=
  ![(16022294901596427181412675182981/16), (13638729318127891431976270576289/16), (13147885781449969198078784915341/64)]

theorem b65x_regIdentity_5_0_2_2 (x : ℝ) :
    (b65x_regPoly_5_0_2.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_2_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_2, b65x_regCoeff_5_0_2_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_2_2 : ∀ i, 0 < b65x_regCoeff_5_0_2_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_2_2]

def b65x_regCoeff_5_0_2_3 : Fin 3 → ℚ :=
  ![(13147885781449969198078784915341/64), (12166198708094124730283813593445/64), (18755399821900734324644518054525/256)]

theorem b65x_regIdentity_5_0_2_3 (x : ℝ) :
    (b65x_regPoly_5_0_2.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_2_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_2, b65x_regCoeff_5_0_2_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_2_3 : ∀ i, 0 < b65x_regCoeff_5_0_2_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_2_3]

def b65x_regCoeff_5_0_2_4 : Fin 3 → ℚ :=
  ![(18755399821900734324644518054525/256), (823650139225826199295088057635/8), (118295127924413344721182434109)]

theorem b65x_regIdentity_5_0_2_4 (x : ℝ) :
    (b65x_regPoly_5_0_2.comp (C (15/16) + C ((1) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_2_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_2, b65x_regCoeff_5_0_2_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_2_4 : ∀ i, 0 < b65x_regCoeff_5_0_2_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_2_4]

theorem b65x_regPoly_positive_5_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_5_0_2.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_5_0_2_0 b65x_regIdentity_5_0_2_0
      b65x_regCoeff_positive_5_0_2_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_5_0_2_1 b65x_regIdentity_5_0_2_1
      b65x_regCoeff_positive_5_0_2_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_5_0_2_2 b65x_regIdentity_5_0_2_2
      b65x_regCoeff_positive_5_0_2_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      2 b65x_regCoeff_5_0_2_3 b65x_regIdentity_5_0_2_3
      b65x_regCoeff_positive_5_0_2_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (15/16) (1) (by norm_num)
    2 b65x_regCoeff_5_0_2_4 b65x_regIdentity_5_0_2_4
    b65x_regCoeff_positive_5_0_2_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_5_0_2 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_5_0 2)).eval₂ (Rat.castHom ℝ) t =
      (1 : ℝ) * b65x_regPoly_5_0_2.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_5_0, b65x_certP5_5_0, b65x_certP7_5_0,
    b65x_certN_5_0, b65x_certD_5_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_5_0_2,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_5_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_5_0 2)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_5_0_2]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_5_0_2 t ht)

def b65x_regPoly_5_0_3 : ℚ[X] :=
  C (22548741934521838928364481000000) + X * (C (-45215304965369646704293977546000) + X * (C (22682148115324112195824403342109) + X * (0)))

def b65x_regCoeff_5_0_3_0 : Fin 3 → ℚ :=
  ![(22548741934521838928364481000000), (22489831386358854504581973227000), (22446505922672174500694372250109/4)]

theorem b65x_regIdentity_5_0_3_0 (x : ℝ) :
    (b65x_regPoly_5_0_3.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_3_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_3, b65x_regCoeff_5_0_3_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_3_0 : ∀ i, 0 < b65x_regCoeff_5_0_3_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_3_0]

def b65x_regCoeff_5_0_3_1 : Fin 3 → ℚ :=
  ![(22446505922672174500694372250109/4), (22359854995298814492919170296327/4), (22335544405830672164723595526981/16)]

theorem b65x_regIdentity_5_0_3_1 (x : ℝ) :
    (b65x_regPoly_5_0_3.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_3_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_3, b65x_regCoeff_5_0_3_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_3_1 : ∀ i, 0 < b65x_regCoeff_5_0_3_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_3_1]

def b65x_regCoeff_5_0_3_2 : Fin 3 → ℚ :=
  ![(22335544405830672164723595526981/16), (22286923226894387508332445988289/16), (22487663399578973570259805187341/64)]

theorem b65x_regIdentity_5_0_3_2 (x : ℝ) :
    (b65x_regPoly_5_0_3.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_3_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_3, b65x_regCoeff_5_0_3_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_3_2 : ∀ i, 0 < b65x_regCoeff_5_0_3_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_3_2]

def b65x_regCoeff_5_0_3_3 : Fin 3 → ℚ :=
  ![(22487663399578973570259805187341/64), (50185043171146515481839799763/4), (15585084476304419894906796109)]

theorem b65x_regIdentity_5_0_3_3 (x : ℝ) :
    (b65x_regPoly_5_0_3.comp (C (7/8) + C ((1) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_5_0_3_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_3, b65x_regCoeff_5_0_3_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_3_3 : ∀ i, 0 < b65x_regCoeff_5_0_3_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_3_3]

theorem b65x_regPoly_positive_5_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_5_0_3.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_5_0_3_0 b65x_regIdentity_5_0_3_0
      b65x_regCoeff_positive_5_0_3_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_5_0_3_1 b65x_regIdentity_5_0_3_1
      b65x_regCoeff_positive_5_0_3_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_5_0_3_2 b65x_regIdentity_5_0_3_2
      b65x_regCoeff_positive_5_0_3_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (7/8) (1) (by norm_num)
    2 b65x_regCoeff_5_0_3_3 b65x_regIdentity_5_0_3_3
    b65x_regCoeff_positive_5_0_3_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_5_0_3 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_5_0 3)).eval₂ (Rat.castHom ℝ) t =
      (4 : ℝ) * b65x_regPoly_5_0_3.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_5_0, b65x_certP5_5_0, b65x_certP7_5_0,
    b65x_certN_5_0, b65x_certD_5_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_5_0_3,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_5_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_5_0 3)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_5_0_3]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_5_0_3 t ht)

def b65x_regPoly_5_0_4 : ℚ[X] :=
  C (100251855671776641622960474622977773164778366884400553538311820657249840591873780630469364162470107183317157120043491123580434901266988487731101726018805760000000000000000000000000000000000) + X * (C (-1234085446446750717691384267676732214453361851018713867748170415253126329207999979729972420769182308438712541607743839435512440277507335204617177887862963415040000000000000000000000000000000) + X * (C (6962791409029022760004457884188936468221010835545736240979581970250430843839971109726459373505489047028030187738887980042887780080366986062561579530957783424059520000000000000000000000000000) + X * (C (-23808993595904768788290340601452809277298671305286059668693748434364792981796732629811195918989963223249889430178674992266558416414312279002883165727066834171472545920000000000000000000000000) + X * (C (54954776560181872433677351753656406619028943283899791520463107138178374230579331199710287056582782367202488422963015565838818806802004248543417864126065381822837050914400000000000000000000000) + X * (C (-90200684626700014953363836508896759924605719294213500342443369357101065031075144266498124032650281672982372431490627381440593742616407481841303166301524712579680676516639680000000000000000000) + X * (C (107955076434446291284080001349623083000915542647301430994229052784286223619176306396177765574416435171045774936832995487654944923188357396252608079182040611681982600290394334520000000000000000) + X * (C (-94925804237450177304871500118222146425508128589723992452726535738490261029191823647724010172679648100356755348986850769983810677038305295852795313216702954098366641162288737573960000000000000) + X * (C (60863003350025184391468054130668743361124503695879675015244715210474625255172005175534374274349161769796267742047524185922851800104301744645119711030217391475245015639187244861512010000000000) + X * (C (-27749841761769749301293558907939632829520822010275466731129747005169311587406776668932560938597037700213443588904878754185781400441126621134344523812316722294295512455118419034641782600000000) + X * (C (8540267645073337261956312857556844922919444979384857686074579263449599874090481906774560463477602570166579047126338379419170640048701356560531269242306901161687619284403900812969140564800000) + X * (C (-1592935003214275490033964556980071579454198125660402244455737519076286976264849984808024967521685427694397413874875042259843166108028189507298705236260791335905571264879725347682660419738000) + X * (C (136177417058251818898042176741359300446311188347426952571491942764064190091692397261650730581433742919557632115343380290362848719669903149978116330821546050834679116883792412722494196658841) + X * (0)))))))))))))

def b65x_regCoeff_5_0_4_0 : Fin 13 → ℚ :=
  ![(100251855671776641622960474622977773164778366884400553538311820657249840591873780630469364162470107183317157120043491123580434901266988487731101726018805760000000000000000000000000000000000), (585979544837944340629833561637367170750659477103449708585656640260434922498485377700646159565050131980449614636649973765208998676450194250464631768294187412480000000000000000000000000000000), (1569850371137385089813892323941739966437134742653944321158538372048902379379662410527744563868896639443020938015001292271712226977422643080498630416734327233294880000000000000000000000000000), (2548912793589677222013089191235714209673982987257073559216150496464468863867568491718767488480887312929018962771498038785003218796414179454913540919416877575114731760000000000000000000000000), (2793578316867511584154585360138240268377614535420832466009066339748852211407082060226576031074629660407577621329330234790074436095956691905516003418818330900890301522150000000000000000000000), (2177259003139015748679551539793212822356608260947992818690632873327165159626441403056763711742150784336567343156739076352663173505588290349239563782547991031862647676055010000000000000000000), (1237350016061695485291951676636394057178098581590250969902230635844732824591940211188438552062703739077252911131608477060104771666477151765822783815489116199113737081722481476875000000000000), (516640440664938845796817259781984166712836643647229538867183802697959580727493311439144520489572820240266451290393491468594570086506383380873490754251389826623775389499298098953437500000000), (157296290815694056308802388789330848971265014088980009612510413499278337198260900581725738935033295283601159509409426028155151448990163585137085972119366275665960435425193516882468789062500), (34056027354807522070811338900628805847657427964753645862360860753749652179787493773770132602480202743566590069560155806366337697069376323153905805019699881682132296868169453318465424609375), (9954322882188084364198935695212330922196137475167015427229610508909179760647537065002897833776908046339304389528802210576166863887908035764754203272077560391888899743483558915247431571875/2), (56429274771518815843741006957242975108091327358738813424191074504407060172108775191647456090537169668657376038009876766452262183204488433991312479198699363006304803058954186254801914966375/128), (73309143411744051460427029616854703095710646129556688615131627366641119791720026096710894069908673979918336034922357198046845502736965207788886078381655622727474619307277389571634816382841/4096)]

theorem b65x_regIdentity_5_0_4_0 (x : ℝ) :
    (b65x_regPoly_5_0_4.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_5_0_4_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_4, b65x_regCoeff_5_0_4_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_4_0 : ∀ i, 0 < b65x_regCoeff_5_0_4_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_4_0]

def b65x_regCoeff_5_0_4_1 : Fin 13 → ℚ :=
  ![(73309143411744051460427029616854703095710646129556688615131627366641119791720026096710894069908673979918336034922357198046845502736965207788886078381655622727474619307277389571634816382841/4096), (208348092533545936393915210893748526996665196296099690142656050264513596748610033337218397904880708470006016010222200650803512058996779398169474871845305700496833149293863016106298027714569/2048), (2171385145286646907191286274678982826682685829635266828204327150688484882170492404096246104746804426436098949180218618763113550202126602188994480413045878124025259256460738689453499293057777/8192), (3429177330311478911104592674564558446020118544443605032863107607015461900597264688795646517160768954655047093273390852679400553593845209397923426688847771022242817624750290684954073205673885/8192), (29247695026449425448956016482904810401554219935726380394981499641197795881698735576327658618333780881816808570037843644207098918560433755696359993200187644665010108532777712807830529839589895/65536), (5544225976109204603711739548580688268487281505872632064251399437467207258197171261855681070269374674821528390627261780183986443760872173945987449812652346435462745061036709918251794893190937/16384), (12263160237732765048782665009579966359346622401168423106207328269557165147559373272353178068333339471205001717734575458043545036806323290609239014124647718191617545316063901383001483981595559/65536), (4982888610858851743456962194664292631936703219900911368714920617443747436815530229491598258746919261679585521550014377776966399566787422859851965600371280620436354059486169139266799963784433/65536), (23625621213590008661783445570196585911538026742430018577355171506512156172049366057316172406134654379175570393873898142851831157394608550279044665170962412957206283394025433753383279558761495/1048576), (2489746384422635685252729128753116568787877515644417421700345185594705134443558458339881396029967675974642691895517992186977369440704847743894228194179451187411548981967995507583702212252165/524288), (1417128281735010092782342928097251486968541833134917168144130917472739995656382532863206191157695343495961068344618347448554525213989285010535205197995242300075806460170527375458023854450897/2097152), (122240213228975245170035353090592077285698253401992144610387428713443252000469042887141417949018708907748717927637877801561490759972402768207308195914535980622161368485063529465206943394881/2097152), (38671589305589653748743374833227235456544673825043123384195377057600154609449125780295278220892821178408376349186239347334557547950589718704272433476946953833404518286147965021788064375881/16777216)]

theorem b65x_regIdentity_5_0_4_1 (x : ℝ) :
    (b65x_regPoly_5_0_4.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_5_0_4_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_4, b65x_regCoeff_5_0_4_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_4_1 : ∀ i, 0 < b65x_regCoeff_5_0_4_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_4_1]

def b65x_regCoeff_5_0_4_2 : Fin 13 → ℚ :=
  ![(38671589305589653748743374833227235456544673825043123384195377057600154609449125780295278220892821178408376349186239347334557547950589718704272433476946953833404518286147965021788064375881/16777216), (103563877292356393398619667317860964537505557621403821236983536091514887484104046248374668089997972790177951287400398522888036411610501931923835509463450623256317927605204626265678692593167/8388608), (1018267004475435172061487429899340676755766009514513229111410065823696637570006827097855226965479688148301282638586606146464912280925121093945051673915465046699067131639669223895834009315953/33554432), (1519224850834663183467654723466444807937059625156505776291674067834168778402083630541804689719296833225730695693023316663394663647665310431567936084154534131921950609204512353612215206287595/33554432), (12260869824655036340773878705091848097830739487339267850674360139407546289380765051408336242866190627751244720426572553125067214532491900413505442333063598213858132712005985394428028532609495/268435456), (2203225628596009340711113562655881692217964455590767995439800999672103435080350399020307693405308675304654582931664970107764583960824508613359986201697261792022840135763378285552909066950431/67108864), (4629301923792787339693285918228637622395476502322007266306500199768306583005541396371397809329370665567704426546104848084917838582351238775531790016543052981138837811093176053383046538222791/268435456), (1791146298072233815389492051925719698666875248481362657578159346486215554013355626414978867146644444355807262207866476037181139170376560810663412747485751127423005797962558908176930675848791/268435456), (8109084066658984143704822517060907008685537726285953621925208163396363343340203293826712744405539775998668986523573018230138247534012887811826714065352052550354768992211157876725920173205895/4294967296), (818610773696562105297630707338023469006353082924759330469716271696024848084048346229228132612745413389565399282111438892152204586236069500076291921624000580203522952849135369118940696638195/2147483648), (448020063202899297473499402343018671172388308587548515441281359747472215191972818350453765742312926407903760196004887628301934387077956751576032857113021425908735772612582072385293457971473/8589934592), (37324698442093238968489825021087541243532170300735754558927957771575319390561392994152975247927401274607628560882815262238127525946261017932061058366292094722910716649840443427557573737767/8589934592), (11464903867924175871166379018426162782398779923010029890563693781304101300114823741212534562847200695053349521708571830220352738341213469996188954854816245234756766277742723434535522922041/68719476736)]

theorem b65x_regIdentity_5_0_4_2 (x : ℝ) :
    (b65x_regPoly_5_0_4.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_5_0_4_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_4, b65x_regCoeff_5_0_4_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_4_2 : ∀ i, 0 < b65x_regCoeff_5_0_4_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_4_2]

def b65x_regCoeff_5_0_4_3 : Fin 13 → ℚ :=
  ![(11464903867924175871166379018426162782398779923010029890563693781304101300114823741212534562847200695053349521708571830220352738341213469996188954854816245234756766277742723434535522922041/68719476736), (28534737927131104903517761123660382554524678705618759897217328488586272919910627682606860569770003706264888573611515947506919593178399194101578476960762017666989463200003624055704558822835/34359738368), (270296507228769879789755275061089586915744391787053337484052066189264787347890049313745095408453343814252878694933769473219667410745773228140191315981954034933488077160978617160624406346825/137438953472), (406248388796555595906064553363118419057813439796333656867558482657158360860716522682569214016778047650374181966643804822375992284692444285551786230562231310828151173067746697169335444024375/137438953472), (3483709478324605853700895716539756356810191292105242436678964633229880519313224606949033799396411250150549002730372591079152631235033432428197686537892856217170978384272573986750628248684375/1099511627776), (706798721468613458692959271210805442422863732676836268054680281852794524123932809434344723064783887918222539264649313311726756282217910408250790650165874009170952757041814017393176596221875/274877906944), (1789265772607580695181860633376745113838990137631088344862759478041825435777205375979950621877146301486728674857609891490783102450344401222823030847801497459659152966083639796061503143609375/1099511627776), (889744640292632841189052899055786587070948365516203869778325568647067710829538292306155465123350985617236504527151836883351168293101472465861329167498238120260343631864217904217469158671875/1099511627776), (5494066549061897561076009203647076730521264945153447708976567253477323327360659267414259018396601344826465852214704487877361276006805968993919519209458044824372903532140763951986044333984375/17592186044416), (795886416484637433776424311879489706948322081604858105693403430811568270531046871057030061075086886211666344702634314316471298067556998790634175495396425314177784941234973226749198427734375/8796093022208), (651086640163352446532073438204483846497221761669521016782578773109538971065232482073306989279029841430455556122871222575188020075369097757698642429364773896067976989366563402207108916015625/35184372088832), (83634407564822049775604149409566098501871643344309315771744430758401025217849400274476607335231904427100382471104564643580147547428832608174220034874212407247499629564647935387107763671875/35184372088832), (40494865788211687999341515801562452392551266159771203287838816165361603560664790653264106956759186731802195947868724835624516032086184554057596825546319191867477398458518527053877197265625/281474976710656)]

theorem b65x_regIdentity_5_0_4_3 (x : ℝ) :
    (b65x_regPoly_5_0_4.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_5_0_4_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_4, b65x_regCoeff_5_0_4_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_4_3 : ∀ i, 0 < b65x_regCoeff_5_0_4_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_4_3]

def b65x_regCoeff_5_0_4_4 : Fin 13 → ℚ :=
  ![(40494865788211687999341515801562452392551266159771203287838816165361603560664790653264106956759186731802195947868724835624516032086184554057596825546319191867477398458518527053877197265625/281474976710656), (197184976964261092442865343394929874529218108749322198047060483971452381610284315330423747940368871732018998588609394233460349193917995770169931360168447912312297326997370872710679248046875/140737488355328), (3591579901195770551552976223819258744329556174681301761748178633441616813022251916081755555022986440689823934822693633528653865570467299306903782301319857812242744197112728672731738447265625/562949953421312), (10034919284244574722887054847082917420332432383726410429821154494824758421581881804307536437048902310030884945942736223737571055675129655819898593209528747998835643274012574960203899443359375/562949953421312), (152691273239615321289369672683712561608626116309948236121005558630109409751001449063146899793121756294771148910091823767384275646067500823348528827833422472626225206345148703500187682771484375/4503599627370496), (51932556290093832301530712512469618977300243132426782511682954831363833395681315918506051097840664586847416330178546875030124852714091895548989717782245900837643211483782710482176052170546875/1125899906842624), (206813756532403567265025958695087265223901160282698038587193122765010517436509371222208081561346857873341131577394366156402711580047348629826533149590185397742757511091398073237765140191859375/4503599627370496), (151466616407671061721319088071518282712998934126811992894133623140147715161485243025777226612930814499453403766785242731076306016673290582569261413947058187443392365450960628657881790440646875/4503599627370496), (1292207537706062708510909442311753606507783164034538253500687307216240848482958617411285618302563875196432932963499824420530158110087500121904057252240852754100447836782855195291464177331684375/72057594037927936), (243745548119091273128368697354369446853027890195391941295641498826013132235195690411623971142784862289226818426255981444671317533637379498248500266157882414863859270103373137455247823167979375/36028797018963968), (245969160652986126007264581879766678895781244818611147172152275121314256568007708636640785592935691072325423717404076402505458196924861861574898977843397035833874515404775280095178876062174425/144115188075855872), (37085822730714536068067957980606836716683370634025406844984298872712254355266291221892858222830184326597792630674943344087521227415292445624296467754854191073124837430020224538399938456267195/144115188075855872), (20141647842506281877269880252080450793573712571447867295435820763684617099292429526427333274686660430242445375131098492511526233330002290538311120918164616712096549351797746289276714247391001/1152921504606846976)]

theorem b65x_regIdentity_5_0_4_4 (x : ℝ) :
    (b65x_regPoly_5_0_4.comp (C (15/16) + C ((31/32) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_5_0_4_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_4, b65x_regCoeff_5_0_4_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_4_4 : ∀ i, 0 < b65x_regCoeff_5_0_4_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_4_4]

def b65x_regCoeff_5_0_4_5 : Fin 13 → ℚ :=
  ![(20141647842506281877269880252080450793573712571447867295435820763684617099292429526427333274686660430242445375131098492511526233330002290538311120918164616712096549351797746289276714247391001/1152921504606846976), (1458695049800269347733855173477157229002360442519887190082697713646349808913187334836821350076862310258096468419897008340441092035919651624414805937477478691447800664085813395589387767869113/9007199254740992), (370138435078022009608107635254184169205779709874343036452655410637644629018747953621483995138013398770213606335474894865079519115931654865643139365375145248923102424037718624205124219485153/562949953421312), (13225253001558929788588851800662285609093540150365995932605854683603052130439565312738301922363227239466845973108626399212951361400383613256054821054974651965077505522037831864958307044605/8796093022208), (2259291747383788160204882267956017001755588609090536589086794012937145520181395706523695441108646952957503183427162404377677002359581381700550717357643710453424373242458094380442131961095/1099511627776), (6922016701274838748356186304495065331231060894157853389083767370738577212519338206753603300643196455026452181665713066801049205621917394058841871358087255054268151749683693978207318249/4294967296), (175253591308558042328422825026504481249840937558691482494178586459595814008854574049033872345394614515628718869998847094519424567807804083856658081131944116453688661571273738311742551/268435456), (1669704679039636323872904438504766595766092355039373989602925801533496506368425193841822118717981147800228887833825510968438020908882196798758802937186034393332519687208067772970609/4194304), (980300499629593611741929540038018244041732088052588686828656554400244711061036177297399617410988451908413732284131325248915339660879350611438232561592390149055169994793066221504695/1048576), (9840239289285297393773375814157826326567505857810129869436465729586893133883149853326160226903438482386315184455190244028793105548146895396526235713984244888473223762184617585205/8192), (402652546971772681544612560274430629944519479642865788705465724877010711533654806941088230374007880243015079943930923772043595074987155547603487893862233630127003505112706901633/512), (2108663016705397813304550143204558041487130419817963033003303827166541751699155492043005061257426999902026055346245393086935315548650130437410969913861113680003130340207503713/8), (36162595665890199194979633821065183655903531660605723918598334788311678385867576342406444370900497690720517390948981421158705668986693443481885537926342710650919201741720841)]

theorem b65x_regIdentity_5_0_4_5 (x : ℝ) :
    (b65x_regPoly_5_0_4.comp (C (31/32) + C ((1) - (31/32)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_5_0_4_5).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_4, b65x_regCoeff_5_0_4_5, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_4_5 : ∀ i, 0 < b65x_regCoeff_5_0_4_5 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_4_5]

theorem b65x_regPoly_positive_5_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_5_0_4.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      12 b65x_regCoeff_5_0_4_0 b65x_regIdentity_5_0_4_0
      b65x_regCoeff_positive_5_0_4_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      12 b65x_regCoeff_5_0_4_1 b65x_regIdentity_5_0_4_1
      b65x_regCoeff_positive_5_0_4_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      12 b65x_regCoeff_5_0_4_2 b65x_regIdentity_5_0_4_2
      b65x_regCoeff_positive_5_0_4_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      12 b65x_regCoeff_5_0_4_3 b65x_regIdentity_5_0_4_3
      b65x_regCoeff_positive_5_0_4_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h4 : t ≤ (31/32 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (15/16) (31/32) (by norm_num)
      12 b65x_regCoeff_5_0_4_4 b65x_regIdentity_5_0_4_4
      b65x_regCoeff_positive_5_0_4_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (31/32) (1) (by norm_num)
    12 b65x_regCoeff_5_0_4_5 b65x_regIdentity_5_0_4_5
    b65x_regCoeff_positive_5_0_4_5 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_5_0_4 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_5_0 4)).eval₂ (Rat.castHom ℝ) t =
      (1600 : ℝ) * b65x_regPoly_5_0_4.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_5_0, b65x_certP5_5_0, b65x_certP7_5_0,
    b65x_certN_5_0, b65x_certD_5_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_5_0_4,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_5_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_5_0 4)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_5_0_4]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_5_0_4 t ht)

def b65x_regPoly_5_0_5 : ℚ[X] :=
  C (4986930057764875649156627301229322760436266972204358998885079267994718982230449812734695594508196850493954713974098985793504321177604566851879911033880576000000000000000000000000000000000000) + X * (C (-61233183411726119741708183371220083439917146936918695464924242468495557204382017715787462696615111428734629206503651455776730268537528541924196730118185923584000000000000000000000000000000000) + X * (C (344689823873576836332619272467938574978214086585634043369134601286232008612239717732248930534118937798006861678484163207202643053685474458613909594106050348966096000000000000000000000000000000) + X * (C (-1176228139419496110467971660217801233487760272459087808546985848420705354870969554126893760090941333771697195763752319898642376335572348782437322784381377038612736784000000000000000000000000000) + X * (C (2709958981831631580874061873591342929387535862808123196542639110457548808672844401142020608864750619806493056123926642239463636211355956186376953701653754495806645839708000000000000000000000000) + X * (C (-4440936020284740754215383710454964178188758126481249707035561385986314003994171559466820029988690180768758881295321622539570540482550607414163733574560070079668330304707368000000000000000000000) + X * (C (5307808728241217106644439604468715790709303231982814155800161801887431084291738377769747772225924004435356219978076525431362377758326742915233669077622056005915045713198006251000000000000000000) + X * (C (-4661906845749665594593626831537975948557608833797524422440512659439110431685802998583479065203260828730961744058322286128808187788866207150758617690766277773305769377356494980481000000000000000) + X * (C (2986337987596560011357381258342855009530078947192567604568558912394628324742163730432802060688649726869722694800261302733639024679722842010329053601414871201829368888822907715576628250000000000) + X * (C (-1360664833685123795570470687107295514776341613279972716112781973054067803424111216212151859560293662741084315784709666778960458137525738163303644232657063755275397406356156868906704489000000000) + X * (C (418567692671647123617210214847511212438976928176789920815299418877753549699086717225339649668110866840702777023604202450198886310518607661305151330117643092642016539194147388638915336820000000) + X * (C (-78053815157499499011664263292023507393255708157359709978331138434738061836977649255593223408562585957025473279868877070732315139293381285857636556576778775459372991979106542036450360567162000) + X * (C (6672693435854339126004066660326605721869248229023920676003105195439145314492927465820885798490253403058323973651825634227779587263825254348927700210255756490899276727305828223402215636283209) + X * (0)))))))))))))

def b65x_regCoeff_5_0_5_0 : Fin 13 → ℚ :=
  ![(4986930057764875649156627301229322760436266972204358998885079267994718982230449812734695594508196850493954713974098985793504321177604566851879911033880576000000000000000000000000000000000000), (29226568987315447919025435929141831405276630197992960254158829981688849184574388894922615785790806491560141964437362101633686719862490531260460567347473950208000000000000000000000000000000000), (78527331016382343348097211456409487013802833658843379711615548432483890356168519636721097039687613724062265906141490857399929484186863046294469511112608023529524000000000000000000000000000000), (127908111142309426940534687204519995957822375526393986823764043238202205141921571682238412958817420592022738621192729871387178866558112353228278986421067564028647902000000000000000000000000000), (140669045221491825911732950601599396540686687942782231663184363406915800042465046917629923271386711596224338537098644201227930068220598423747380134637923337737166482981750000000000000000000000), (110041671916461991490704465224315391456064808848916282943542755560538748362916206315065740018559393571789596833507883632853764880057543378141624539419927653779252069831894750000000000000000000), (62786269870923430871255100806567587436236207560148041428495310785116188861905482748460711388161049798753775481420650729562454322704106760647835930364787954208909322602982097671875000000000000), (26327039958369057277443481752726827040819521531402157573033929258831802206187354058532839945397378308295926811723618559518283933228746773200158029008002421800946540865505218996242187500000000), (8051763774964832568924932376419859268091580924626600023480857395503092517597129202361478112649959594818538517464064944015872371097959889722334728543900452225003124898575363167057141601562500), (1751635571831741337545030939041590777379178517974486352857153442585180198772446572048566565390980246084761680440849619565547673030340510989196750539479759245668117301285597258723284201171875), (1029172070609805488232746998382318626681435120333894232016493605883466652391182575260311627269850943673158445563141181091292030286739443310042686926828977847383225520287488869366275011015625/4), (2932699056611020919606711379292343235692826769941971853198387517613291091412493765361643586630226198601616465749726141039948943993386799021631379727408034040893030777836577350678819919552375/128), (3831414921386888092482671256040215316458404097532976858443839274749000276991154162339751782115680996594927934498190973151192695444133614190639685932157492469374543832407485286578929781959209/4096)]

theorem b65x_regIdentity_5_0_5_0 (x : ℝ) :
    (b65x_regPoly_5_0_5.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_5_0_5_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_5, b65x_regCoeff_5_0_5_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_5_0 : ∀ i, 0 < b65x_regCoeff_5_0_5_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_5_0]

def b65x_regCoeff_5_0_5_1 : Fin 13 → ℚ :=
  ![(3831414921386888092482671256040215316458404097532976858443839274749000276991154162339751782115680996594927934498190973151192695444133614190639685932157492469374543832407485286578929781959209/4096), (11021141839593825475490350270023191962583022718261016900407453331834673761620437338164617345999319380541419684485909630041142707050108135542706135570153159897226648268974748773779808681213881/2048), (116401229913507127890176217949333857403228264048886835261516381512970312024861556637238018709761506287697226758435601275552707625210048505940473932315769947672930733914504590071058033358231073/8192), (186529570807488995675575019219658628474278997624695772684432521231432056159685508463883927858182008900127679514392336957325309939816934315630032934337337915423815590183732265681932907382020365/8192), (1616388148078684049381226351459298600540105879965974610223117811702096603301882477890416804970713171330232724588287907718545444897723038976267848258749738373317526046410954851731800068667904855/65536), (311713822311540474619290870056986328620147625009973949864009893264651562125581319553332997826050685505360476232447502391638321624673824785992606312092704783592964938457639523865446970452755913/16384), (702342150169960466823896125991585463000624099017131778166390732212243471612876067483965522312324630242761060756703470401652726812882441983297462861087010396604487161758643434079433716613382391/65536), (291094044034201447029688969945485521488318029499640494706390331759259259819860609111296081358885577297825224518782235170330976952139306987643291734639423298191289833602436593697267096491037217/65536), (1409676605292941737325589649962309954093648603510943379377829343456616059537244457560112013988005756016397003347639296936874879721833524094548730579237971912436886620992204887934466206587313255/1048576), (151934503341023071685367743240448203880124069124105927340404327392722217752043094307181018430067995735839041694563349830250828745596486556344508132732209434564498749281478279461194613736356085/524288), (88564123489294676398409040496348805474769829142810927925302621117537252032501806651667664071178736849150078913031915926982333565110957635682264981831761981829947698768641509504532542338493953/2097152), (7834160061480793812950255539227198520807415793706520355896671679114374290210106012011827203089458196161256106884152652249782786214165747384037538505919393277049655111289857811637427743149169/2097152), (2544959185823969312213137187108525147872727434421220920439050679215399905335124751229308946576688109673592508346156426080619094713419367804925258389838668607158781308360479577873376677618169/16777216)]

theorem b65x_regIdentity_5_0_5_1 (x : ℝ) :
    (b65x_regPoly_5_0_5.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_5_0_5_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_5, b65x_regCoeff_5_0_5_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_5_1 : ∀ i, 0 < b65x_regCoeff_5_0_5_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_5_1]

def b65x_regCoeff_5_0_5_2 : Fin 13 → ℚ :=
  ![(2544959185823969312213137187108525147872727434421220920439050679215399905335124751229308946576688109673592508346156426080619094713419367804925258389838668607158781308360479577873376677618169/16777216), (7236312549454136184017723605522329289239715322377947572158112754709850567595910737040126113011276594739820361347102530226006279992442815476252248496709230910329721552664600577585534612265183/8388608), (76000244031432808011504175378636986070700479825085638093247874554025373706805284136214222610182834076371484522227972156901877610059504126098906586327772591075394368967367241510382580510881697/33554432), (121817312712104564237356222878576006436855799921866171309207944222095692048418948326426551437998473727933730304139323979367781239289236970296679436098266970632503614605017274203306530964092155/33554432), (1061848867794443471535623546878801373706135951073446646762781388319716901460180023398244585732470817919199680470843478596206892175157055813043566511701661674275438959419431815239863337169865255/268435456), (207096110301218837038062875211371639674388586498933594232010196631627667541160239867877962405091003882745854425045698521849346862086799229573270230049968575170968884400662135350427761963771119/67108864), (474328059643286505618280387958701631525524515847110915435643260758960780589531967451115218388748769254046246866302545620717753335611197788365069028742824960949213195525221961904568251886516759/268435456), (200794739245108707025208937731918624118589622601072906453000348803995809566412479112717648994336885182804924524925814271237853779692006950703853387205333788089137677605000303712884724601390759/268435456), (997598087276893208340982232425373069094364078473993099562098593829233412399345924270274463142685753391343664242130196658329008683348325367804402855310145267643833086673379213596517672423088855/4294967296), (110762448323715822537274538094608236442527750203304436530601935769845428644837080262028531638962275532398764984289693547101720907810090686008344407622922357126852463822628206208402745047271555/2147483648), (66763590044061763151851549757174869544775432152009316303542506661980872045846599464921682029177916230646249513380480901677034180977063553116869906774278611354170737116990561547129386346202177/8589934592), (6128334393085541442162743043674218094044711849992342084697502678317579875464862950278162134720172813581762903895341552812518692465035033438055655419441544757480708593025911068748014924350583/8589934592), (2072607302765594409203208506289558046014573592026772947878781886453933737915473888149231114558708505715341363435036890613355831299240436442831040522764813314205717703511741602586477755980009/68719476736)]

theorem b65x_regIdentity_5_0_5_2 (x : ℝ) :
    (b65x_regPoly_5_0_5.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_5_0_5_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_5, b65x_regCoeff_5_0_5_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_5_2 : ∀ i, 0 < b65x_regCoeff_5_0_5_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_5_2]

def b65x_regCoeff_5_0_5_3 : Fin 13 → ℚ :=
  ![(2072607302765594409203208506289558046014573592026772947878781886453933737915473888149231114558708505715341363435036890613355831299240436442831040522764813314205717703511741602586477755980009/68719476736), (6396796938719266798503390469257586226041738628256272361514031621450243890309539092786755761588030924274546463124648909895165096763093861109368053866000230312890042145553852285782269955118915/34359738368), (73678589210337121775277043631701429431528121240999675554097893386821264782920233203290967357585279727248679679542795147622351214398039422164952146991980091748327572131529241081963468896594425/137438953472), (130486611506200878738545699276144066373680980161462649717198363409776417686363728925300360385687815120921500773152951000248187535130452712874435456531956285925013799057692364940925912917194375/137438953472), (1264197822317744111572019001441727127439047091025430700611990863071236137946489705707712905560473042165396176898377230175303877440537472715326386058778643188679785969932525731709096521785534375/1099511627776), (275510804127183932443146470026862499448492905637743735457943420167061655734299946394261295340106549193232061572141438116818129669824513969890846828152240111551587723684821566218247717214871875/274877906944), (709028390474428258805814521347295448165746683995385597457956037337354200140974514791527179201681346603153287930015133515041750323132086179528810493876596465479924045892685110978410054036859375/1099511627776), (339360798938962817296580343796334645305317307652620137837958816035441115372790102308992796507712657599901568026383970510143404958914495832912076929339110282718502792057051909312752948774921875/1099511627776), (1920042215198329197566157988557886454324031946079013239606369706622724728742095860946500799397003520682034045868733137495973419732781712077964997699705152986695338742194528955070224172365234375/17592186044416), (244762448540732755813363085907460431815099591648996664744497866389951693079586581418840170843531349393387612909942041368411356558309039499092059747971016987905450581209421040899840722958984375/8796093022208), (170921664460190491798347923458050821771961842232643474697021872410806084415743922064292155329413001605328998479079449964082263392474160859554271131359626069021146056905369382168098336884765625/35184372088832), (18349774732225597531783295898331523577141229273966429495696513504364553732703879568020151012786965763175556156960621336867661712778683676701753304026648863690598338212023631684468280419921875/35184372088832), (7328637346350616961388905888849112440024345696549363773748347020938380656222709699867638289123789526443134174612250046695176715646541736952235507201746141634294306953288699663639982666015625/281474976710656)]

theorem b65x_regIdentity_5_0_5_3 (x : ℝ) :
    (b65x_regPoly_5_0_5.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_5_0_5_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_5, b65x_regCoeff_5_0_5_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_5_3 : ∀ i, 0 < b65x_regCoeff_5_0_5_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_5_3]

def b65x_regCoeff_5_0_5_4 : Fin 13 → ℚ :=
  ![(7328637346350616961388905888849112440024345696549363773748347020938380656222709699867638289123789526443134174612250046695176715646541736952235507201746141634294306953288699663639982666015625/281474976710656), (454517163353281669047927721026976717866475976960207728193565944806323529495531191447845481823050352019230795859516100402233554270117691769369152197323695151535572830980308413306458447265625/4398046511104), (141744574699964153514832937918406462432159471742359848834281671964882249243874869741889009206012643563909231064844251467727145744984332680304221569233964714995230401552758968904931181640625/549755813888), (7193979564640179309931798557150516607970747570863464909106131007107831626306027644985167972771417212840176672450756821315010862878824438390267741127858679889761687669930876552919111328125/17179869184), (2042976641541815197005158494968253260706114899203523530797826181861410287991382372004373377422729221966356705816366157720711124862719882503575195896234791792734780781475903212288771484375/4294967296), (13108606060150635154347593388349329830464156423447390419528037874877608611239214804713778732984446866727210201603860978753989839299205032531716804575332799057549405537775066112681015625/33554432), (1224912011985048361903878278567080511213938347068612459851487729226830149370830167199171007071695385025262182636197207099282647048889136263057890136785010972198326808359307219059234375/4194304), (29007452307453202639050658166993346412351912676652272978599709665799114259251048418732005122416958407066645306831131348288078963119970599447332187488972770086386871201612534120040625/131072), (11819322466946130292701809840929629619718361395226883728681320156470820926121516293616839583860550146990840736588356917836407584575232805455820145182829190777327207142734295958034375/65536), (107573178259096763613034483790788032549664290426528281193518105604880624440504562823594544457294820637416935644531671479504622929152168204735536719474516134122252014657326966983125/1024), (3963556285115997572772533978374223636183494186420345377927591783000596410895134953325898469177409241312403090146263815709026626455258175965731709764483084295517486448187644111825/128), (269570905531615886775076522131228769101234117052030004883339934379252716761460655633878996238136410250478939167636590483371689168767097284444581282243419414271287841528663905/4), (47581698638979682772870835044141191584781563596427298381326219989202426188902605571648903500336809397243769705241714614393347098758131744465393251240792014790952889121209)]

theorem b65x_regIdentity_5_0_5_4 (x : ℝ) :
    (b65x_regPoly_5_0_5.comp (C (15/16) + C ((1) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_5_0_5_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_5_0_5, b65x_regCoeff_5_0_5_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_5_0_5_4 : ∀ i, 0 < b65x_regCoeff_5_0_5_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_5_0_5_4]

theorem b65x_regPoly_positive_5_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_5_0_5.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      12 b65x_regCoeff_5_0_5_0 b65x_regIdentity_5_0_5_0
      b65x_regCoeff_positive_5_0_5_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      12 b65x_regCoeff_5_0_5_1 b65x_regIdentity_5_0_5_1
      b65x_regCoeff_positive_5_0_5_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      12 b65x_regCoeff_5_0_5_2 b65x_regIdentity_5_0_5_2
      b65x_regCoeff_positive_5_0_5_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      12 b65x_regCoeff_5_0_5_3 b65x_regIdentity_5_0_5_3
      b65x_regCoeff_positive_5_0_5_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (15/16) (1) (by norm_num)
    12 b65x_regCoeff_5_0_5_4 b65x_regIdentity_5_0_5_4
    b65x_regCoeff_positive_5_0_5_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_5_0_5 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_5_0 5)).eval₂ (Rat.castHom ℝ) t =
      (64 : ℝ) * b65x_regPoly_5_0_5.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_5_0, b65x_certP5_5_0, b65x_certP7_5_0,
    b65x_certN_5_0, b65x_certD_5_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_5_0_5,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_5_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_5_0 5)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_5_0_5]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_5_0_5 t ht)

theorem b65x_certFactors_ne_zero_5_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1))
    (j : Fin 6) : b65x_cpEval (b65x_certFactors_5_0 j) t ≠ 0 := by
  apply b65x_cpEval_ne_zero
  fin_cases j

  · exact b65x_certFactor_norm_positive_5_0_0 t ht

  · exact b65x_certFactor_norm_positive_5_0_1 t ht

  · exact b65x_certFactor_norm_positive_5_0_2 t ht

  · exact b65x_certFactor_norm_positive_5_0_3 t ht

  · exact b65x_certFactor_norm_positive_5_0_4 t ht

  · exact b65x_certFactor_norm_positive_5_0_5 t ht

theorem b65x_certND_ratio_5_0 (t : ℝ) :
    b65b_inverseNormalization (b65x_piece 5 0 t) =
      b65x_cpEval b65x_certN_5_0 t / b65x_cpEval b65x_certD_5_0 t := by
  have hQ : (1 + t ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hQc : (((1 + t ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ
  push_cast at hQc
  have hrel : b65x_cpEval b65x_certD_5_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 6).1 : ℂ) - b65x_piece 5 0 t *
          (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ))) := by
    norm_num [b65x_cpEval, b65x_certD_5_0, Polynomial.eval₂_pow,
      b65x_piece, b65x_centre, b65x_radius, b65x_et, mr_centre, mr_basePoint,
      b65b_vertex0, b65b_track, b65b_radius, b65b_boxCentre]
    push_cast
    field_simp [hQc]
    <;> ring
  have hnrel : b65x_cpEval b65x_certN_5_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 0).1 : ℂ) * ((b65b_boxCentre 6).1 : ℂ)) := by
    norm_num [b65x_cpEval, b65x_certN_5_0, Polynomial.eval₂_pow, b65b_boxCentre]
    all_goals push_cast
    all_goals ring
  unfold b65b_inverseNormalization
  rw [hnrel, hrel]
  have hLQ : (50000000000000 : ℂ) * (1) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    norm_num
  exact (mul_div_mul_left _ _ hLQ).symm

theorem b65x_piece_regular_5_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    ((b65b_boxCentre 6).1 : ℂ) - b65x_piece 5 0 t *
        (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
      b65b_inverseNormalization (b65x_piece 5 0 t) ∈ b65s_regular := by

  have h0 := b65x_certFactors_ne_zero_5_0 t ht 0

  have h1 := b65x_certFactors_ne_zero_5_0 t ht 1

  have h2 := b65x_certFactors_ne_zero_5_0 t ht 2

  have h3 := b65x_certFactors_ne_zero_5_0 t ht 3

  have h4 := b65x_certFactors_ne_zero_5_0 t ht 4

  have h5 := b65x_certFactors_ne_zero_5_0 t ht 5

  change b65x_cpEval b65x_certD_5_0 t ≠ 0 at h0
  change b65x_cpEval (b65x_cpSub b65x_certN_5_0 (b65x_cpScale 3 b65x_certD_5_0)) t ≠ 0 at h1
  change b65x_cpEval (b65x_cpSub b65x_certN_5_0 b65x_certD_5_0) t ≠ 0 at h2
  change b65x_cpEval (b65x_cpAdd b65x_certN_5_0 (b65x_cpScale 2 b65x_certD_5_0)) t ≠ 0 at h3
  change b65x_cpEval b65x_certP5_5_0 t ≠ 0 at h4
  change b65x_cpEval b65x_certP7_5_0 t ≠ 0 at h5
  norm_num only [b65x_certFactors_5_0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, b65x_certP5_5_0, b65x_certP7_5_0,
    b65x_cpEval_sub, b65x_cpEval_add, b65x_cpEval_mul, b65x_cpEval_pow,
    b65x_cpEval_scale] at h0 h1 h2 h3 h4 h5
  have hN : b65x_cpEval b65x_certN_5_0 t ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [b65x_cpEval, b65x_certN_5_0, Polynomial.eval₂_pow,
      pow_two, Complex.mul_re] at hr
    skip
  have hreg : b65b_inverseNormalization (b65x_piece 5 0 t) ∈ b65s_regular := by
    rw [b65x_certND_ratio_5_0]
    exact b65x_regular_of_homogeneous _ _ h0 hN h1 h2 h3
      (by simpa only [mul_assoc] using h4) (by simpa only [mul_assoc] using h5)
  refine ⟨?_, hreg⟩
  intro h
  apply hreg.1
  simp [b65b_inverseNormalization, h]

end HodgeLean.Foundations.Program

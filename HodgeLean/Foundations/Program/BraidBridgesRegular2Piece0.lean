import HodgeLean.Foundations.Program.BraidBridgesInterval
import HodgeLean.Foundations.Program.BraidBridgesRegular1Piece2

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

def b65x_certN_2_0 : b65x_CPoly := (C (72917227095500) + X * (0), C (0) + X * (0))
def b65x_certD_2_0 : b65x_CPoly := (C (557208737500000) + X * (C (-565419112500000) + X * (0)), C (-1028034750000000) + X * (C (1027993698516363) + X * (0)))

def b65x_certP5_2_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_2_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_2_0 (b65x_cpScale 3 b65x_certD_2_0)) 4))
    (b65x_cpScale (5) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_2_0 b65x_certD_2_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_2_0 (b65x_cpScale 2 b65x_certD_2_0)) 3)))

def b65x_certP7_2_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_2_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_2_0 (b65x_cpScale 3 b65x_certD_2_0)) 4))
    (b65x_cpScale (-7) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_2_0 b65x_certD_2_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_2_0 (b65x_cpScale 2 b65x_certD_2_0)) 3)))

def b65x_certFactors_2_0 : Fin 6 → b65x_CPoly :=
  ![b65x_certD_2_0,
    b65x_cpSub b65x_certN_2_0 (b65x_cpScale 3 b65x_certD_2_0),
    b65x_cpSub b65x_certN_2_0 b65x_certD_2_0,
    b65x_cpAdd b65x_certN_2_0 (b65x_cpScale 2 b65x_certD_2_0),
    b65x_certP5_2_0, b65x_certP7_2_0]

def b65x_regPoly_2_0_0 : ℚ[X] :=
  C (1367337024353906406250000000000) + X * (C (-2743739429380680152728500000000) + X * (C (1376469816969638680277378747769) + X * (0)))

def b65x_regCoeff_2_0_0_0 : Fin 3 → ℚ :=
  ![(1367337024353906406250000000000), (1362804334017472736135750000000), (1358339055623903999820378747769/4)]

theorem b65x_regIdentity_2_0_0_0 (x : ℝ) :
    (b65x_regPoly_2_0_0.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_0_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_0, b65x_regCoeff_2_0_0_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_0_0 : ∀ i, 0 < b65x_regCoeff_2_0_0_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_0_0]

def b65x_regCoeff_2_0_0_1 : Fin 3 → ℚ :=
  ![(1358339055623903999820378747769/4), (1349408498836766527189636243307/4), (1340747589821088789754408729921/16)]

theorem b65x_regIdentity_2_0_0_1 (x : ℝ) :
    (b65x_regPoly_2_0_0.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_0_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_0, b65x_regCoeff_2_0_0_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_0_1 : ∀ i, 0 < b65x_regCoeff_2_0_0_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_0_1]

def b65x_regCoeff_2_0_0_2 : Fin 3 → ℚ :=
  ![(1340747589821088789754408729921/16), (1323425771789733314883953703149/16), (1307182544844216780795558640681/64)]

theorem b65x_regIdentity_2_0_0_2 (x : ℝ) :
    (b65x_regPoly_2_0_0.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_0_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_0, b65x_regCoeff_2_0_0_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_0_2 : ∀ i, 0 < b65x_regCoeff_2_0_0_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_0_2]

def b65x_regCoeff_2_0_0_3 : Fin 3 → ℚ :=
  ![(1307182544844216780795558640681/64), (1274696090953183712618768515745/64), (1246524001405506407570218248025/256)]

theorem b65x_regIdentity_2_0_0_3 (x : ℝ) :
    (b65x_regPoly_2_0_0.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_0_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_0, b65x_regCoeff_2_0_0_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_0_3 : ∀ i, 0 < b65x_regCoeff_2_0_0_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_0_3]

def b65x_regCoeff_2_0_0_4 : Fin 3 → ℚ :=
  ![(1246524001405506407570218248025/256), (1190179822310151797473117712585/256), (1151093100588220239888976606009/1024)]

theorem b65x_regIdentity_2_0_0_4 (x : ℝ) :
    (b65x_regPoly_2_0_0.comp (C (15/16) + C ((31/32) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_0_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_0, b65x_regCoeff_2_0_0_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_0_4 : ∀ i, 0 < b65x_regCoeff_2_0_0_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_0_4]

def b65x_regCoeff_2_0_0_5 : Fin 3 → ℚ :=
  ![(1151093100588220239888976606009/1024), (1072919657144357124720694392857/1024), (1063776043194186219604249895161/4096)]

theorem b65x_regIdentity_2_0_0_5 (x : ℝ) :
    (b65x_regPoly_2_0_0.comp (C (31/32) + C ((63/64) - (31/32)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_0_5).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_0, b65x_regCoeff_2_0_0_5, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_0_5 : ∀ i, 0 < b65x_regCoeff_2_0_0_5 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_0_5]

def b65x_regCoeff_2_0_0_6 : Fin 3 → ℚ :=
  ![(1063776043194186219604249895161/4096), (1045488815293844409371360899769/4096), (1303320905368271439345822766201/16384)]

theorem b65x_regIdentity_2_0_0_6 (x : ℝ) :
    (b65x_regPoly_2_0_0.comp (C (63/64) + C ((127/128) - (63/64)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_0_6).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_0, b65x_regCoeff_2_0_0_6, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_0_6 : ∀ i, 0 < b65x_regCoeff_2_0_0_6 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_0_6]

def b65x_regCoeff_2_0_0_7 : Fin 3 → ℚ :=
  ![(1303320905368271439345822766201/16384), (4028626407412922343350966663/64), (67411942864933798878747769)]

theorem b65x_regIdentity_2_0_0_7 (x : ℝ) :
    (b65x_regPoly_2_0_0.comp (C (127/128) + C ((1) - (127/128)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_0_7).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_0, b65x_regCoeff_2_0_0_7, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_0_7 : ∀ i, 0 < b65x_regCoeff_2_0_0_7 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_0_7]

theorem b65x_regPoly_positive_2_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_2_0_0.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_2_0_0_0 b65x_regIdentity_2_0_0_0
      b65x_regCoeff_positive_2_0_0_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_2_0_0_1 b65x_regIdentity_2_0_0_1
      b65x_regCoeff_positive_2_0_0_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_2_0_0_2 b65x_regIdentity_2_0_0_2
      b65x_regCoeff_positive_2_0_0_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      2 b65x_regCoeff_2_0_0_3 b65x_regIdentity_2_0_0_3
      b65x_regCoeff_positive_2_0_0_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h4 : t ≤ (31/32 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (15/16) (31/32) (by norm_num)
      2 b65x_regCoeff_2_0_0_4 b65x_regIdentity_2_0_0_4
      b65x_regCoeff_positive_2_0_0_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h5 : t ≤ (63/64 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (31/32) (63/64) (by norm_num)
      2 b65x_regCoeff_2_0_0_5 b65x_regIdentity_2_0_0_5
      b65x_regCoeff_positive_2_0_0_5 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h6 : t ≤ (127/128 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (63/64) (127/128) (by norm_num)
      2 b65x_regCoeff_2_0_0_6 b65x_regIdentity_2_0_0_6
      b65x_regCoeff_positive_2_0_0_6 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (127/128) (1) (by norm_num)
    2 b65x_regCoeff_2_0_0_7 b65x_regIdentity_2_0_0_7
    b65x_regCoeff_positive_2_0_0_7 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_2_0_0 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_2_0 0)).eval₂ (Rat.castHom ℝ) t =
      (1 : ℝ) * b65x_regPoly_2_0_0.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_2_0, b65x_certP5_2_0, b65x_certP7_2_0,
    b65x_certN_2_0, b65x_certD_2_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_2_0_0,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_2_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_2_0 0)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_2_0_0]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_2_0_0 t ht)

def b65x_regPoly_2_0_1 : ℚ[X] :=
  C (12067569444881148294028620250000) + X * (C (-24446282101444329998094000000000) + X * (C (12388228352726748122496408729921) + X * (0)))

def b65x_regCoeff_2_0_1_0 : Fin 3 → ℚ :=
  ![(12067569444881148294028620250000), (11911997839040131589010240500000), (11765941929362681302422889729921/4)]

theorem b65x_regIdentity_2_0_1_0 (x : ℝ) :
    (b65x_regPoly_2_0_1.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_1_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_1, b65x_regCoeff_2_0_1_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_1_0 : ∀ i, 0 < b65x_regCoeff_2_0_1_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_1_0]

def b65x_regCoeff_2_0_1_1 : Fin 3 → ℚ :=
  ![(11765941929362681302422889729921/4), (11473830110007780729248188189763/4), (11219781075307145829797602569289/16)]

theorem b65x_regIdentity_2_0_1_1 (x : ℝ) :
    (b65x_regPoly_2_0_1.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_1_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_1, b65x_regCoeff_2_0_1_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_1_1 : ∀ i, 0 < b65x_regCoeff_2_0_1_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_1_1]

def b65x_regCoeff_2_0_1_2 : Fin 3 → ℚ :=
  ![(11219781075307145829797602569289/16), (10711683005905876030896431328341/16), (10355836075121668926891723766129/64)]

theorem b65x_regIdentity_2_0_1_2 (x : ℝ) :
    (b65x_regPoly_2_0_1.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_1_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_1, b65x_regCoeff_2_0_1_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_1_2 : ∀ i, 0 < b65x_regCoeff_2_0_1_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_1_2]

def b65x_regCoeff_2_0_1_3 : Fin 3 → ℚ :=
  ![(10355836075121668926891723766129/64), (9644142213553254718882308641705/64), (9541452906453091290458748232225/256)]

theorem b65x_regIdentity_2_0_1_3 (x : ℝ) :
    (b65x_regPoly_2_0_1.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_1_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_1, b65x_regCoeff_2_0_1_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_1_3 : ∀ i, 0 < b65x_regCoeff_2_0_1_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_1_3]

def b65x_regCoeff_2_0_1_4 : Fin 3 → ℚ :=
  ![(9541452906453091290458748232225/256), (9336074292252764433611627413265/256), (11566713895925440695107925454081/1024)]

theorem b65x_regIdentity_2_0_1_4 (x : ℝ) :
    (b65x_regPoly_2_0_1.comp (C (15/16) + C ((31/32) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_1_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_1, b65x_regCoeff_2_0_1_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_1_4 : ∀ i, 0 < b65x_regCoeff_2_0_1_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_1_4]

def b65x_regCoeff_2_0_1_5 : Fin 3 → ℚ :=
  ![(11566713895925440695107925454081/1024), (139414975229542266343518627551/16), (9515696163566418431028979921)]

theorem b65x_regIdentity_2_0_1_5 (x : ℝ) :
    (b65x_regPoly_2_0_1.comp (C (31/32) + C ((1) - (31/32)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_1_5).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_1, b65x_regCoeff_2_0_1_5, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_1_5 : ∀ i, 0 < b65x_regCoeff_2_0_1_5 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_1_5]

theorem b65x_regPoly_positive_2_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_2_0_1.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_2_0_1_0 b65x_regIdentity_2_0_1_0
      b65x_regCoeff_positive_2_0_1_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_2_0_1_1 b65x_regIdentity_2_0_1_1
      b65x_regCoeff_positive_2_0_1_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_2_0_1_2 b65x_regIdentity_2_0_1_2
      b65x_regCoeff_positive_2_0_1_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      2 b65x_regCoeff_2_0_1_3 b65x_regIdentity_2_0_1_3
      b65x_regCoeff_positive_2_0_1_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h4 : t ≤ (31/32 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (15/16) (31/32) (by norm_num)
      2 b65x_regCoeff_2_0_1_4 b65x_regIdentity_2_0_1_4
      b65x_regCoeff_positive_2_0_1_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (31/32) (1) (by norm_num)
    2 b65x_regCoeff_2_0_1_5 b65x_regIdentity_2_0_1_5
    b65x_regCoeff_positive_2_0_1_5 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_2_0_1 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_2_0 1)).eval₂ (Rat.castHom ℝ) t =
      (1 : ℝ) * b65x_regPoly_2_0_1.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_2_0, b65x_certP5_2_0, b65x_certP7_2_0,
    b65x_certN_2_0, b65x_certD_2_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_2_0_1,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_2_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_2_0 1)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_2_0_1]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_2_0_1 t ht)

def b65x_regPoly_2_0_2 : ℚ[X] :=
  C (1291393714257434431753620250000) + X * (C (-2661281841720083027241000000000) + X * (C (1376469816969638680277378747769) + X * (0)))

def b65x_regCoeff_2_0_2_0 : Fin 3 → ℚ :=
  ![(1291393714257434431753620250000), (1252146507654827349886740500000), (1219480990559210352809859747769/4)]

theorem b65x_regIdentity_2_0_2_0 (x : ℝ) :
    (b65x_regPoly_2_0_2.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_2_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_2, b65x_regCoeff_2_0_2_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_2_0 : ∀ i, 0 < b65x_regCoeff_2_0_2_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_2_0]

def b65x_regCoeff_2_0_2_1 : Fin 3 → ℚ :=
  ![(1219480990559210352809859747769/4), (1154149956367976358656098243307/4), (1115145680204702703662332729921/16)]

theorem b65x_regIdentity_2_0_2_1 (x : ℝ) :
    (b65x_regPoly_2_0_2.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_2_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_2, b65x_regCoeff_2_0_2_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_2_1 : ∀ i, 0 < b65x_regCoeff_2_0_2_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_2_1]

def b65x_regCoeff_2_0_2_2 : Fin 3 → ℚ :=
  ![(1115145680204702703662332729921/16), (1037137127878155393674801703149/16), (1064435607663449440327254640681/64)]

theorem b65x_regIdentity_2_0_2_2 (x : ℝ) :
    (b65x_regPoly_2_0_2.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_2_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_2, b65x_regCoeff_2_0_2_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_2_2 : ∀ i, 0 < b65x_regCoeff_2_0_2_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_2_2]

def b65x_regCoeff_2_0_2_3 : Fin 3 → ℚ :=
  ![(1064435607663449440327254640681/64), (6824619946323511663113234383/4), (6581689506990084789998997769)]

theorem b65x_regIdentity_2_0_2_3 (x : ℝ) :
    (b65x_regPoly_2_0_2.comp (C (7/8) + C ((1) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_2_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_2, b65x_regCoeff_2_0_2_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_2_3 : ∀ i, 0 < b65x_regCoeff_2_0_2_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_2_3]

theorem b65x_regPoly_positive_2_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_2_0_2.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_2_0_2_0 b65x_regIdentity_2_0_2_0
      b65x_regCoeff_positive_2_0_2_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_2_0_2_1 b65x_regIdentity_2_0_2_1
      b65x_regCoeff_positive_2_0_2_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_2_0_2_2 b65x_regIdentity_2_0_2_2
      b65x_regCoeff_positive_2_0_2_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (7/8) (1) (by norm_num)
    2 b65x_regCoeff_2_0_2_3 b65x_regIdentity_2_0_2_3
    b65x_regCoeff_positive_2_0_2_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_2_0_2 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_2_0 2)).eval₂ (Rat.castHom ℝ) t =
      (1 : ℝ) * b65x_regPoly_2_0_2.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_2_0, b65x_certP5_2_0, b65x_certP7_2_0,
    b65x_certN_2_0, b65x_certD_2_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_2_0_2,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_2_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_2_0 2)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_2_0_2]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_2_0_2 t ht)

def b65x_regPoly_2_0_3 : ℚ[X] :=
  C (1409296370907614933022780062500) + X * (C (-2784968223210978715472250000000) + X * (C (1376469816969638680277378747769) + X * (0)))

def b65x_regCoeff_2_0_3_0 : Fin 3 → ℚ :=
  ![(1409296370907614933022780062500), (33624518604251150573310125000), (797964666274897827908810269)]

theorem b65x_regIdentity_2_0_3_0 (x : ℝ) :
    (b65x_regPoly_2_0_3.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_2_0_3_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_3, b65x_regCoeff_2_0_3_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_3_0 : ∀ i, 0 < b65x_regCoeff_2_0_3_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_3_0]

theorem b65x_regPoly_positive_2_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_2_0_3.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_2_0_3_0 b65x_regIdentity_2_0_3_0
    b65x_regCoeff_positive_2_0_3_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_2_0_3 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_2_0 3)).eval₂ (Rat.castHom ℝ) t =
      (4 : ℝ) * b65x_regPoly_2_0_3.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_2_0, b65x_certP5_2_0, b65x_certP7_2_0,
    b65x_certN_2_0, b65x_certD_2_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_2_0_3,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_2_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_2_0 3)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_2_0_3]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_2_0_3 t ht)

def b65x_regPoly_2_0_4 : ℚ[X] :=
  C (5975476245389976598200826324401961157606742792391810032028664389684786831848250665096602687982923220593759841921537585471894437150179653628534181476760253906250000000000000000000000) + X * (C (-72474935787395016605939103768219994295047339486965509888195339718525153198169278275892943755306721059353870457385744127170303869578292393808634586949768066406250000000000000000000000) + X * (C (402898264577198720356066696805042823464708518182057532043959183734432701350024769141642973439018583598163993390671588072904759912461022953595322502922571027642211914062500000000000000) + X * (C (-1357467351556056770060701649428320785640382363651929712109292338742964736985830724027648771514934669377458423373616463855237158719806766082717284570846667969970703125000000000000000000) + X * (C (3087287868631070554835848536551141037933527742546417804568860678640055957654037081925995177553133699980918394279255811457668525125143682972855363661832479004170247976074218750000000000) + X * (C (-4993118401282798324749045046965697834128477808948632771902233523729538042057681008992601755004132969971626491979177567817673979723507863818274721923439587367452885742187500000000000000) + X * (C (5888470738745566624330203232967383309659437246031961644457413581781974496555116813753105254746269330510825636023661012518237393333800659876506093291205648028068840937735732421875000000) + X * (C (-5102091878800699601172898631857724787020489375347001608783433863607811997846155467153681257584471613930349409866033789774918263197905034036753315773924951831490954655605468750000000000) + X * (C (3223510356769086016600150925258079004598053354833092864180145993360145471494175538899204877483708548775608639056929393583620861265552801621343337847366380754609968831649968337539062500) + X * (C (-1448288600043544744317586620385503927419996025016384270593754620133215701302264744774662471946441824945173351245384307391453248383663926836382690559237815909527347615843804687500000000) + X * (C (439230257763500188098854765093556567914237475284537837642432670048030699016813041217855372282574220064725553875193181424855003986224009665166744357547386732057545947044492852247325000) + X * (C (-80733224062398924281517423224355775127172188637813491764000765018024048308463947070704547043198013008936465854618159937275030249169648338021436627401647888403117384743653397750000000) + X * (C (6801428801081300368372514537251195287893312465080881252620061194324402681213893021027596245243175464240295744942764140128262254005670355845095728090893274488969031658948794129396881) + X * (0)))))))))))))

def b65x_regCoeff_2_0_4_0 : Fin 13 → ℚ :=
  ![(5975476245389976598200826324401961157606742792391810032028664389684786831848250665096602687982923220593759841921537585471894437150179653628534181476760253906250000000000000000000000), (35468247050982210875440364008713536743757243765218965440246302816954865383094368843212760378141718117448182874365578962077581311013009646638092884246239013671875000000000000000000000), (96493851509365544237606140886580173645461786665063540739807277200915763649559705664375330112440612632282860398867784959934551547346504711934596374973095149488677978515625000000000000), (159106282330921599573435473576448572016405078433299301217170740464422551308793076084847975243487904721623408199607217506990674700813194592188714469719228106062316894531250000000000000), (177088736790313193484134486685138438677318328908168822235214074457180401348015027394403752570470925475728408009027546516178705424855182627605959652181412737596608516082763671875000000), (140166621017837700973462419451787808351513124996610798803916672466820532203104436791022124542905406342071935137362148283747789573436502673112856172558267497969164667968750000000000000), (80898057933087089750805577011839189527375040611725280418189701865624557078878983332187077278270447632731771297801619358601190075737853481013636203804533307161183517459738006591796875), (34304529137414830484974747076238198611727493397532327771086533243916949079083533805082199226662103629768677852301509352874320436705656536973865358207840089479868769802525939941406250), (678868250223453935257357398749124294081075088597800363933779256571979735328476705815019928500243555660075929235253606354323134198056939615357628468048343124288432232591056537509765625/64), (37319116607993845315664799713593425757503040189012973526214091384067016207119345064206290191431799582150720895721319293313604801720075962674086048009629502502253885964199359775390625/16), (44314486761306344028847421865310690329897571007574561305069354692923713829313637002693967109227207846964326242361484309799457763986619236634808799142644620100571149339898259773103125/128), (1993294040140240646933519746203276742856564331677584271011964972788724338274592136867214773464873101105699923961853328132837615654980583643290735130721422188284381966586673827790625/64), (5260222019829215762541733955613712271670231895863693995556741387354619200839495316864714606666421478728626980948259463133964827969547695746554062750898126388016340710544308243696881/4096)]

theorem b65x_regIdentity_2_0_4_0 (x : ℝ) :
    (b65x_regPoly_2_0_4.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_2_0_4_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_4, b65x_regCoeff_2_0_4_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_4_0 : ∀ i, 0 < b65x_regCoeff_2_0_4_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_4_0]

def b65x_regCoeff_2_0_4_1 : Fin 13 → ℚ :=
  ![(5260222019829215762541733955613712271670231895863693995556741387354619200839495316864714606666421478728626980948259463133964827969547695746554062750898126388016340710544308243696881/4096), (15449293536219091511939289661270982559327057755931897623819232921571983395161983661906995084559823690866444045144681918080281601246239923426334802666540382479596954929511992948621929/2048), (166399221682084462774656882671583349507888074941181107372826855866208422700379004620144911148656509966212313515699694999302355999082077095568481125257235628021684223754504142600723657/8192), (271594261337595950381832600160997350701527328192182564525941653456315035891515618093109719020735645168659829770878743521663009594035860909982765671388474618984787919658664345707868285/8192), (2394187606644804393884038186866271270154637758709848193185002478689191794126186309391667300409153149443881221952150763415675622344015240749758240527177598366155093022444687543904943695/65536), (469096146839176401358125242778192623165992002579188988310387365668400065025080427633969433661118830543716747626080069971703874268834895293803780832590654383496853025522150543910116217/16384), (1072494799595593997822152048412529224153514857037140103480939091942901524194792864901251955818562706063839903092722287801136316520443073050879029822061306944091550092122166014182413519/65536), (450466237294240364248618570163779476645264561558417766193193994122988265049421258826273652123660262390913043916055101838234434781226996517651469935757634430544390774188460266449295953/65536), (2207842341851283560017472909518528552886835368194720862140049199914463878996930820014875624687715547249304246148800724177996425684850600072061608127447484485043952780791250665922939295/1048576), (240523928333725331003190677730956784649145415886652922244357204946569242316804328004687540160095911475214127354793504614132190774089665552067571868332087462199037271966117802409729765/524288), (141528692760466368085795044790316170931030094713120475758038858727961016223044380351502026513205836307566785714605444323465749905387212458659902490890399951571906877285801299894913577/2097152), (12621025316010080696787989512483997314480507977017166930827066856053437605296783502890433242625861270145235209332683161260269357269830649599379607820666489723476752737663792027535521/2097152), (4127909378141116592341584090617775034430753836481335132700779440141954065791764963710784374156618563899623271792731467263422173321211658348162026022357186348067687235937690510635521/16777216)]

theorem b65x_regIdentity_2_0_4_1 (x : ℝ) :
    (b65x_regPoly_2_0_4.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_2_0_4_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_4, b65x_regCoeff_2_0_4_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_4_1 : ∀ i, 0 < b65x_regCoeff_2_0_4_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_4_1]

def b65x_regCoeff_2_0_4_2 : Fin 13 → ℚ :=
  ![(4127909378141116592341584090617775034430753836481335132700779440141954065791764963710784374156618563899623271792731467263422173321211658348162026022357186348067687235937690510635521/16777216), (11909133771249887937498277790591980680915768574297682332652881249170711381532317667616192882157844534806139027469216882850260845351243625934699018559881697685655679648111630540648647/8388608), (126128514636446448292616038426856223438627215321172402575114103634950658533156293246573877150725371049284206948948845784743829938331066616925623459873707508164799256845078733603715273/33554432), (202660502647757686929320022779554563462608905621792578069335165223005593305183500301607154934558796599451825410828521733402731815382392646688371407507894297360644796499451875450559395/33554432), (1760952187161677307910634001764214443281004208385053162123153306136421280039198240023399914091416529499459841073603520877671821815924019972354916922989720394775776074514594194845747295/268435456), (340575451840307679542260992247393984401346403447994318274272380985198001526049022793846086052327276847362977393049137303184273873742326562938024273177007254645957799056702892768082071/67108864), (769851975916685387472390667921082452235925763071911682377396288584968995592964960148800708218752373016933502989338477198614616467860933390876985443778322268010328285372106326872046831/268435456), (320274766183347357253754321062511649553767889363827709741252504109075831961527912288758073407689454072351535261523863580983190877595439912636601643911045085021217319889269843641846831/268435456), (1558004196095957453102143211511569972571821748019733313902819403128503777972162052240487970965569255291362101182350886353594106595313752163289897357580140582671030093124922940174879695/4294967296), (168853985544166084259901328064593865891644702826569299155430517072584435121534722774275502519138096884792181493940818098616970826638021522286823244806387466738035867866507141579153995/2147483648), (99106770356500502806528957259563624373650861702533627188224927941398231128233332106821817262514764928241324907586636393821547770815124014045051473212886684393254756659978436876015593/8589934592), (8842558049207147009812654453077184853677986000806383737717542061133051479342649374017435297237577612077399217615335589882654174432837210711830694605092739967451684135903257563597247/8589934592), (2903697950352340583763199550960453068927125978007276366834741230630621957569457285332879617137700753787478127311480121710252532791527142949684503405116613910660699003209014205820081/68719476736)]

theorem b65x_regIdentity_2_0_4_2 (x : ℝ) :
    (b65x_regPoly_2_0_4.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_2_0_4_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_4, b65x_regCoeff_2_0_4_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_4_2 : ∀ i, 0 < b65x_regCoeff_2_0_4_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_4_2]

def b65x_regCoeff_2_0_4_3 : Fin 13 → ℚ :=
  ![(2903697950352340583763199550960453068927125978007276366834741230630621957569457285332879617137700753787478127311480121710252532791527142949684503405116613910660699003209014205820081/68719476736), (8448165454756771234243487052489707912988161800452719826077586953409494659439816819961045959764151559932504710572649915626964446258069865123499141435864045261042922757074612725186235/34359738368), (91607710185303759308515707867320658280465710171852936324102305193324850637832424800851056104595938793629606716631843858720842297209545698274851716298939393335624324653760968237789825/137438953472), (153433324594851721486350235686926337501470016081948742459275626867971029163143332657170302782064904033921836122037385596254478142712237339977602331878460419244969181887810187609249375/137438953472), (1419160028071827818495846745450660014946611661831040157987660812826210022999954550416875545050476372373668907476684316989038214240733851660744055720961717803181607161740057212449809375/1099511627776), (299264520880444060403474294529947013151432349646262987779538113933002048281296770711840377367343991517837434691837540975474693386161774869113300122129447307962336024381726198021346875/274877906944), (757671424576471600497093532822417537065889407818098762641136528407530167942828395356587449893900756731739153193860217148232022947921882504432328209010120349636810243883860447606734375/1099511627776), (363555573138105948697195267063194988482987828506532730847983078055071877263858286194983501852901826162250145797434431747500204805998689618945847432357001040998763740538195299536796875/1099511627776), (2104349892428532652760275902156976768363055334417322487569792256043736415092317926224502273350613285031145993857832973179120910042748923970118646587525282408482733984492220807537109375/17592186044416), (280222255946484176671428466592978242384667301056697286098443399653215107388428352240524868770910955640321864557733220961383005692012746429922542478868439467439431422511826561318359375/8796093022208), (208675957589683549975951417371470961575209766482016974775218730827211665813578836442240885553987159553168129871128558730577733100870762485954546982810737167934135008827748391337890625/35184372088832), (24368566467133467835999919565547032447092141548571065925981103081080138490727130375280149470742502340023354337874109175346012611172546422116556910321744278123932401961045344091796875/35184372088832), (10783349695350770050705305303442925765088868667869648358264056426308449057422691563128113429541802140206774340373423461338438287824745994796672144819906568681828374314850468994140625/281474976710656)]

theorem b65x_regIdentity_2_0_4_3 (x : ℝ) :
    (b65x_regPoly_2_0_4.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_2_0_4_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_4, b65x_regCoeff_2_0_4_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_4_3 : ∀ i, 0 < b65x_regCoeff_2_0_4_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_4_3]

def b65x_regCoeff_2_0_4_4 : Fin 13 → ℚ :=
  ![(10783349695350770050705305303442925765088868667869648358264056426308449057422691563128113429541802140206774340373423461338438287824745994796672144819906568681828374314850468994140625/281474976710656), (997685327364855289514499543097718106021808056879734893601383274730651085192618039263023852235363010074621085405770151083662781537711445284182440517246928490194090122938257861328125/4398046511104), (444031800926916707144191592860199968548676850830498753536692579869178717383293590145395943320805917179341994847205173392717486770177484807507433356082497120436851844919004658203125/549755813888), (31192596784932021517821945016895894494534224442987542096118532168750591499456436137339017056613927999232197139398160978689593805101645502454160805828461626788129103683979033203125/17179869184), (12619407303995164493080537154627300518087902416093833981615122189168298797685254255567430270948182800690916423081020985226394850592603773496459149104085603135989638702362029296875/4294967296), (116290060636049357170082223202257116270255247668980709461959438276861113250254693474007174470659476158550296105903161147213911676738495692202641416669628926099171056253472890625/33554432), (12682979069460054833074283765375301778330262509020141000243396560907101598898422747434580081252587397961621024854551127954260068290459907290756697159312726786716325539898734375/4194304), (251738263096843174661023690020886857303351538859706176817542493840019590258475114279797541920729795713158865168971372798799945221185657078549546858523332305976958029316303125/131072), (55564164608780697942122145327558892554575729562164827976787913128530055246600470158039218172733932412853209312840957270953196236576164726354893157955818999520173205630434375/65536), (237478116005262195871198470559839294304079920663055331624821107481161242982495799803155958655943772833362026401583482490959926443907551192310398541161898214456569612910625/1024), (3717148129745404698923497355346380599631429584853437008280957699555325641108660346407227934201034214682590308518136372568115984317761184266369813579886358607328076628925/128), (113322747476832273471964614983446588042993110989479021348292654283559918843022826854357746684895632038073384159582621034676404319004707676377901159471317518248022145/4), (9021907032796383899291046813009136550382198568835884664218328736107589444669322178259436359255879158716170706495592982407528641680041692776114845434320540784381)]

theorem b65x_regIdentity_2_0_4_4 (x : ℝ) :
    (b65x_regPoly_2_0_4.comp (C (15/16) + C ((1) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_2_0_4_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_4, b65x_regCoeff_2_0_4_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_4_4 : ∀ i, 0 < b65x_regCoeff_2_0_4_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_4_4]

theorem b65x_regPoly_positive_2_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_2_0_4.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      12 b65x_regCoeff_2_0_4_0 b65x_regIdentity_2_0_4_0
      b65x_regCoeff_positive_2_0_4_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      12 b65x_regCoeff_2_0_4_1 b65x_regIdentity_2_0_4_1
      b65x_regCoeff_positive_2_0_4_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      12 b65x_regCoeff_2_0_4_2 b65x_regIdentity_2_0_4_2
      b65x_regCoeff_positive_2_0_4_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      12 b65x_regCoeff_2_0_4_3 b65x_regIdentity_2_0_4_3
      b65x_regCoeff_positive_2_0_4_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (15/16) (1) (by norm_num)
    12 b65x_regCoeff_2_0_4_4 b65x_regIdentity_2_0_4_4
    b65x_regCoeff_positive_2_0_4_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_2_0_4 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_2_0 4)).eval₂ (Rat.castHom ℝ) t =
      (1600 : ℝ) * b65x_regPoly_2_0_4.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_2_0, b65x_certP5_2_0, b65x_certP7_2_0,
    b65x_certN_2_0, b65x_certD_2_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_2_0_4,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_2_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_2_0 4)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_2_0_4]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_2_0_4 t ht)

def b65x_regPoly_2_0_5 : ℚ[X] :=
  C (297244194612793663093842703177292511489168821108601033621137098550481735600855935378950571686518004566070718406087099659055728982544217518084043922059570312500000000000000000000000000) + X * (C (-3596010319878865992250401379436922617313042734270404582040632585654031023854108569377254727803408555215313605464805057941136288143177239989177320978706359863281250000000000000000000000) + X * (C (19944653679733837912802294898970101254869917878011051287039366020159215041994499212016578601573141499062016433806763146860464749265384491841831647283361539032852172851562500000000000000) + X * (C (-67059931984224731945474909495119537825864611067334196053717665190862845640848779522763980861732305731288462702161818117040359207460710794746671152357018364166259765625000000000000000000) + X * (C (152235844994734072541571256784025235331116514044318347509233142738972589278957751458324484491385411936296546767764279457025705775842667966532022789783868238001377377136230468750000000000) + X * (C (-245821649020575287458757183385530400686822098347182507816359130935395543786163367019137464831646766874178655286316409740623834179737106428198367952792461643530360717773437500000000000000) + X * (C (289508029407440517564340748025367957720085128802545227290666783615753592445089520160835935206173810919772399812583015246705882873345339833662892520735728130318320404867440185546875000000) + X * (C (-250562798353672381480421743779307389396156834411055073199633288538105661317216507955204509667383476239467717251475348743338533921496153839168840843809578384470159218071777343750000000000) + X * (C (158163803240649716303568551056572440665618517023855816037964614637315096097555432825334448133736185834400360215045066808683374360888951803194255174609457610952532343892376081985351562500) + X * (C (-71013596487639658674030076296941641188769717157197328535503858839387642052533346307074308565524129495522510117020505082822738676500131727816941431743140576663429562336601210937500000000) + X * (C (21527068616624551158161944628869704571226924628891177962398834299010703123011545623421581911680131001653129874192505978574337036594639129978188410872382784950391439314669282299152375000) + X * (C (-3955927979057547289794353737993432981231437243252861096436037485883178367114733406464522805116702637437886826876289836926476482209312768563050394742680746531752751852439016489750000000) + X * (C (333270011252983718050253212325308569106772310788963181378382998521895731379480758030352216016915597747774491502195442866284850446277847436409690676453770449959482551288490912340447169) + X * (0)))))))))))))

def b65x_regCoeff_2_0_5_0 : Fin 13 → ℚ :=
  ![(297244194612793663093842703177292511489168821108601033621137098550481735600855935378950571686518004566070718406087099659055728982544217518084043922059570312500000000000000000000000000), (1768925175414090961000911748409048829213504486168010112433328889778765315283216939858779496336511777185191818140642666938100603718941990222419866575361663818359375000000000000000000000), (4826223505044078285016984547540756676780886624183205839531410788274427678957519406439981378784726622441946693197011545536544715376789659213529545293887046135166168212890625000000000000), (7982581719452294382580730325024291460450183763066955101416472477160310576080470715190569652656541267358417145803703434132129424453226134537358560102457124571113586425781250000000000000), (8914695670250151485008772249619413530196211676092386762198241274287154360877829677179329020005792617708331673546004537662773006379708009383325170573876035274427669322967529296875000000), (7081611781797594616138413961603347316571508149532639346043041192715245432126725890755463327262461690193865336587613172935333924743661262388046454046063534936354906372070312500000000000), (4103090258895146386591261277420085744359287178105734352821891723943273577598180674997652565754184916952725093787870714078939477695334871229439408614575999827410544946048870086669921875), (1747127519633001867826603754906608064327339376909146240939483087164782567232803211999832097842094916170305982960798179020199737425404502492215169368946343059817849057812538146972656250), (34727594342503382992598420498101860154899616442137496883956980902913347546102241333050063414711481916057518253777106482907744327356099684000289151103419404141413499059159694324462890625/64), (1918022579494148138358179594098435438587005198343676984415678935616689475303558725215791421290414727533639435382526503030303736774990780559740990647347533323276816241304480701416015625/16), (2288861730450855639443543382575241727963579157120450818944828262517445005727392344053748086630543898090779178042745021127430506439342966700718601286734297876579846941318126946573734375/128), (103494247913883393544831029810302167332991381861525785894401609230437314935185453506926048250020602424791964628193684163879221170142661426280656378497750257622849241543322812128421875/64), (274625392349536431553869001277897238957692662479935363457555504517644804574420473354556941375312956700258007020166161233219233370507174601631788636279689430573344784592086395074947169/4096)]

theorem b65x_regIdentity_2_0_5_0 (x : ℝ) :
    (b65x_regPoly_2_0_5.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_2_0_5_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_5, b65x_regCoeff_2_0_5_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_5_0 : ∀ i, 0 < b65x_regCoeff_2_0_5_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_5_0]

def b65x_regCoeff_2_0_5_1 : Fin 13 → ℚ :=
  ![(274625392349536431553869001277897238957692662479935363457555504517644804574420473354556941375312956700258007020166161233219233370507174601631788636279689430573344784592086395074947169/4096), (815720564523693587267524534536240473291371852535005696807573792971806202206817004080195700377486971505650629130396504476905561612281988594195595670553200753194515196635612561619774521/2048), (8895603417965146819254220021060258914213088024696786145523137694677822478685319187849474022534894348848780286300739747248542858399467857743765709869192254855832153015190800874825559193/8192), (14717634381684996593960628595842381216572524454332659994964510228357675461492015315751645630920562475164859435429879730051012279516177839629448514559146121717898038568995326916266545965/8192), (131667136147983722033038182369201938834365903401123421435949386882665068970662690816434644711336000711823374994666105612817193775348492779687669726584786280447409828760078872648084241055/65536), (26211836004286825207150968793286403061379859777847148501512724827510486614918956870458069203779131812164481628416386636877308032328849645560211184354846474498312342704383355137492794633/16384), (60963118381099378769874572438448949333649806895697651703753335651708653003319209419624374263025850627276370099611459856430693530508794076784668961513331930365741971707737911976113562431/65536), (26079264747839505299428129594000785184353450399139263865187118102591654612075512320656372260873447524360407791785718476826839404880348517864720936971595316281564987514793248936733901697/65536), (130343906740515349856828129987005796879439854398757466072626840398963721326307423714639350726345028851431312982635095171161350149427513252949413692784897512645678592594683098520661025455/1048576), (14497785626946535105121795774299867180495205106217661020028612417031122542473498920284988261633048715904957284293980264399611504014588139908990078446085812296426283673585337760293258485/524288), (8720496131974861271746747335308042089829798436163352143359962278494246161258448855329599414847240862425780148296642417550387400615993244015524782591385178780707661208109872686498865273/2097152), (795934657752581694924144844799545835928510710475306945362322184333078465811594028847719829739467686551131126906193931036466183124515598338861028684934888827690433343226850889959440529/2097152), (266766035515817838283126745012050942478120576288251530747016538440181064546665675396033895631149185330300254177792418537798592025593779271169060109898124218201936327977636774045940529/16777216)]

theorem b65x_regIdentity_2_0_5_1 (x : ℝ) :
    (b65x_regPoly_2_0_5.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_2_0_5_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_5, b65x_regCoeff_2_0_5_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_5_1 : ∀ i, 0 < b65x_regCoeff_2_0_5_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_5_1]

def b65x_regCoeff_2_0_5_2 : Fin 13 → ℚ :=
  ![(266766035515817838283126745012050942478120576288251530747016538440181064546665675396033895631149185330300254177792418537798592025593779271169060109898124218201936327977636774045940529/16777216), (809025004137197154699851015509366810446063765643649885998504477295472649296803020868865401201407294870440033787743904767254961981312816762799483619213340308436560265345029186494583703/8388608), (9048122252756559327088513096271247932757591119523596417477232698744403328263089206041447136230536868052987332373319079114195261629266438869654196593878282673668532935853295162993648377/33554432), (15419734468853007339370293915428859956609717737559487691989434467326989034039379361363762367953592548183212440336452740355739869579209383873202193027598753087395840350117887505961410355/33554432), (142696185469694406208924469797432823339850176714826872932051559518030488474539070447146171091925002476620922895119326293952221626500824856639889678514050337630963419471565992911049617455/268435456), (29505461367234678022452538536730958267619126640586615975401527748596902163287396523078617807825012515171206418053023317724268450668969186908723516054392952425550495085078114539850821479/67108864), (71554784525920316349973747661063526835324971816653715317268257856445088859212182692889419736361351732217096317630624151481485735941232040934057768282396983143803904913934664446970694719/268435456), (32036456379132099363481654096951088778172256110735381772149160736680996786422776440796482995744050523214303827216934447414012083622383366431667240307936617691423451021568124436237694719/268435456), (168166047753996450425485092637800660973970633641289934880989207131350393079659795823633573310692854991311866222564012907637842941801351397985317203381319258826754848444013124118573105055/4294967296), (19709557701667364387152580551875762593123735247807715742317001274346231130621458449990984161373074396204433321167161680311658459004624456536512498162233191948151584242751827013496545755/2147483648), (12530932240711482431780432887681054026048430966634128569299060978606273899873371755011110954393777532099562475312472503312027948264825123522754612138394026814120944822161417710653164057/8589934592), (1212386157925839509198428034914309508602164901959044252321213642711413224760799863645747991035885725736459102902546272474385508806415759068566443672996495233043745269036914063873065103/8589934592), (431908951793805729854040020481203868139055126125061320306804887317140412122826111666923489549083352475124403849594445754603756859012988726572903395761229612486471467365788773144383969/68719476736)]

theorem b65x_regIdentity_2_0_5_2 (x : ℝ) :
    (b65x_regPoly_2_0_5.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_2_0_5_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_5, b65x_regCoeff_2_0_5_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_5_2 : ∀ i, 0 < b65x_regCoeff_2_0_5_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_5_2]

def b65x_regCoeff_2_0_5_3 : Fin 13 → ℚ :=
  ![(431908951793805729854040020481203868139055126125061320306804887317140412122826111666923489549083352475124403849594445754603756859012988726572903395761229612486471467365788773144383969/68719476736), (1462408250292572550289504114502215796047166331207463378118816700431437259583835277710815423869978720803201428841257466842662794118285380402023243215858076046290752668218270830553325515/34359738368), (18365714799395416279579117024952909806007329267085885101917094609709252331547260183881985396915950016297596261443332435746540417739277948832400192259123931403191429583412280035250101425/137438953472), (35301969896570425536411004695278471488269585371848239077011399903261004436635548516829654827503966702803509792537998952173334441135198540153159049444671767091146328079321851416293219375/137438953472), (369766123424264085942293898318644945975797392213345606236183514496767521597146925572765262732118357785652434987747577007641228268327621922175729317779688382742962108725308451540440659375/1099511627776), (86789018549795636235389075824451900443015009799508938139597222375010257545103101596942669838854970920264654816531808574607192400370933812269917395223365978833823386881143136964045996875/274877906944), (239531623806248041790897302218997743177708260193675753687095225601936749110686729469830451855363938597947394719993513780579239815747451533237433654728400997762513208046844596557729984375/1099511627776), (122349800983611987306071390058214115410985518949152455603531395049607447728651599489465829217127967999785913691828553932152519847940482756829558798673442762524195472238469490617303046875/1099511627776), (734573136289747619093767575945526807741305649790841697672265085381418040551799363560932654363467446217446846606542321073574894516780961758333105125124138283249271251215826472819318359375/17592186044416), (98739062107893966532452936696642317953441174546096779524542722562744449789681121259141090048585337411806683854123215036693564756317622957021439612552862432192746573315714818379599609375/8796093022208), (72206692882165999788190227188525061486062711208477758048220409251330183508447207372741167808349340341791660287340478590097568361903409170253233400367868650089928637560555736800556640625/35184372088832), (8060447761815344229870385203321614251753789001440970845406107355356855587690902798458885019003568111814924713765335694044145820207606139691257460346259747737280089407777440610498046875/35184372088832), (3323630513133338966622168937745239499995744155427363246035935854901273997802268645516094811362994597069718166648685722115715217251410475535667608539525939836720236982900297980712890625/281474976710656)]

theorem b65x_regIdentity_2_0_5_3 (x : ℝ) :
    (b65x_regPoly_2_0_5.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_2_0_5_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_5, b65x_regCoeff_2_0_5_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_5_3 : ∀ i, 0 < b65x_regCoeff_2_0_5_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_5_3]

def b65x_regCoeff_2_0_5_4 : Fin 13 → ℚ :=
  ![(3323630513133338966622168937745239499995744155427363246035935854901273997802268645516094811362994597069718166648685722115715217251410475535667608539525939836720236982900297980712890625/281474976710656), (238805472198084083749515201239263031029180433105139861587712526168370800714487892261174926885676959924278723272590184037874978943328160864468170659039758971610077692615431666455078125/4398046511104), (71197641494197072337083244703788303864670473529365415132373916331584414167534548573075408832025993518187751311089408608515038853634684214415630539914222101273976422268154323955078125/549755813888), (3455964112159654159856063748598394785507646417077329592187287439159141227890697642014233540878556613604018537428573159630066192595041729857979570148674577590048302966447306611328125/17179869184), (945029541840918365747483355782969117055661835903297838945629732163160380775096271035482043008618629227498809747931454963502700947630327704547730679486314691315988696935063654296875/4294967296), (5692868948150256842996438361058737501947369867819944431362846181059438346235252366320700428202567118223659901420628541168398616338040517829821771711453586962441868133976890390625/33554432), (380257428598820822910713136402396199580916204302799994450199141774226398580299911581046297302962051563623202711129317429764863536235977638995460561458236997389134270309178609375/4194304), (4154606496918236332757514396295808870145401790133482850011819679060295085199870677327400239017615275036321621080749827490353310187075284487347822649492376605479382436389478125/131072), (467372787429009496604099244955869199121165997347872408614841836409196043460941830814284463604574732296633589886466388321198846547291392924184831348409319378649426056228784375/65536), (1871958657884633309114710549718333634281927543469855564379649860421385669190126866512250514879829106570903311516917913517444724100610349814468662460137867413768010290120625/1024), (115841866824353894311612526905072783228831415094081123907888038755247991958021262621643882086948222527471049559587028854357706838386355006789304382232711680046754782042325/128), (934969923444621523206393011783470962554232991918629912249026975529114974282249314533890934120818058904607822339347380825067236786242670544204193281631227446183300060105/4), (20860223234978715927355202549226813018611647832994671265858243193320289673045325260387752523984736601682026619819212491680635181459725568792689954954311938316469384669)]

theorem b65x_regIdentity_2_0_5_4 (x : ℝ) :
    (b65x_regPoly_2_0_5.comp (C (15/16) + C ((1) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_2_0_5_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_2_0_5, b65x_regCoeff_2_0_5_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_2_0_5_4 : ∀ i, 0 < b65x_regCoeff_2_0_5_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_2_0_5_4]

theorem b65x_regPoly_positive_2_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_2_0_5.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      12 b65x_regCoeff_2_0_5_0 b65x_regIdentity_2_0_5_0
      b65x_regCoeff_positive_2_0_5_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      12 b65x_regCoeff_2_0_5_1 b65x_regIdentity_2_0_5_1
      b65x_regCoeff_positive_2_0_5_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      12 b65x_regCoeff_2_0_5_2 b65x_regIdentity_2_0_5_2
      b65x_regCoeff_positive_2_0_5_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      12 b65x_regCoeff_2_0_5_3 b65x_regIdentity_2_0_5_3
      b65x_regCoeff_positive_2_0_5_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (15/16) (1) (by norm_num)
    12 b65x_regCoeff_2_0_5_4 b65x_regIdentity_2_0_5_4
    b65x_regCoeff_positive_2_0_5_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_2_0_5 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_2_0 5)).eval₂ (Rat.castHom ℝ) t =
      (64 : ℝ) * b65x_regPoly_2_0_5.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_2_0, b65x_certP5_2_0, b65x_certP7_2_0,
    b65x_certN_2_0, b65x_certD_2_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_2_0_5,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_2_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_2_0 5)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_2_0_5]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_2_0_5 t ht)

theorem b65x_certFactors_ne_zero_2_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1))
    (j : Fin 6) : b65x_cpEval (b65x_certFactors_2_0 j) t ≠ 0 := by
  apply b65x_cpEval_ne_zero
  fin_cases j

  · exact b65x_certFactor_norm_positive_2_0_0 t ht

  · exact b65x_certFactor_norm_positive_2_0_1 t ht

  · exact b65x_certFactor_norm_positive_2_0_2 t ht

  · exact b65x_certFactor_norm_positive_2_0_3 t ht

  · exact b65x_certFactor_norm_positive_2_0_4 t ht

  · exact b65x_certFactor_norm_positive_2_0_5 t ht

theorem b65x_certND_ratio_2_0 (t : ℝ) :
    b65b_inverseNormalization (b65x_piece 2 0 t) =
      b65x_cpEval b65x_certN_2_0 t / b65x_cpEval b65x_certD_2_0 t := by
  have hQ : (1 + t ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hQc : (((1 + t ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ
  push_cast at hQc
  have hrel : b65x_cpEval b65x_certD_2_0 t =
      (12500000000000 : ℂ) * (1) *
        (((b65b_boxCentre 6).1 : ℂ) - b65x_piece 2 0 t *
          (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ))) := by
    norm_num [b65x_cpEval, b65x_certD_2_0, Polynomial.eval₂_pow,
      b65x_piece, b65x_centre, b65x_radius, b65x_et, mr_centre, mr_basePoint,
      b65b_vertex0, b65b_track, b65b_radius, b65b_boxCentre]
    push_cast
    field_simp [hQc]
    <;> ring
  have hnrel : b65x_cpEval b65x_certN_2_0 t =
      (12500000000000 : ℂ) * (1) *
        (((b65b_boxCentre 0).1 : ℂ) * ((b65b_boxCentre 6).1 : ℂ)) := by
    norm_num [b65x_cpEval, b65x_certN_2_0, Polynomial.eval₂_pow, b65b_boxCentre]
    all_goals push_cast
    all_goals ring
  unfold b65b_inverseNormalization
  rw [hnrel, hrel]
  have hLQ : (12500000000000 : ℂ) * (1) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    norm_num
  exact (mul_div_mul_left _ _ hLQ).symm

theorem b65x_piece_regular_2_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    ((b65b_boxCentre 6).1 : ℂ) - b65x_piece 2 0 t *
        (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
      b65b_inverseNormalization (b65x_piece 2 0 t) ∈ b65s_regular := by

  have h0 := b65x_certFactors_ne_zero_2_0 t ht 0

  have h1 := b65x_certFactors_ne_zero_2_0 t ht 1

  have h2 := b65x_certFactors_ne_zero_2_0 t ht 2

  have h3 := b65x_certFactors_ne_zero_2_0 t ht 3

  have h4 := b65x_certFactors_ne_zero_2_0 t ht 4

  have h5 := b65x_certFactors_ne_zero_2_0 t ht 5

  change b65x_cpEval b65x_certD_2_0 t ≠ 0 at h0
  change b65x_cpEval (b65x_cpSub b65x_certN_2_0 (b65x_cpScale 3 b65x_certD_2_0)) t ≠ 0 at h1
  change b65x_cpEval (b65x_cpSub b65x_certN_2_0 b65x_certD_2_0) t ≠ 0 at h2
  change b65x_cpEval (b65x_cpAdd b65x_certN_2_0 (b65x_cpScale 2 b65x_certD_2_0)) t ≠ 0 at h3
  change b65x_cpEval b65x_certP5_2_0 t ≠ 0 at h4
  change b65x_cpEval b65x_certP7_2_0 t ≠ 0 at h5
  norm_num only [b65x_certFactors_2_0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, b65x_certP5_2_0, b65x_certP7_2_0,
    b65x_cpEval_sub, b65x_cpEval_add, b65x_cpEval_mul, b65x_cpEval_pow,
    b65x_cpEval_scale] at h0 h1 h2 h3 h4 h5
  have hN : b65x_cpEval b65x_certN_2_0 t ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [b65x_cpEval, b65x_certN_2_0, Polynomial.eval₂_pow,
      pow_two, Complex.mul_re] at hr
    skip
  have hreg : b65b_inverseNormalization (b65x_piece 2 0 t) ∈ b65s_regular := by
    rw [b65x_certND_ratio_2_0]
    exact b65x_regular_of_homogeneous _ _ h0 hN h1 h2 h3
      (by simpa only [mul_assoc] using h4) (by simpa only [mul_assoc] using h5)
  refine ⟨?_, hreg⟩
  intro h
  apply hreg.1
  simp [b65b_inverseNormalization, h]

end HodgeLean.Foundations.Program

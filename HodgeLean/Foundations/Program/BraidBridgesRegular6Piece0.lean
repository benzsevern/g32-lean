import HodgeLean.Foundations.Program.BraidBridgesInterval
import HodgeLean.Foundations.Program.BraidBridgesRegular5Piece2

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

def b65x_certN_6_0 : b65x_CPoly := (C (291668908382000) + X * (0), C (0) + X * (0))
def b65x_certD_6_0 : b65x_CPoly := (C (2228834950000000) + X * (C (-2348883827751117) + X * (0)), C (-4112139000000000) + X * (C (4389163783147257) + X * (0)))

def b65x_certP5_6_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_6_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_6_0 (b65x_cpScale 3 b65x_certD_6_0)) 4))
    (b65x_cpScale (5) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_6_0 b65x_certD_6_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_6_0 (b65x_cpScale 2 b65x_certD_6_0)) 3)))

def b65x_certP7_6_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_6_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_6_0 (b65x_cpScale 3 b65x_certD_6_0)) 4))
    (b65x_cpScale (-7) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_6_0 b65x_certD_6_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_6_0 (b65x_cpScale 2 b65x_certD_6_0)) 3)))

def b65x_certFactors_6_0 : Fin 6 → b65x_CPoly :=
  ![b65x_certD_6_0,
    b65x_cpSub b65x_certN_6_0 (b65x_cpScale 3 b65x_certD_6_0),
    b65x_cpSub b65x_certN_6_0 b65x_certD_6_0,
    b65x_cpAdd b65x_certN_6_0 (b65x_cpScale 2 b65x_certD_6_0),
    b65x_certP5_6_0, b65x_certP7_6_0]

def b65x_regPoly_6_0_0 : ℚ[X] :=
  C (10938696194831251250000000000000) + X * (C (-23284125938848847723862150000000) + X * (C (12391006975781140173970920685869) + X * (0)))

def b65x_regCoeff_6_0_0_0 : Fin 3 → ℚ :=
  ![(10938696194831251250000000000000), (10235329420238078638068925000000), (9577539877408449726246620685869/4)]

theorem b65x_regIdentity_6_0_0_0 (x : ℝ) :
    (b65x_regPoly_6_0_0.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_0_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_0, b65x_regCoeff_6_0_0_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_0_0 : ∀ i, 0 < b65x_regCoeff_6_0_0_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_0_0]

def b65x_regCoeff_6_0_0_1 : Fin 3 → ℚ :=
  ![(9577539877408449726246620685869/4), (8261960791749191902602012057607/4), (7128690633144108879392486172821/16)]

theorem b65x_regIdentity_6_0_0_1 (x : ℝ) :
    (b65x_regPoly_6_0_0.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_0_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_0, b65x_regCoeff_6_0_0_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_0_1 : ∀ i, 0 < b65x_regCoeff_6_0_0_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_0_1]

def b65x_regCoeff_6_0_0_2 : Fin 3 → ℚ :=
  ![(7128690633144108879392486172821/16), (4862150315933942832973434403249/16), (3324845706940475988294713607581/64)]

theorem b65x_regIdentity_6_0_0_2 (x : ℝ) :
    (b65x_regPoly_6_0_0.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_0_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_0, b65x_regCoeff_6_0_0_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_0_2 : ∀ i, 0 < b65x_regCoeff_6_0_0_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_0_2]

def b65x_regCoeff_6_0_0_3 : Fin 3 → ℚ :=
  ![(3324845706940475988294713607581/64), (250236488953542298937272016245/64), (92570103833405416541154320525/256)]

theorem b65x_regIdentity_6_0_0_3 (x : ℝ) :
    (b65x_regPoly_6_0_0.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_0_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_0, b65x_regCoeff_6_0_0_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_0_3 : ∀ i, 0 < b65x_regCoeff_6_0_0_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_0_3]

def b65x_regCoeff_6_0_0_4 : Fin 3 → ℚ :=
  ![(92570103833405416541154320525/256), (332657956593564150995844852235/1024), (11789047635940219931270561808029/16384)]

theorem b65x_regIdentity_6_0_0_4 (x : ℝ) :
    (b65x_regPoly_6_0_0.comp (C (15/16) + C ((121/128) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_0_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_0, b65x_regCoeff_6_0_0_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_0_4 : ∀ i, 0 < b65x_regCoeff_6_0_0_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_0_4]

def b65x_regCoeff_6_0_0_5 : Fin 3 → ℚ :=
  ![(11789047635940219931270561808029/16384), (10458415809565963327287182399089/4096), (10608905644526193387962272118549/4096)]

theorem b65x_regIdentity_6_0_0_5 (x : ℝ) :
    (b65x_regPoly_6_0_0.comp (C (121/128) + C ((61/64) - (121/128)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_0_5).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_0, b65x_regCoeff_6_0_0_5, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_0_5 : ∀ i, 0 < b65x_regCoeff_6_0_0_5 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_0_5]

def b65x_regCoeff_6_0_0_6 : Fin 3 → ℚ :=
  ![(10608905644526193387962272118549/4096), (10684150562006308418299816978279/1024), (11129675894820045114801979120109/1024)]

theorem b65x_regIdentity_6_0_0_6 (x : ℝ) :
    (b65x_regPoly_6_0_0.comp (C (61/64) + C ((31/32) - (61/64)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_0_6).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_0, b65x_regCoeff_6_0_0_6, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_0_6 : ∀ i, 0 < b65x_regCoeff_6_0_0_6 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_0_6]

def b65x_regCoeff_6_0_0_7 : Fin 3 → ℚ :=
  ![(11129675894820045114801979120109/1024), (709527410076682091440816261939/16), (45577231763543700108770685869)]

theorem b65x_regIdentity_6_0_0_7 (x : ℝ) :
    (b65x_regPoly_6_0_0.comp (C (31/32) + C ((1) - (31/32)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_0_7).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_0, b65x_regCoeff_6_0_0_7, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_0_7 : ∀ i, 0 < b65x_regCoeff_6_0_0_7 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_0_7]

theorem b65x_regPoly_positive_6_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_6_0_0.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_6_0_0_0 b65x_regIdentity_6_0_0_0
      b65x_regCoeff_positive_6_0_0_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_6_0_0_1 b65x_regIdentity_6_0_0_1
      b65x_regCoeff_positive_6_0_0_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_6_0_0_2 b65x_regIdentity_6_0_0_2
      b65x_regCoeff_positive_6_0_0_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      2 b65x_regCoeff_6_0_0_3 b65x_regIdentity_6_0_0_3
      b65x_regCoeff_positive_6_0_0_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h4 : t ≤ (121/128 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (15/16) (121/128) (by norm_num)
      2 b65x_regCoeff_6_0_0_4 b65x_regIdentity_6_0_0_4
      b65x_regCoeff_positive_6_0_0_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h5 : t ≤ (61/64 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (121/128) (61/64) (by norm_num)
      2 b65x_regCoeff_6_0_0_5 b65x_regIdentity_6_0_0_5
      b65x_regCoeff_positive_6_0_0_5 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h6 : t ≤ (31/32 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (61/64) (31/32) (by norm_num)
      2 b65x_regCoeff_6_0_0_6 b65x_regIdentity_6_0_0_6
      b65x_regCoeff_positive_6_0_0_6 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (31/32) (1) (by norm_num)
    2 b65x_regCoeff_6_0_0_7 b65x_regIdentity_6_0_0_7
    b65x_regCoeff_positive_6_0_0_7 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_6_0_0 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_6_0 0)).eval₂ (Rat.castHom ℝ) t =
      (2 : ℝ) * b65x_regPoly_6_0_0.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_6_0, b65x_certP5_6_0, b65x_certP7_6_0,
    b65x_certN_6_0, b65x_certD_6_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_6_0_0,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_6_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_6_0 0)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_6_0_0]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_6_0_0 t ht)

def b65x_regPoly_6_0_1 : ℚ[X] :=
  C (96540555559049186352228962000000) + X * (C (-207501844303770723474645861918000) + X * (C (111519062782030261565738286172821) + X * (0)))

def b65x_regCoeff_6_0_1_0 : Fin 3 → ℚ :=
  ![(96540555559049186352228962000000), (89330188966213010967134993041000), (82677596410685560025362410336821/4)]

theorem b65x_regIdentity_6_0_1_0 (x : ℝ) :
    (b65x_regPoly_6_0_1.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_1_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_1, b65x_regCoeff_6_0_1_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_1_0 : ∀ i, 0 < b65x_regCoeff_6_0_1_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_1_0]

def b65x_regCoeff_6_0_1_1 : Fin 3 → ℚ :=
  ![(82677596410685560025362410336821/4), (69372411299630658141817244928463/4), (58298322337810654031557624539389/16)]

theorem b65x_regIdentity_6_0_1_1 (x : ℝ) :
    (b65x_regPoly_6_0_1.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_1_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_1, b65x_regCoeff_6_0_1_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_1_1 : ∀ i, 0 < b65x_regCoeff_6_0_1_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_1_1]

def b65x_regCoeff_6_0_1_2 : Fin 3 → ℚ :=
  ![(58298322337810654031557624539389/16), (36150144414170645811038383761241/16), (22926351087470228683661323060229/64)]

theorem b65x_regIdentity_6_0_1_2 (x : ℝ) :
    (b65x_regPoly_6_0_1.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_1_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_1, b65x_regCoeff_6_0_1_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_1_2 : ∀ i, 0 < b65x_regCoeff_6_0_1_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_1_2]

def b65x_regCoeff_6_0_1_3 : Fin 3 → ℚ :=
  ![(22926351087470228683661323060229/64), (42331466609009851796229847778663/128), (83349178254585416996995899438461/1024)]

theorem b65x_regIdentity_6_0_1_3 (x : ℝ) :
    (b65x_regPoly_6_0_1.comp (C (7/8) + C ((29/32) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_1_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_1, b65x_regCoeff_6_0_1_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_1_3 : ∀ i, 0 < b65x_regCoeff_6_0_1_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_1_3]

def b65x_regCoeff_6_0_1_4 : Fin 3 → ℚ :=
  ![(83349178254585416996995899438461/1024), (80721668327716843806068307200731/1024), (101009023074555968802027917221901/4096)]

theorem b65x_regIdentity_6_0_1_4 (x : ℝ) :
    (b65x_regPoly_6_0_1.comp (C (29/32) + C ((59/64) - (29/32)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_1_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_1, b65x_regCoeff_6_0_1_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_1_4 : ∀ i, 0 < b65x_regCoeff_6_0_1_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_1_4]

def b65x_regCoeff_6_0_1_5 : Fin 3 → ℚ :=
  ![(101009023074555968802027917221901/4096), (10143677373419562497979805010585/512), (5728716168426924546721800564725/256)]

theorem b65x_regIdentity_6_0_1_5 (x : ℝ) :
    (b65x_regPoly_6_0_1.comp (C (59/64) + C ((15/16) - (59/64)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_1_5).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_1, b65x_regCoeff_6_0_1_5, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_1_5 : ∀ i, 0 < b65x_regCoeff_6_0_1_5 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_1_5]

def b65x_regCoeff_6_0_1_6 : Fin 3 → ℚ :=
  ![(5728716168426924546721800564725/256), (1156243966794691264726824863315/8), (557774037308724443321386254821)]

theorem b65x_regIdentity_6_0_1_6 (x : ℝ) :
    (b65x_regPoly_6_0_1.comp (C (15/16) + C ((1) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_1_6).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_1, b65x_regCoeff_6_0_1_6, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_1_6 : ∀ i, 0 < b65x_regCoeff_6_0_1_6 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_1_6]

theorem b65x_regPoly_positive_6_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_6_0_1.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_6_0_1_0 b65x_regIdentity_6_0_1_0
      b65x_regCoeff_positive_6_0_1_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_6_0_1_1 b65x_regIdentity_6_0_1_1
      b65x_regCoeff_positive_6_0_1_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_6_0_1_2 b65x_regIdentity_6_0_1_2
      b65x_regCoeff_positive_6_0_1_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (29/32 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (29/32) (by norm_num)
      2 b65x_regCoeff_6_0_1_3 b65x_regIdentity_6_0_1_3
      b65x_regCoeff_positive_6_0_1_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h4 : t ≤ (59/64 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (29/32) (59/64) (by norm_num)
      2 b65x_regCoeff_6_0_1_4 b65x_regIdentity_6_0_1_4
      b65x_regCoeff_positive_6_0_1_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h5 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (59/64) (15/16) (by norm_num)
      2 b65x_regCoeff_6_0_1_5 b65x_regIdentity_6_0_1_5
      b65x_regCoeff_positive_6_0_1_5 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (15/16) (1) (by norm_num)
    2 b65x_regCoeff_6_0_1_6 b65x_regIdentity_6_0_1_6
    b65x_regCoeff_positive_6_0_1_6 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_6_0_1 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_6_0 1)).eval₂ (Rat.castHom ℝ) t =
      (2 : ℝ) * b65x_regPoly_6_0_1.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_6_0, b65x_certP5_6_0, b65x_certP7_6_0,
    b65x_certN_6_0, b65x_certD_6_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_6_0_1,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_6_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_6_0 1)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_6_0_1]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_6_0_1 t ht)

def b65x_regPoly_6_0_2 : ℚ[X] :=
  C (10331149714059475454028962000000) + X * (C (-22599029556892545710490987306000) + X * (C (12391006975781140173970920685869) + X * (0)))

def b65x_regCoeff_6_0_2_0 : Fin 3 → ℚ :=
  ![(10331149714059475454028962000000), (9362784649672678052812430347000), (8517546718233950569104794073869/4)]

theorem b65x_regIdentity_6_0_2_0 (x : ℝ) :
    (b65x_regPoly_6_0_2.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_2_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_2, b65x_regCoeff_6_0_2_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_2_0 : ∀ i, 0 < b65x_regCoeff_6_0_2_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_2_0]

def b65x_regCoeff_6_0_2_1 : Fin 3 → ℚ :=
  ![(8517546718233950569104794073869/4), (6827070855356495601689521527607/4), (5629103524271320304309830500821/16)]

theorem b65x_regIdentity_6_0_2_1 (x : ℝ) :
    (b65x_regPoly_6_0_2.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_2_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_2, b65x_regCoeff_6_0_2_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_2_1 : ∀ i, 0 < b65x_regCoeff_6_0_2_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_2_1]

def b65x_regCoeff_6_0_2_2 : Fin 3 → ℚ :=
  ![(5629103524271320304309830500821/16), (3233168862100969709550448447249/16), (2807268327099737794933392471581/64)]

theorem b65x_regIdentity_6_0_2_2 (x : ℝ) :
    (b65x_regPoly_6_0_2.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_2_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_2, b65x_regCoeff_6_0_2_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_2_2 : ∀ i, 0 < b65x_regCoeff_6_0_2_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_2_2]

def b65x_regCoeff_6_0_2_3 : Fin 3 → ℚ :=
  ![(2807268327099737794933392471581/64), (1955467257097273965699280520245/64), (8983802695771284857034472880525/256)]

theorem b65x_regIdentity_6_0_2_3 (x : ℝ) :
    (b65x_regPoly_6_0_2.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_2_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_2, b65x_regCoeff_6_0_2_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_2_3 : ∀ i, 0 < b65x_regCoeff_6_0_2_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_2_3]

def b65x_regCoeff_6_0_2_4 : Fin 3 → ℚ :=
  ![(8983802695771284857034472880525/256), (878541929834251361416899045035/8), (123127132948069917508895379869)]

theorem b65x_regIdentity_6_0_2_4 (x : ℝ) :
    (b65x_regPoly_6_0_2.comp (C (15/16) + C ((1) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_2_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_2, b65x_regCoeff_6_0_2_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_2_4 : ∀ i, 0 < b65x_regCoeff_6_0_2_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_2_4]

theorem b65x_regPoly_positive_6_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_6_0_2.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_6_0_2_0 b65x_regIdentity_6_0_2_0
      b65x_regCoeff_positive_6_0_2_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_6_0_2_1 b65x_regIdentity_6_0_2_1
      b65x_regCoeff_positive_6_0_2_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_6_0_2_2 b65x_regIdentity_6_0_2_2
      b65x_regCoeff_positive_6_0_2_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      2 b65x_regCoeff_6_0_2_3 b65x_regIdentity_6_0_2_3
      b65x_regCoeff_positive_6_0_2_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (15/16) (1) (by norm_num)
    2 b65x_regCoeff_6_0_2_4 b65x_regIdentity_6_0_2_4
    b65x_regCoeff_positive_6_0_2_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_6_0_2 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_6_0 2)).eval₂ (Rat.castHom ℝ) t =
      (2 : ℝ) * b65x_regPoly_6_0_2.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_6_0, b65x_certP5_6_0, b65x_certP7_6_0,
    b65x_certN_6_0, b65x_certD_6_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_6_0_2,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_6_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_6_0 2)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_6_0_2]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_6_0_2 t ht)

def b65x_regPoly_6_0_3 : ℚ[X] :=
  C (11274370967260919464182240500000) + X * (C (-23626674129826998730547731347000) + X * (C (12391006975781140173970920685869) + X * (0)))

def b65x_regCoeff_6_0_3_0 : Fin 3 → ℚ :=
  ![(11274370967260919464182240500000), (10735404869608339563090615326500), (10235142585170820569604419991869/4)]

theorem b65x_regIdentity_6_0_3_0 (x : ℝ) :
    (b65x_regPoly_6_0_3.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_3_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_3, b65x_regCoeff_6_0_3_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_3_0 : ∀ i, 0 < b65x_regCoeff_6_0_3_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_3_0]

def b65x_regCoeff_6_0_3_1 : Fin 3 → ℚ :=
  ![(10235142585170820569604419991869/4), (9234618016295782582632029322607/4), (8388908700280988226081358008821/16)]

theorem b65x_regIdentity_6_0_3_1 (x : ℝ) :
    (b65x_regPoly_6_0_3.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_3_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_3, b65x_regCoeff_6_0_3_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_3_1 : ∀ i, 0 < b65x_regCoeff_6_0_3_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_3_1]

def b65x_regCoeff_6_0_3_2 : Fin 3 → ℚ :=
  ![(8388908700280988226081358008821/16), (6697490068251399512980015381249/16), (5625332447662785321565550175581/64)]

theorem b65x_regIdentity_6_0_3_2 (x : ℝ) :
    (b65x_regPoly_6_0_3.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_3_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_3, b65x_regCoeff_6_0_3_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_3_2 : ∀ i, 0 < b65x_regCoeff_6_0_3_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_3_2]

def b65x_regCoeff_6_0_3_3 : Fin 3 → ℚ :=
  ![(5625332447662785321565550175581/64), (3481017206485556938736619764245/64), (3813746011072226642655199040525/256)]

theorem b65x_regIdentity_6_0_3_3 (x : ℝ) :
    (b65x_regPoly_6_0_3.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_3_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_3, b65x_regCoeff_6_0_3_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_3_3 : ∀ i, 0 < b65x_regCoeff_6_0_3_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_3_3]

def b65x_regCoeff_6_0_3_4 : Fin 3 → ℚ :=
  ![(3813746011072226642655199040525/256), (41591100573333712989822409535/8), (38703813215060907605429838869)]

theorem b65x_regIdentity_6_0_3_4 (x : ℝ) :
    (b65x_regPoly_6_0_3.comp (C (15/16) + C ((1) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_6_0_3_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_3, b65x_regCoeff_6_0_3_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_3_4 : ∀ i, 0 < b65x_regCoeff_6_0_3_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_3_4]

theorem b65x_regPoly_positive_6_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_6_0_3.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_6_0_3_0 b65x_regIdentity_6_0_3_0
      b65x_regCoeff_positive_6_0_3_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_6_0_3_1 b65x_regIdentity_6_0_3_1
      b65x_regCoeff_positive_6_0_3_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_6_0_3_2 b65x_regIdentity_6_0_3_2
      b65x_regCoeff_positive_6_0_3_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      2 b65x_regCoeff_6_0_3_3 b65x_regIdentity_6_0_3_3
      b65x_regCoeff_positive_6_0_3_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (15/16) (1) (by norm_num)
    2 b65x_regCoeff_6_0_3_4 b65x_regIdentity_6_0_3_4
    b65x_regCoeff_positive_6_0_3_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_6_0_3 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_6_0 3)).eval₂ (Rat.castHom ℝ) t =
      (8 : ℝ) * b65x_regPoly_6_0_3.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_6_0, b65x_certP5_6_0, b65x_certP7_6_0,
    b65x_certN_6_0, b65x_certD_6_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_6_0_3,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_6_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_6_0 3)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_6_0_3]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_6_0_3 t ht)

def b65x_regPoly_6_0_4 : ℚ[X] :=
  C (1566435244871510025358757415984027705699661982568758649036122197769528759248027822351083815038595424739330580000679548805944295332296695120798464469043840000000000000000000000000000000000) + X * (C (-20156814679497019008707310889101564479973523131133978888226851442806706860489153564942477141065858102789510977017240688471922357906935345210694507891525875040000000000000000000000000000000) + X * (C (118880697085262096997119885582384920233061337077271683177047177175286806284232606095076253125513529638295722504829022526763693556490298224811429414894017404485220000000000000000000000000000) + X * (C (-424927533961318395239077820387446426435176889074966464433488509253953070366111920251204897070147459229670012085772051884150152339067217757115250802565675524258128700000000000000000000000000) + X * (C (1025226201942607119444418150056186834184555114288041083821508054381716153788529514832969185839131179619828134485994936514793085702923339999648667664627284123400205388490000000000000000000000) + X * (C (-1758972246632760723001859102474916988559227242198024909218459406634713787420141720741999095936161230960635729560621843729141993149139714942172007465512583673914894356301200000000000000000000) + X * (C (2200500938602323695825473839157799313547093571912321057961213776874457789070556963209968921071217022310393367683973068450527877464434475616054168800372391772712603925660915105000000000000000) + X * (C (-2022490489899567120902664098755098510324581820986625855023152585492944155175689621005313034983672780454739061797999786730597359631336912461256508231627583450879007695653523983255000000000000) + X * (C (1355419156262862961826079810798034562434802664312326634784069945260498506320833074389944013497308888515716609547802914309106871865018543577687499965423193625665297741706349258006902500000000) + X * (C (-645941303985987623620568539358668941909551244685861158028987638883701885809924602681004159004625359788095909027481630917424505613580863421033936795970977693770317036734826706457738550000000) + X * (C (207783254218153196650352175542121814838341704141041047198466481035435251008482939320047713020585915521391698220467057760215839513397695697446688632986065502865310975862817235559436692500000) + X * (C (-40507719422180122168573481380350648335473170969565136512983264398586482999747224741758472077564864094412669792549196550164210693198430283256021626890077074677343501821020391339807289691000) + X * (C (3619425225230423177251500595969230873016173194679494949854349778292085605637283468789751415540795948339776793094501590419760515691391597794147428558721599430453518570977676202204729628281) + X * (0)))))))))))))

def b65x_regCoeff_6_0_4_0 : Fin 13 → ℚ :=
  ![(1566435244871510025358757415984027705699661982568758649036122197769528759248027822351083815038595424739330580000679548805944295332296695120798464469043840000000000000000000000000000000000), (8718815598709610799951433547257550228409182225258114344320040651830991680731757085741767209930216045477211471499534241435370365034092668844234319682763142480000000000000000000000000000000), (22242419695601581375067750960483453994588647897619107745398176411173711948737643191756970798063460877027438532657282066287673912566012035516736215277005478401305000000000000000000000000000), (34389151153554625927390568473724569332909981617750883250140348113584770285931923087610338609195287307971730483526431635720344979506894275670730403087017307080783912500000000000000000000000), (35889239277021735873144071805679444742417759605954003987115667574500045984942605920095036879228457289521354484621648448606030647662641907264908504836332202580843049280625000000000000000000), (26634519817187722113576930561382752951846790863484002337572486919698788260587567451712331356003863391031329605817967021536669582992171321113502491672307995685283095610587500000000000000000), (14412967294188173376928028662580522708780517705583323099066747217068410936217993800080632736542995849414790711729631710873363430198272938123148868973039915253809375755064298515625000000000), (5730205443175106812903777011866430806155929045913983574893855378217836970274939648958801970354212090278613599774000315972175541536690808928274315882133750139216783800755134974570312500000), (1661178726578384228711198303057615390716413658690765359333397006703278879226296844634741518639170365724545169896160597223405092043019298872983375470696486619816223708164123927566025390625), (1369819275491399448486338282140890452465378179014115880108231373042599492304296151030539582773901929004588538725528835565382621793443942436965145945477336272772739233823631464042823828125/4), (1524923136383702050010314438596981612415941767626349689893985613576066074910202979354014555608593323365664938581288098886849512236006161578862518158095041285977506325548304018083293515625/32), (1028853154503069438239008775122211377829795407270109065880921678797332347879023485117343143165299009958413794074649796801136745456327793205058308008163479288060395106460728653244610038625/256), (636320145187159852214214413576820932543975320520176864586071553849008476021207677777749437563630063087541309351881688587117425385438462281338397657064607627130420075379568048868520246281/4096)]

theorem b65x_regIdentity_6_0_4_0 (x : ℝ) :
    (b65x_regPoly_6_0_4.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_6_0_4_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_4, b65x_regCoeff_6_0_4_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_4_0 : ∀ i, 0 < b65x_regCoeff_6_0_4_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_4_0]

def b65x_regCoeff_6_0_4_1 : Fin 13 → ℚ :=
  ![(636320145187159852214214413576820932543975320520176864586071553849008476021207677777749437563630063087541309351881688587117425385438462281338397657064607627130420075379568048868520246281/4096), (1611468688672160916971894621702542881576596255601155517750957269451746892674775159530372365411474527954216607868336010079509846643634987711812346880927551491932200252573197826838242062029/2048), (14964931060333075613183488270258836413114955803270115542715007559528006332489470907669924719709162803381083311003753483632143322109080232469311952111112575512350859117190803214704247948457/8192), (21058646089410602022270290244634948812975727671328730456610290981177499974921946483654331508829300573203207244038902912256201261291351793617010734306294884637676329813938021710423564249785/8192), (160043493710348838437869343211588476896949532408184152287869032260249938680182162978301892853913117824177070087886394725093198679738389448467351381174995347069715622131611702999898371446695/65536), (27033495274739455565697207201044206799264573254583458751821592123147107682716590704527944018349302718515270476016079981692007456896948242098363036660460819833443393240276684778404949889517/16384), (53283542782492698276494535011509032744048148297516048085212854229999569340827078176592881099456459753204848059369821394467580772117191063894852937961500405343981602828324416292567793377119/65536), (19293942553561193064449811360573540851549502882119085965161543067765354462495396425410462301680484756629806109003563390522080908185955451703185045389105200401383365427195939048049370392653/65536), (81526114156751310044495070780844069480766122022321618390412941370460375048580537645832641886502653217193162267705242999314841955385726897622326104509909339226314487363135403606948128792295/1048576), (7657226887773463115729625740166254705303888200333470446415025329859282504329135383018234182965241296397899570354076189514719521981124641711493282847388714798626979710212678458897858898265/524288), (3884740390053070523816155635162190767489496968283241371584141629342833911908124662072710619119136957478285520624011815095414024507159190678301719294436781688232204659117400699356759758377/2097152), (298703974329978138833830664066737405734365997436844490259640503844057868166597570289403838904479376691235301595796532422596757111756694897259413089558363838126300437632788261712365045421/2097152), (84243144119630958867795581003336294845484156194861104467821670462679449794865657629238110159774148864914064789359963761933247997549245662966599812719966707272302640808448717160136974921/16777216)]

theorem b65x_regIdentity_6_0_4_1 (x : ℝ) :
    (b65x_regPoly_6_0_4.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_6_0_4_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_4, b65x_regCoeff_6_0_4_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_4_1 : ∀ i, 0 < b65x_regCoeff_6_0_4_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_4_1]

def b65x_regCoeff_6_0_4_2 : Fin 13 → ℚ :=
  ![(84243144119630958867795581003336294845484156194861104467821670462679449794865657629238110159774148864914064789359963761933247997549245662966599812719966707272302640808448717160136974921/16777216), (160780348416722352142498900896551842140625410880060959691114026475999311820595778084335313629008586401755979912646609012205717754429821172180572135362972689198122892010461931016502683447/8388608), (1130250752185562552934262441830305082130470601343240799007056137371493638716719685973254458538192319549559514290814217893058814548878998176044493733873212180131045189050821247955534589473/33554432), (1210742731970142976316412552285774575460346981219413501399376953157468140298303653125556755256315217588372306969078477707169030302056168224738658113467543459248430209428580177784727107395/33554432), (7051877599879753652407703905606734432551818490547823260366376198637909686840674051099550348577227080053733174359672650826398696404116439244928785136850448741291209708968202246323380370295/268435456), (920219273291329706383374305564406237530068542071642775593117755771116125707641861599523918355824597603281986644511333287593192008307081215387318492853844604379022869396859930104356026471/67108864), (1414896285436558093661779005911296043760252687398603650132209474537424577966995666006081108261053259360896826329402319825188472760183192446868823796846505826267896913782774073071982162231/268435456), (404668838658769858634469090293607949443972089485879215736146621774818199380261950067739837456816898005095228856785162860471965388569689089728364637036592086856268302469227747727917069231/268435456), (1374018514559260577317376598535735190849089049952721195596129719076610874343705864309334919919943678352302656827104169849672915757393635023438081947787538608034127980445926092899239722695/4294967296), (106373156793570542875190807743035511346233839487280404810138446091962762875633305923079574199348881538369184790938885604444136129815396558560738253476145661270478805729437193275899831995/2147483648), (46237356068931848285277946846874669777163745399446788563592209915807732035883563114988697413522320155225525412970595882715557560011791081688885997517394077175496135086671511048279185793/8589934592), (3225911467037755038400314937862701137045363353384473327162426246086081263381219952275559801252206920967731510287630304147643678051784397326633088537295653958560298175052416803815462047/8589934592), (892873454063034920033044091078254433192779832414989399024435669262110821959745720165518131568578962116053130643537916977267425320998962774064372480031857095750574097311916139721627481/68719476736)]

theorem b65x_regIdentity_6_0_4_2 (x : ℝ) :
    (b65x_regPoly_6_0_4.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_6_0_4_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_4, b65x_regCoeff_6_0_4_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_4_2 : ∀ i, 0 < b65x_regCoeff_6_0_4_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_4_2]

def b65x_regCoeff_6_0_4_3 : Fin 13 → ℚ :=
  ![(892873454063034920033044091078254433192779832414989399024435669262110821959745720165518131568578962116053130643537916977267425320998962774064372480031857095750574097311916139721627481/68719476736), (1584038152491804203496766943978887624644291784965957936895068531186834870875271576938543581612796817109015155216580644500119471785421870313313175245695405944634570525702411649863723235/34359738368), (24312526483465099322084310639863695676922629178288526579185968950715115499257697648739780964665918801629322095045944725621690057548315823537094929716011543609945688141406119586799114825/137438953472), (55520836703575922347909035635329803476322339354194738994910011441775939010761981207675473356203063990862750271624473732455249892601198798966089304159089708580845000571095948398861874375/137438953472), (715198882074204187351393916818954303017680042497234893433094957543395840784187554907484398907501330169768434388708956734956262875856130155429831235227779610490078690569921026590529184375/1099511627776), (204151491110876007778850199219307657936788645315100734436063948474098571477072566628809018669135748110145947155043496743610070741188701945758272710116495288459293677735923250024431971875/274877906944), (688045662645041879781824654073839669044687445525249590116171359340150684226428666533234944348554770626912765086958545933028946405073755806221644470212080907372930318965436655940328609375/1099511627776), (438208429686017797046594831864509507571767617127876531082534964186357347167702525842092686303220460753416351113987604096558272429941697929149234860512103607993322429534578430160864921875/1099511627776), (3351232539899435668712999991952498161703886929476886742912995357537286805722666534545962935031670835320149896240130355448220287245538936642566072389721543467160981207664799005335271484375/17592186044416), (573258579174728803735897861895070281189532711892059215592405155326134184664318586566281172713684171528807435099893917453525816961803754120482479818962967380268713319982271681594521484375/8796093022208), (508018775053902820023190797515776767093991817936181896419047712822385068579399405639253193945670330265287824582425891390824033643017909693998301499250100183821314691168372093002666015625/35184372088832), (65150843149083288265238804429381179217014604326513128129825959435890209679425546818813419913134960195015602631015521251680163680399228280875940634680677496268652781269182485939794921875/35184372088832), (36767322380447326174746168743669434380235797486621914979023875913851303893303987446719498415960769770446741063349669620549588903462491962122677265172245774386153829935305624150634765625/281474976710656)]

theorem b65x_regIdentity_6_0_4_3 (x : ℝ) :
    (b65x_regPoly_6_0_4.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_6_0_4_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_4, b65x_regCoeff_6_0_4_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_4_3 : ∀ i, 0 < b65x_regCoeff_6_0_4_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_4_3]

def b65x_regCoeff_6_0_4_4 : Fin 13 → ℚ :=
  ![(36767322380447326174746168743669434380235797486621914979023875913851303893303987446719498415960769770446741063349669620549588903462491962122677265172245774386153829935305624150634765625/281474976710656), (5643890499032336282374962725203390490461598516669077100905708538207962750060801940168134416843418639540577569879185951246075378748530950686511395104507478361226088567091798314013671875/4398046511104), (4500341630138003780540010447038783732303934997053379247979132974842085689235452521360959430990728256245109715478492520812451038882767535387124332608739153447719217048616296864033203125/549755813888), (792464167616811291802658521425132008315609378114909264079528935690725273429673195634412333340013684465516214044167382399243629925322845347811606160788650068946128540031955830107421875/17179869184), (887666392672585141052146324432292190509534623046462160212985661494133146659608596533672545332245530229449593493682126064109468418617801913488369436176329371396712420354577654412109375/4294967296), (22125510643033652729841172675335877635993019826608418739034405233809224863009373529340240959628081363021465513759926294558734526690093788766360177463366006740471801992207022320546875/33554432), (6078979840569580683006849765862980512578065555572157034929459530508768007011618946151919829901369642759395317231281168860738629094771921276253093001481874966977532279954799106546875/4194304), (284313555397002364496371299770226020150783667776209812441936298579360564651017749683979810758430069834607097291732399230658626723807448367135412147866045277553042310584192838334375/131072), (141028745014938329053047654028729870266559840051167896058267167653437352883332359108551826501949843447511867641628740718049220725427015469481784510009630666594367417587036750434375/65536), (1340705309119890162393448031754793087797894673038671544571818904485053234744141979055492165378939143953004949236015947633663220828070443963979038428613841939872858547374551254375/1024), (49171896062973613205247022693849224435626379842934948421548948412444017372821993701103806184420365653253335990890421600038931530806571439483821505646012847338802697566856053925/128), (9353324880796624563810379679895641976994056320210146964987684805497083578814519936364254537443358861991161408128250735415734713521268093867165643614130719143759528821004895/4), (4603765902897623772586335862072258435897650596750032205416166152924785571098374348361746574720430200682929129057967198518980940872294576019400259780488193715998082437281)]

theorem b65x_regIdentity_6_0_4_4 (x : ℝ) :
    (b65x_regPoly_6_0_4.comp (C (15/16) + C ((1) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_6_0_4_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_4, b65x_regCoeff_6_0_4_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_4_4 : ∀ i, 0 < b65x_regCoeff_6_0_4_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_4_4]

theorem b65x_regPoly_positive_6_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_6_0_4.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      12 b65x_regCoeff_6_0_4_0 b65x_regIdentity_6_0_4_0
      b65x_regCoeff_positive_6_0_4_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      12 b65x_regCoeff_6_0_4_1 b65x_regIdentity_6_0_4_1
      b65x_regCoeff_positive_6_0_4_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      12 b65x_regCoeff_6_0_4_2 b65x_regIdentity_6_0_4_2
      b65x_regCoeff_positive_6_0_4_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      12 b65x_regCoeff_6_0_4_3 b65x_regIdentity_6_0_4_3
      b65x_regCoeff_positive_6_0_4_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (15/16) (1) (by norm_num)
    12 b65x_regCoeff_6_0_4_4 b65x_regIdentity_6_0_4_4
    b65x_regCoeff_positive_6_0_4_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_6_0_4 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_6_0 4)).eval₂ (Rat.castHom ℝ) t =
      (102400 : ℝ) * b65x_regPoly_6_0_4.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_6_0, b65x_certP5_6_0, b65x_certP7_6_0,
    b65x_certN_6_0, b65x_certD_6_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_6_0_4,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_6_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_6_0 4)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_6_0_4]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_6_0_4 t ht)

def b65x_regPoly_6_0_5 : ℚ[X] :=
  C (77920782152576182018072301581708168131816671440693109357579363562417484097350778323979618664190575788968042405845296653023505018400071357060623609904384000000000000000000000000000000000000) + X * (C (-1000169529129322195357874835479622826245059179986841521312210972382644146224344875060817294660004811454932768430419682356188844263667385500011041359463589584000000000000000000000000000000000) + X * (C (5885359541687152051610900846923640531174920646907836644490853999209974246737356307104951607371583973324992480243568540437310072669459740858932302861478353994974500000000000000000000000000000) + X * (C (-20993523537264026415268688299524912526115792298629453789275660216818013824346711044594493048130054392073435627279886717333636023200305697834563537950503720938311515500000000000000000000000000) + X * (C (50558907748183438409533990129225077447131316669019933916951084388387319090006817502605647249974692570950057626280873425189343430314776172453448930617735787768822087600250000000000000000000000) + X * (C (-86605031602634333428859421567966967031043185275892437532808042185635598461823661238364060908126631841748308436412246947672826581129894265872575879528455906620380356962563000000000000000000000) + X * (C (108195813246865006193281784778454758178496031647406704547463745673609839901867657636890803448169906093029647950326703159019077017108348850428833532191766908056854127977331164625000000000000000) + X * (C (-99329626777465249957377975807026177264396534956980715529581146382308256281561630582960357619575314836797404769954286117550634786989328980623019865176125545684819203455100299663875000000000000) + X * (C (66507118365572080709216925976422599610668268139848374150818677381742656014420577479702449299778485343529081578776883588105286257847230917115539378572945779494892753497089252485851562500000000) + X * (C (-31672966073764411713867513437432814494023626833511802671314269622182326089375157805196166112139616419361502394522918476671341585666819951512537294346269960600599543022898411225407842750000000) + X * (C (10183724251447641073247738329104146476091970823255813818856169024732271512336750671766159041867265349902532681335184466128488867065827412915621969695835545868206954063391384750917039604500000) + X * (C (-1984878251686825986260100587637181768438185377508691689136179955530737666987614012346165131800678340626220819834910630958046323966723083879545059717613776659189831589229999175650557194859000) + X * (C (177351836036290735685323529202492312777792486539295252542863139136312194676226889970697819361499001468649062861630577930568265268878188291913223999377358372092222409977906133908031751785769) + X * (0)))))))))))))

def b65x_regCoeff_6_0_5_0 : Fin 13 → ℚ :=
  ![(77920782152576182018072301581708168131816671440693109357579363562417484097350778323979618664190575788968042405845296653023505018400071357060623609904384000000000000000000000000000000000000), (434964621266253086537930201240686604459270467294896551634846876557687736056036902357346776640284503740150124654933718658187638088967163534721962639120813208000000000000000000000000000000000), (1113179097280543951627185520985723685145804986885076011505791146817504707875593633324397613049447532401008692479373461249840205931599024530673506492009189786743625000000000000000000000000000), (1727118434570276498753014452154656529433367847255252110149335714131816369047739054291107890384497492865619944648359510296548565570773737221043871703598686310147310562500000000000000000000000), (1809313611176024745962349929878656784315168247797436231140812263294664731210817701527238286231364865015156519076626160854787088181227703371542759907847222443414050537515625000000000000000000), (1348264127938012888996981199035783401536151941240977163248485374809075563716820897634280589308805610638491053460347341021292631247233383220831708873467369069357337895044906250000000000000000), (732817755637192907172299129499487944635556547466344074574759470937635318653880071320318128574234132191779426672849535207289450458938333174354592137570393940509133214522643197265625000000000), (292723562456972427657210430889167995679828297706685899587665982209904001323374924764234105255576624328059254854511064077843860752616461182601839728701366276907252690074856842469726562500000), (85286783630120828243829394761150814593810149041791994781546442771708138640496595200247380436540183989643635104811918560021343823776613912119964638256736618974359626360609895887115478515625), (70703373023119149777096641883032378709169902210852529637065175238457094847301414360837663985754242212999185721005618861911722496434832425556154181324273763001785747933671578956286384765625/4), (79153582774241891597603645148825593967461374806322805873232852711765111709598342247662080134221797800813142794557618637466444902819241450215683836118397211307746712914453560903358847015625/32), (53722572335851552838649559604470931456933961163037522043411572937942722608847865856169123821680741896883314677698885483378893697654449642303808576003068392574243370468289945046686027892625/256), (33434564291514058411838281220489023791810502913928954144568892587801052477818582295444123093259972315463453242182497086404251398054020593415020362389817180638565697245143512637333780067769/4096)]

theorem b65x_regIdentity_6_0_5_0 (x : ℝ) :
    (b65x_regPoly_6_0_5.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_6_0_5_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_5, b65x_regCoeff_6_0_5_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_5_0 : ∀ i, 0 < b65x_regCoeff_6_0_5_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_5_0]

def b65x_regCoeff_6_0_5_1 : Fin 13 → ℚ :=
  ![(33434564291514058411838281220489023791810502913928954144568892587801052477818582295444123093259972315463453242182497086404251398054020593415020362389817180638565697245143512637333780067769/4096), (86020789280220314351946292566517488298558681573210499127473741538438581864975777234320612552616783251637820468846931844122687791868386771519948957496081055450117793333131833549259909039421/2048), (813135795466346461159119076429752175454681605999653137363208416513000966590576259568628998364690976167491676867383459847887202821700863489859349076543068533749551904704105658777987525474393/8192), (1167010717266015711816478616390037305324778572461849309944744818007463124347066794900812575063029814887090540995090379538489952373564980724445269917450335478247879808679519328417506808239465/8192), (9063438591233805553045487603532735980703946741970372860140178469284100098322790718672739962848610489396652563743881718103541519075025651007640549944788461050418452252500772066459506920888055/65536), (1567574357186823823092969418055627059066213295417920061893002698201481245022731698192492001711306331148033908143029648935183397610205591377745775188905622766873163972529593391892376240586333/16384), (3169977051187258454386824104333205046665026880707732509532357458792013005687679301304103273872734876656570984188599412921672713531699677673754193235221859049014599139068165843494121603478831/65536), (1180027225884682738454601695328511233666719541700521252201807597994393343816870402183487854992339076679018550692293262831054699194915494339047077536268016046581848458430373187537879533239997/65536), (5136296978729469348585377960769940634015712115961009082060184975821930576792667967381504546921910487328284304020144195459752585500728311914161481460603799222346779770146326843098238630822455/1048576), (497946739673902996029625938153975898118535713742912073397232551349878715654447836981199074012202830752398043797991567914265553747302497418168399243939036773218044135235722178537699726014985/524288), (261279815232683485914064303207825060839000033593028531667998106424418757780690379915622039791204289141077225329872649695887239263324601096294101573246046483984186232699734034710177884160473/2097152), (20820336951700764149209881419679858002661944130696599278408754600213277049751919665646560402101816976957898326600643566158159649223430492077113441363885770242587659632959651155475839225629/2097152), (6097436921662508582158347337759246149693359791464258200197715898685088833389689005318550882458517787320163381472954211826326459571907479118117659323874280175741228032003743220019959771129/16777216)]

theorem b65x_regIdentity_6_0_5_1 (x : ℝ) :
    (b65x_regPoly_6_0_5.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_6_0_5_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_5, b65x_regCoeff_6_0_5_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_5_1 : ∀ i, 0 < b65x_regCoeff_6_0_5_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_5_1]

def b65x_regCoeff_6_0_5_2 : Fin 13 → ℚ :=
  ![(6097436921662508582158347337759246149693359791464258200197715898685088833389689005318550882458517787320163381472954211826326459571907479118117659323874280175741228032003743220019959771129/16777216), (13236258391561048941005363200473499341916349861785125244961933887739245401003361716573837137923026131965673780055300774120618837700306327908832051187096981096495733022114386669227959488903/8388608), (107773549039998124861582024748055093463551367185047707380758440378993844072245758376751798177557098439954846505673048963090841848662100729078376852141925476110318584753373922663828810884177/33554432), (135775243054853923394213878327117575051030906573205454570967030002308379935127802995683057744734809427572447561126312504626665554142505766361317588956888374120761470993768692117634668262355/33554432), (941294350756862693136341910703906445280218043645190756507305068149896834277751037567366628974732468093303511756139889405007641726570410934580354305374035806442086050323656919516976518144455/268435456), (147443792694435861327245968676804324176369952045712160221954880272326930167579501637834927306875715487946475463506919759199500644415223000202548818381718803643053755796650801771798693297079/67108864), (273347550641081583258060284137473614918077861146247468836761880839674465024348851682460385205607080884654569810415743847463786057261858547129606564338343736261538459149122494806092629949319/268435456), (94245993492318563115485397664586139698860396499461184607264337468731092321664789125100516509451180955611321535851962844590474713783398670780230268456537651702948524543905813997237408392319/268435456), (383319350093586681218023965523192871950990674697816108108263531900030899923160581182925756919931703652966673236665483930938491009251019863731245855395295659494260055596322302720600986412055/4294967296), (35002785848725310025246757851965386218234582689740834736799376590184525959927431644755475395881694115598947687145408206094559561373191321916216200028434510584858423746741425122931571767755/2147483648), (17435235062173912381591987322672132471739740448729666252336133626207414097780458460929389829394880203286483732788152076127376128498043928356031510103397685488172220782545690305774064103857/8589934592), (1329885349697372550960556038537000142693892590041536770401563587761509180856012420701232193055084467484910080944287180487578026818661327175660886541073881301093887138292784439442125640303/8589934592), (376334223594005082337502346598641653255355492779501458588604735782802535764276526526831608691353610613691887918410489067893078292276690293059558001905227760904123559442184798592151746569/68719476736)]

theorem b65x_regIdentity_6_0_5_2 (x : ℝ) :
    (b65x_regPoly_6_0_5.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_6_0_5_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_5, b65x_regCoeff_6_0_5_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_5_2 : ∀ i, 0 < b65x_regCoeff_6_0_5_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_5_2]

def b65x_regCoeff_6_0_5_3 : Fin 13 → ℚ :=
  ![(376334223594005082337502346598641653255355492779501458588604735782802535764276526526831608691353610613691887918410489067893078292276690293059558001905227760904123559442184798592151746569/68719476736), (727237312951300639116409042313774593910414254932439586494315446522204460166463897339020092112013560553406829377120040635881650993167558286214248934999287245949337758394094308445114438515/34359738368), (5967338496061982253812749143601082068205721264947744517153747447802797640118322689623897615640393457404294958274615733313449226735057543275577743557691055196820478029864100398604740626425/137438953472), (8361642777330984513785683091957572375757008042291560552303085604536314749906399895844654378765748223668915894121126502005065932453276307321326963142505781471141075840597848224632231844375/137438953472), (72871061429471214121162963144553468761076979026835659705008698784366111962338428570702405913147997611964225560901226081907149766985540317300211359282791890733174614884164205859671930034375/1099511627776), (15645173823652981025489411186578491045097743478600836873541048096704473361157039897398227956506264256748401918248910285644970011469633638976619575451579130762505305824145747509277166621875/274877906944), (42172838329329541031364442293873398228430657977115299565081496084898217560814780008879153855020757258822639116743223274987413306607509208572733074636653669418327352304275710932276101859375/1099511627776), (22180270391440089823612383715023857830906075630755394865318887987718034377932396558756227237625802197034338310247183869545284542031732380486154533016054219814328035428030761500282381171875/1099511627776), (144651070829470595198406915096543289397545197753849544995410473327480998605654138409743471176220884041686501555767602186746435738220415650522447125259407766401196752972044469061428302734375/17592186044416), (22325609263086256887449759030823663188861306096384951336845112652184722562623112147523462248306839159212194427996442616622940273527229657252436321124660851562294405933651720698131552734375/8796093022208), (21247926000222279521122374520624050185438912271620608562144401023504918818696570142994549469190321402003307101945161344549048229475167448500932776783267225747665940508630149057130634765625/35184372088832), (3444805046248114147700495901141354740515789358816380710972752604731227265096209586009404851798832759628485948109137883432528320561165801005109460521019701001673488889647276811049951171875/35184372088832), (2096364822977002632523630753997237924548542790621981638896357899649763248356069971632391454627775476943954624943150672144660165893873634695255781677755556149731506282635595583381103515625/281474976710656)]

theorem b65x_regIdentity_6_0_5_3 (x : ℝ) :
    (b65x_regPoly_6_0_5.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_6_0_5_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_5, b65x_regCoeff_6_0_5_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_5_3 : ∀ i, 0 < b65x_regCoeff_6_0_5_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_5_3]

def b65x_regCoeff_6_0_5_4 : Fin 13 → ℚ :=
  ![(2096364822977002632523630753997237924548542790621981638896357899649763248356069971632391454627775476943954624943150672144660165893873634695255781677755556149731506282635595583381103515625/281474976710656), (11977673314296795397311684983692431839905306397965073328121715887385414705012210572672713388052313773238619728270080282436884851922531110247083114057760603344236578764425806628330029296875/140737488355328), (252897790320307832447542373069017038584588662537448727152392556465477361043839396793557019463764677989407606865490194392066523874307253565820249476651868547240020594543851945434116728515625/562949953421312), (799015452243862619241845126546810830459398866371582732931969562488800779984325729124275777006366722076072400105270383276576680577140414179432945913656243623056134012011650576224272724609375/562949953421312), (13149266699665321547843713450576341868797720898608311778720816711744350370968700449623510891649324648506984545891630004669478845698456994969455762730696240058876028944084567136745533615234375/4503599627370496), (4495383043194563580056271000030910085428242483967636215514096490445297034075188947428470086623149539818851299667988241966573081406773581390577701651071992070261532788003016857298299081796875/1125899906842624), (16032418881535574708620354014807317343098454550596508269358872364047587323605642309689587677325591174158751674280711074338910099248299520282559371392318915884932111890711281141017995698609375/4503599627370496), (8971646433481230530136099071058737497665372963827953774621992702266473237186012927118858155930651610221873015216584387080271508794904858933222555780756251397673512368439715722375355857696875/4503599627370496), (60547890987764265868076183450904137743646998711176736268879528716279788578807725080763642124828905412073326063785345040152310386093939151335208335477155668790277354347397610144004484427034375/72057594037927936), (24534892532147555069022302226393793219443867268346733637596609869183757344713665377544502674198312790827363092165316991608014635822926925185346840513299365703771851924939310910203651941189375/36028797018963968), (99457330197170957171841448419415198736539296597950446067712948410643265200633098654100520088864502263309695410022668631126011918593214158999094941038756364160757099222419713521282808591814825/144115188075855872), (54480756345658144523131512175435362868955843574815242328753501619763330955767570656464555274320044358136393376289335903527469299811660860063292883984968771030584537673430769051794251968055755/144115188075855872), (94200641758671726369854735632528353984561545030155767870778202687227966795556313843957221966881021228557216338357017842429734784359591691825068223033654191222404092064234269142520625033623209/1152921504606846976)]

theorem b65x_regIdentity_6_0_5_4 (x : ℝ) :
    (b65x_regPoly_6_0_5.comp (C (15/16) + C ((31/32) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_6_0_5_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_5, b65x_regCoeff_6_0_5_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_5_4 : ∀ i, 0 < b65x_regCoeff_6_0_5_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_5_4]

def b65x_regCoeff_6_0_5_5 : Fin 13 → ℚ :=
  ![(94200641758671726369854735632528353984561545030155767870778202687227966795556313843957221966881021228557216338357017842429734784359591691825068223033654191222404092064234269142520625033623209/1152921504606846976), (14257573058147314661652043420134356192795549469728253830223819152620035589431335679712944414145188707970953477423857351485108440829194638463244486569749612664789233657454502398485476445800867/9007199254740992), (7849616674331479483859978345442472254336100484168575994417252349431144095418378519775268081878504792682410860536870576381652090650793754171226183021406373874325126205182319047206991763297477/562949953421312), (648765980510120662197256403811229665972062059512972265994220383519186411095418140430921573696527814062223236540935188672765294581855307523610295779384321427160666292890955019942910378326195/8796093022208), (286872405395263177439274593557163867141407966635364984595756014885217338946836446683508708899022996222014820873773746426669217476687005065402477016327909653516034855993637272425165235603855/1099511627776), (2794462987867033790158940711556134467588472062107588762294408139670012230123705489364597981412579988480481424426915603691501085446317968358304041962081546278494815714116818862190187411291/4294967296), (315105445282984382352734342471405465511129539411083098836195415381871708594207397611718248765460770134406600268664208536208702468634676575437139467267551335803114958854711485225361735659/268435456), (6481837207714468385053149312598903805085377469188742107041067983397276341573074785653395839116994551258369670993255876409868867859008578760672782742894675148682221826600396730180685031/4194304), (1546643345271227733027354184673957071227395793783864159700096003462924805294292277623767879366522655099898185060207450264941839959781662026543498273028744725010026460079375683911271255/1048576), (8163122843288426157688774851677035175066967640352742467317051103663312533431843895688959664781746156425645892846569587119206650662005010472915925088579950762073499370688125022529095/8192), (231849844460388642676226476306602190011208262755206135384390681847605860318180821112019314318911833188578998751367368572289768805836272658264368965829499502360589113710538040415797/512), (995486226105483699808411175915234299016180977470703509428287317198698655671248229597909891635762774033815639584746604449656945188333233056024839644330349503566565118564703724767/8), (15657603161355846746814209733161908708707053463635523213973823617707842627970755322265932124605796020480920423270076181988199097283470611617468542195018247997930743233911426769)]

theorem b65x_regIdentity_6_0_5_5 (x : ℝ) :
    (b65x_regPoly_6_0_5.comp (C (31/32) + C ((1) - (31/32)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_6_0_5_5).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_6_0_5, b65x_regCoeff_6_0_5_5, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_6_0_5_5 : ∀ i, 0 < b65x_regCoeff_6_0_5_5 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_6_0_5_5]

theorem b65x_regPoly_positive_6_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_6_0_5.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      12 b65x_regCoeff_6_0_5_0 b65x_regIdentity_6_0_5_0
      b65x_regCoeff_positive_6_0_5_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      12 b65x_regCoeff_6_0_5_1 b65x_regIdentity_6_0_5_1
      b65x_regCoeff_positive_6_0_5_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      12 b65x_regCoeff_6_0_5_2 b65x_regIdentity_6_0_5_2
      b65x_regCoeff_positive_6_0_5_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      12 b65x_regCoeff_6_0_5_3 b65x_regIdentity_6_0_5_3
      b65x_regCoeff_positive_6_0_5_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h4 : t ≤ (31/32 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (15/16) (31/32) (by norm_num)
      12 b65x_regCoeff_6_0_5_4 b65x_regIdentity_6_0_5_4
      b65x_regCoeff_positive_6_0_5_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (31/32) (1) (by norm_num)
    12 b65x_regCoeff_6_0_5_5 b65x_regIdentity_6_0_5_5
    b65x_regCoeff_positive_6_0_5_5 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_6_0_5 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_6_0 5)).eval₂ (Rat.castHom ℝ) t =
      (4096 : ℝ) * b65x_regPoly_6_0_5.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_6_0, b65x_certP5_6_0, b65x_certP7_6_0,
    b65x_certN_6_0, b65x_certD_6_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_6_0_5,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_6_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_6_0 5)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_6_0_5]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_6_0_5 t ht)

theorem b65x_certFactors_ne_zero_6_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1))
    (j : Fin 6) : b65x_cpEval (b65x_certFactors_6_0 j) t ≠ 0 := by
  apply b65x_cpEval_ne_zero
  fin_cases j

  · exact b65x_certFactor_norm_positive_6_0_0 t ht

  · exact b65x_certFactor_norm_positive_6_0_1 t ht

  · exact b65x_certFactor_norm_positive_6_0_2 t ht

  · exact b65x_certFactor_norm_positive_6_0_3 t ht

  · exact b65x_certFactor_norm_positive_6_0_4 t ht

  · exact b65x_certFactor_norm_positive_6_0_5 t ht

theorem b65x_certND_ratio_6_0 (t : ℝ) :
    b65b_inverseNormalization (b65x_piece 6 0 t) =
      b65x_cpEval b65x_certN_6_0 t / b65x_cpEval b65x_certD_6_0 t := by
  have hQ : (1 + t ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hQc : (((1 + t ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ
  push_cast at hQc
  have hrel : b65x_cpEval b65x_certD_6_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 6).1 : ℂ) - b65x_piece 6 0 t *
          (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ))) := by
    norm_num [b65x_cpEval, b65x_certD_6_0, Polynomial.eval₂_pow,
      b65x_piece, b65x_centre, b65x_radius, b65x_et, mr_centre, mr_basePoint,
      b65b_vertex0, b65b_track, b65b_radius, b65b_boxCentre]
    push_cast
    field_simp [hQc]
    <;> ring
  have hnrel : b65x_cpEval b65x_certN_6_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 0).1 : ℂ) * ((b65b_boxCentre 6).1 : ℂ)) := by
    norm_num [b65x_cpEval, b65x_certN_6_0, Polynomial.eval₂_pow, b65b_boxCentre]
    all_goals push_cast
    all_goals ring
  unfold b65b_inverseNormalization
  rw [hnrel, hrel]
  have hLQ : (50000000000000 : ℂ) * (1) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    norm_num
  exact (mul_div_mul_left _ _ hLQ).symm

theorem b65x_piece_regular_6_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    ((b65b_boxCentre 6).1 : ℂ) - b65x_piece 6 0 t *
        (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
      b65b_inverseNormalization (b65x_piece 6 0 t) ∈ b65s_regular := by

  have h0 := b65x_certFactors_ne_zero_6_0 t ht 0

  have h1 := b65x_certFactors_ne_zero_6_0 t ht 1

  have h2 := b65x_certFactors_ne_zero_6_0 t ht 2

  have h3 := b65x_certFactors_ne_zero_6_0 t ht 3

  have h4 := b65x_certFactors_ne_zero_6_0 t ht 4

  have h5 := b65x_certFactors_ne_zero_6_0 t ht 5

  change b65x_cpEval b65x_certD_6_0 t ≠ 0 at h0
  change b65x_cpEval (b65x_cpSub b65x_certN_6_0 (b65x_cpScale 3 b65x_certD_6_0)) t ≠ 0 at h1
  change b65x_cpEval (b65x_cpSub b65x_certN_6_0 b65x_certD_6_0) t ≠ 0 at h2
  change b65x_cpEval (b65x_cpAdd b65x_certN_6_0 (b65x_cpScale 2 b65x_certD_6_0)) t ≠ 0 at h3
  change b65x_cpEval b65x_certP5_6_0 t ≠ 0 at h4
  change b65x_cpEval b65x_certP7_6_0 t ≠ 0 at h5
  norm_num only [b65x_certFactors_6_0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, b65x_certP5_6_0, b65x_certP7_6_0,
    b65x_cpEval_sub, b65x_cpEval_add, b65x_cpEval_mul, b65x_cpEval_pow,
    b65x_cpEval_scale] at h0 h1 h2 h3 h4 h5
  have hN : b65x_cpEval b65x_certN_6_0 t ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [b65x_cpEval, b65x_certN_6_0, Polynomial.eval₂_pow,
      pow_two, Complex.mul_re] at hr
    skip
  have hreg : b65b_inverseNormalization (b65x_piece 6 0 t) ∈ b65s_regular := by
    rw [b65x_certND_ratio_6_0]
    exact b65x_regular_of_homogeneous _ _ h0 hN h1 h2 h3
      (by simpa only [mul_assoc] using h4) (by simpa only [mul_assoc] using h5)
  refine ⟨?_, hreg⟩
  intro h
  apply hreg.1
  simp [b65b_inverseNormalization, h]

end HodgeLean.Foundations.Program

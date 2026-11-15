import HodgeLean.Foundations.Program.BraidBridgesInterval
import HodgeLean.Foundations.Program.BraidBridgesRegular0Piece2

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

def b65x_certN_1_0 : b65x_CPoly := (C (29166890838200) + X * (0), C (0) + X * (0))
def b65x_certD_1_0 : b65x_CPoly := (C (222883495000000) + X * (C (-267289035000000) + X * (0)), C (-411213900000000) + X * (C (411064789727721) + X * (0)))

def b65x_certP5_1_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_1_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_1_0 (b65x_cpScale 3 b65x_certD_1_0)) 4))
    (b65x_cpScale (5) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_1_0 b65x_certD_1_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_1_0 (b65x_cpScale 2 b65x_certD_1_0)) 3)))

def b65x_certP7_1_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_1_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_1_0 (b65x_cpScale 3 b65x_certD_1_0)) 4))
    (b65x_cpScale (-7) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_1_0 b65x_certD_1_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_1_0 (b65x_cpScale 2 b65x_certD_1_0)) 3)))

def b65x_certFactors_1_0 : Fin 6 → b65x_CPoly :=
  ![b65x_certD_1_0,
    b65x_cpSub b65x_certN_1_0 (b65x_cpScale 3 b65x_certD_1_0),
    b65x_cpSub b65x_certN_1_0 b65x_certD_1_0,
    b65x_cpAdd b65x_certN_1_0 (b65x_cpScale 2 b65x_certD_1_0),
    b65x_certP5_1_0, b65x_certP7_1_0]

def b65x_regPoly_1_0_0 : ℚ[X] :=
  C (218773923896625025000000000000) + X * (C (-457219739265186831043800000000) + X * (C (240417689585126705161315853841) + X * (0)))

def b65x_regCoeff_1_0_0_0 : Fin 3 → ℚ :=
  ![(218773923896625025000000000000), (208937978160656634478100000000), (201073906641253143073715853841/4)]

theorem b65x_regIdentity_1_0_0_0 (x : ℝ) :
    (b65x_regPoly_1_0_0.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_0_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_0, b65x_regCoeff_1_0_0_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_0_0 : ∀ i, 0 < b65x_regCoeff_1_0_0_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_0_0]

def b65x_regCoeff_1_0_0_1 : Fin 3 → ℚ :=
  ![(201073906641253143073715853841/4), (185345763602446160264947561523/4), (177505117429898773926242684569/16)]

theorem b65x_regIdentity_1_0_0_1 (x : ℝ) :
    (b65x_regPoly_1_0_0.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_0_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_0, b65x_regCoeff_1_0_0_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_0_1 : ∀ i, 0 < b65x_regCoeff_1_0_0_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_0_1]

def b65x_regCoeff_1_0_0_2 : Fin 3 → ℚ :=
  ![(177505117429898773926242684569/16), (161823825084804001248832930661/16), (177692520204747614451676838209/64)]

theorem b65x_regIdentity_1_0_0_2 (x : ℝ) :
    (b65x_regPoly_1_0_0.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_0_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_0, b65x_regCoeff_1_0_0_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_0_2 : ∀ i, 0 < b65x_regCoeff_1_0_0_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_0_2]

def b65x_regCoeff_1_0_0_3 : Fin 3 → ℚ :=
  ![(177692520204747614451676838209/64), (3967173779985903300710976887/4), (1971874216564899117515853841)]

theorem b65x_regIdentity_1_0_0_3 (x : ℝ) :
    (b65x_regPoly_1_0_0.comp (C (7/8) + C ((1) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_0_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_0, b65x_regCoeff_1_0_0_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_0_3 : ∀ i, 0 < b65x_regCoeff_1_0_0_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_0_3]

theorem b65x_regPoly_positive_1_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_1_0_0.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_1_0_0_0 b65x_regIdentity_1_0_0_0
      b65x_regCoeff_positive_1_0_0_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_1_0_0_1 b65x_regIdentity_1_0_0_1
      b65x_regCoeff_positive_1_0_0_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_1_0_0_2 b65x_regIdentity_1_0_0_2
      b65x_regCoeff_positive_1_0_0_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (7/8) (1) (by norm_num)
    2 b65x_regCoeff_1_0_0_3 b65x_regIdentity_1_0_0_3
    b65x_regCoeff_positive_1_0_0_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_1_0_0 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_1_0 0)).eval₂ (Rat.castHom ℝ) t =
      (1 : ℝ) * b65x_regPoly_1_0_0.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_1_0, b65x_certP5_1_0, b65x_certP7_1_0,
    b65x_certN_1_0, b65x_certD_1_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_1_0_0,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_1_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_1_0 0)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_1_0_0]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_1_0_0 t ht)

def b65x_regPoly_1_0_1 : ℚ[X] :=
  C (1930811111180983727044579240000) + X * (C (-4068201712750124564572200000000) + X * (C (2163759206266140346451842684569) + X * (0)))

def b65x_regCoeff_1_0_1_0 : Fin 3 → ℚ :=
  ![(1930811111180983727044579240000), (1827521365986905171803058480000), (1750600225489826125485759644569/4)]

theorem b65x_regIdentity_1_0_1_0 (x : ℝ) :
    (b65x_regPoly_1_0_1.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_1_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_1, b65x_regCoeff_1_0_1_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_1_0 : ∀ i, 0 < b65x_regCoeff_1_0_1_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_1_0]

def b65x_regCoeff_1_0_1_1 : Fin 3 → ℚ :=
  ![(1750600225489826125485759644569/4), (1596757944495668032851161973707/4), (1548390082289507975913452001121/16)]

theorem b65x_regIdentity_1_0_1_1 (x : ℝ) :
    (b65x_regPoly_1_0_1.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_1_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_1, b65x_regCoeff_1_0_1_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_1_1 : ∀ i, 0 < b65x_regCoeff_1_0_1_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_1_1]

def b65x_regCoeff_1_0_1_2 : Fin 3 → ℚ :=
  ![(1548390082289507975913452001121/16), (1451654357877187862038032055949/16), (1776816308616859890950162903881/64)]

theorem b65x_regIdentity_1_0_1_2 (x : ℝ) :
    (b65x_regPoly_1_0_1.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_1_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_1, b65x_regCoeff_1_0_1_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_1_2 : ∀ i, 0 < b65x_regCoeff_1_0_1_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_1_2]

def b65x_regCoeff_1_0_1_3 : Fin 3 → ℚ :=
  ![(1776816308616859890950162903881/64), (81290487684918007228032711983/4), (26368604696999508924221924569)]

theorem b65x_regIdentity_1_0_1_3 (x : ℝ) :
    (b65x_regPoly_1_0_1.comp (C (7/8) + C ((1) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_1_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_1, b65x_regCoeff_1_0_1_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_1_3 : ∀ i, 0 < b65x_regCoeff_1_0_1_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_1_3]

theorem b65x_regPoly_positive_1_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_1_0_1.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_1_0_1_0 b65x_regIdentity_1_0_1_0
      b65x_regCoeff_positive_1_0_1_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_1_0_1_1 b65x_regIdentity_1_0_1_1
      b65x_regCoeff_positive_1_0_1_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_1_0_1_2 b65x_regIdentity_1_0_1_2
      b65x_regCoeff_positive_1_0_1_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (7/8) (1) (by norm_num)
    2 b65x_regCoeff_1_0_1_3 b65x_regIdentity_1_0_1_3
    b65x_regCoeff_positive_1_0_1_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_1_0_1 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_1_0 1)).eval₂ (Rat.castHom ℝ) t =
      (1 : ℝ) * b65x_regPoly_1_0_1.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_1_0, b65x_certP5_1_0, b65x_certP7_1_0,
    b65x_certN_1_0, b65x_certD_1_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_1_0_1,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_1_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_1_0 1)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_1_0_1]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_1_0_1 t ht)

def b65x_regPoly_1_0_2 : ℚ[X] :=
  C (206622994281189509080579240000) + X * (C (-441627759053001192769800000000) + X * (C (240417689585126705161315853841) + X * (0)))

def b65x_regCoeff_1_0_2_0 : Fin 3 → ℚ :=
  ![(206622994281189509080579240000), (192432109035878421776258480000), (183654148603882355944032813841/4)]

theorem b65x_regIdentity_1_0_2_0 (x : ℝ) :
    (b65x_regPoly_1_0_2.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_2_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_2, b65x_regCoeff_1_0_2_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_2_0 : ∀ i, 0 < b65x_regCoeff_1_0_2_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_2_0]

def b65x_regCoeff_1_0_2_1 : Fin 3 → ℚ :=
  ![(183654148603882355944032813841/4), (166098227739890224279581481523/4), (170194006129158178503510524569/16)]

theorem b65x_regIdentity_1_0_2_1 (x : ℝ) :
    (b65x_regPoly_1_0_2.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_2_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_2, b65x_regCoeff_1_0_2_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_2_1 : ∀ i, 0 < b65x_regCoeff_1_0_2_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_2_1]

def b65x_regCoeff_1_0_2_2 : Fin 3 → ℚ :=
  ![(170194006129158178503510524569/16), (2047889194633977111964521523/2), (5412924813315021472095093841)]

theorem b65x_regIdentity_1_0_2_2 (x : ℝ) :
    (b65x_regPoly_1_0_2.comp (C (3/4) + C ((1) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_2_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_2, b65x_regCoeff_1_0_2_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_2_2 : ∀ i, 0 < b65x_regCoeff_1_0_2_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_2_2]

theorem b65x_regPoly_positive_1_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_1_0_2.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_1_0_2_0 b65x_regIdentity_1_0_2_0
      b65x_regCoeff_positive_1_0_2_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_1_0_2_1 b65x_regIdentity_1_0_2_1
      b65x_regCoeff_positive_1_0_2_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (3/4) (1) (by norm_num)
    2 b65x_regCoeff_1_0_2_2 b65x_regIdentity_1_0_2_2
    b65x_regCoeff_positive_1_0_2_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_1_0_2 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_1_0 2)).eval₂ (Rat.castHom ℝ) t =
      (1 : ℝ) * b65x_regPoly_1_0_2.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_1_0, b65x_certP5_1_0, b65x_certP7_1_0,
    b65x_certN_1_0, b65x_certD_1_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_1_0_2,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_1_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_1_0 2)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_1_0_2]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_1_0_2 t ht)

def b65x_regPoly_1_0_3 : ℚ[X] :=
  C (225487419345218389283644810000) + X * (C (-465015729371279650180800000000) + X * (C (240417689585126705161315853841) + X * (0)))

def b65x_regCoeff_1_0_3_0 : Fin 3 → ℚ :=
  ![(225487419345218389283644810000), (218466974004796953476889620000), (212335908223440961934295093841/4)]

theorem b65x_regIdentity_1_0_3_0 (x : ℝ) :
    (b65x_regPoly_1_0_3.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_3_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_3, b65x_regCoeff_1_0_3_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_3_0 : ∀ i, 0 < b65x_regCoeff_1_0_3_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_3_0]

def b65x_regCoeff_1_0_3_1 : Fin 3 → ℚ :=
  ![(212335908223440961934295093841/4), (200073776660728978849106041523/4), (191369163334278772820559644569/16)]

theorem b65x_regIdentity_1_0_3_1 (x : ℝ) :
    (b65x_regPoly_1_0_3.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_3_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_3, b65x_regCoeff_1_0_3_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_3_1 : ∀ i, 0 < b65x_regCoeff_1_0_3_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_3_1]

def b65x_regCoeff_1_0_3_2 : Fin 3 → ℚ :=
  ![(191369163334278772820559644569/16), (173959936681378360763466850661/16), (170780782973525056932944678209/64)]

theorem b65x_regIdentity_1_0_3_2 (x : ℝ) :
    (b65x_regPoly_1_0_3.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_3_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_3, b65x_regCoeff_1_0_3_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_3_2 : ∀ i, 0 < b65x_regCoeff_1_0_3_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_3_2]

def b65x_regCoeff_1_0_3_3 : Fin 3 → ℚ :=
  ![(170780782973525056932944678209/64), (164422475557818449271900333305/64), (214984459922300274517138474225/256)]

theorem b65x_regIdentity_1_0_3_3 (x : ℝ) :
    (b65x_regPoly_1_0_3.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_3_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_3, b65x_regCoeff_1_0_3_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_3_3 : ∀ i, 0 < b65x_regCoeff_1_0_3_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_3_3]

def b65x_regCoeff_1_0_3_4 : Fin 3 → ℚ :=
  ![(214984459922300274517138474225/256), (6320248045560228155654767615/8), (889379559065444264160663841)]

theorem b65x_regIdentity_1_0_3_4 (x : ℝ) :
    (b65x_regPoly_1_0_3.comp (C (15/16) + C ((1) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_1_0_3_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_3, b65x_regCoeff_1_0_3_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_3_4 : ∀ i, 0 < b65x_regCoeff_1_0_3_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_3_4]

theorem b65x_regPoly_positive_1_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_1_0_3.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_1_0_3_0 b65x_regIdentity_1_0_3_0
      b65x_regCoeff_positive_1_0_3_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_1_0_3_1 b65x_regIdentity_1_0_3_1
      b65x_regCoeff_positive_1_0_3_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_1_0_3_2 b65x_regIdentity_1_0_3_2
      b65x_regCoeff_positive_1_0_3_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      2 b65x_regCoeff_1_0_3_3 b65x_regIdentity_1_0_3_3
      b65x_regCoeff_positive_1_0_3_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (15/16) (1) (by norm_num)
    2 b65x_regCoeff_1_0_3_4 b65x_regIdentity_1_0_3_4
    b65x_regCoeff_positive_1_0_3_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_1_0_3 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_1_0 3)).eval₂ (Rat.castHom ℝ) t =
      (4 : ℝ) * b65x_regPoly_1_0_3.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_1_0, b65x_certP5_1_0, b65x_certP7_1_0,
    b65x_certN_1_0, b65x_certD_1_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_1_0_3,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_1_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_1_0 3)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_1_0_3]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_1_0_3 t ht)

def b65x_regPoly_1_0_4 : ℚ[X] :=
  C (100251855671776641622960474622977773164778366884400553538311820657249840591873780630469364162470107183317157120043491123580434901266988487731101726018805760000000000000000000000) + X * (C (-1265139642425943873257702562167095035788466115961003888677549779726523625575989465143900799634299505280642819244627930206103807043426483300231947610867200000000000000000000000000) + X * (C (7323269341074725641776404344226121533082245918085663277009772440892355338584531813408966992217779630690710183672793527653944428635824174880259610815238375342144000000000000000000) + X * (C (-25711416993308414420167159971819472839380113033236295072479833441676006153085418090000895111552238084784560100323331638100286628480829579086843725945843298560000000000000000000000) + X * (C (60980185193705896922192500901065334337594033564576799094880753814908174013141745575070919252187666692492242076983949413283257180294672937916653211641211649979105105600000000000000) + X * (C (-102926359830917327269095167778183412332936195678985937358356573416999042502623381378501273004994489109044118830185267847564808380032899091109350912527406586427896000000000000000000) + X * (C (126773621888790810194772033992918581266222958745828432239882901950168631920241397851695706933406535533220145095140476288193492307362190789041293063762923905869857681355640000000000) + X * (C (-114808835686189811485549803999092610870823463763514758636168052632312521546967367520862293874077754367331607986920794957340840658856272294117498313871316948513683561200000000000000) + X * (C (75872873783960620608832221142380698068439701057238712942511510051741839029454619669677595563018629523499711275759964304852528749440004175744538078693239456604036754817950881000000) + X * (C (-35684013566548072797013863003583168289644786586415194027861306857953236723783353247312018546573762991219907594140979390021316535856893797003640452859057873001981439457000000000000) + X * (C (11337146821936547699026944793355080557086586646770298154168269036302469167182067649587218944434710254131484899656644134176647092136191451621877655801173228850837706162466691828000) + X * (C (-2184690387467740091991218770051066888607397626211304550464687552436253086029433131164411023226250592084362161614371835819830686188241525739091378254934546542044847086211800000000) + X * (C (193107221717574850014706209954024954544598652310178867140142324208082050204857644998598659578531690160040651645201998477464667642078086756578538834330909371867104357653259187041) + X * (0)))))))))))))

def b65x_regCoeff_1_0_4_0 : Fin 13 → ℚ :=
  ![(100251855671776641622960474622977773164778366884400553538311820657249840591873780630469364162470107183317157120043491123580434901266988487731101726018805760000000000000000000000), (570452446848347762846674414392185760083107344632304698120966958023736274314490634993681970132491533559484475818207928379913315293490620202657246906792069120000000000000000000000), (1489171776263248454642128319254040715309370056106330965054499485105698373041860416671765384788824702728074409995615179936223871903731625759041904761281173995536000000000000000000), (2358314309600666944384599821547866339851523191700136148260433524136952804198173719518293717400606501240802483823867330892166227613965916359257381720154793235360000000000000000000), (2523345601614383864538498770152200962989103554854383038816668849485723495634637185752323405808476038257584770006399795743007133924980178707771932192698591042814069100000000000000), (1921776306257047424340710054888169190057186999206256259672905033066974925741237627310381086252979618660400647488335030440847638820385650622912158718786947828000802800000000000000), (1068239934997837601607856715325491285690761728345230839509914263814634716431799034533676833054473375545552930568265995951336875757253517364471354477759275534108211071181875000000), (436670696961177517995177813277414252683339484831711089192346107447560732027101111287967031170336263673871887265253897325618838058450400110622440158341311253669124405216250000000), (521121503495570911963917974015570159335010825668065379816143804220286399478521575148211400345283136714784379728565745392198314506575743892242035585544231439700942127442982515625/4), (27666529199491637817724996818285218274379650266586128569655460795075727661651763218603126818321385511978809362428248877244370020882080981279782895588316688606696099978529390625), (127027575602334837824726311456010466683618222193003963606023022359795932392777205461420687606354911552955387400125575913184828040463270557503838301555806902378345300152744869625/32), (5528308349432225988139665188015950543024329709369864535861256493746139004861935743216243886629007677146281437171589308679032016946111470548408551178834658501522788570024682125/16), (56513731218185101583284387257182865466671506579412484772695014027521864384199026305837589543656286301006003871349933086497138551320440991925208584980289048557478227270522499041/4096)]

theorem b65x_regIdentity_1_0_4_0 (x : ℝ) :
    (b65x_regPoly_1_0_4.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_1_0_4_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_4, b65x_regCoeff_1_0_4_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_4_0 : ∀ i, 0 < b65x_regCoeff_1_0_4_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_4_0]

def b65x_regCoeff_1_0_4_1 : Fin 13 → ℚ :=
  ![(56513731218185101583284387257182865466671506579412484772695014027521864384199026305837589543656286301006003871349933086497138551320440991925208584980289048557478227270522499041/4096), (154811846600003451008620913281624954446486457815041032659134710647943883146627349186698697148650085371692022863167682023016197877332834812228729989377183292919845576953122835369/2048), (1562768542348682217116001194388605817618234982059453848797945167617242238708035383019273924151702942522035152786173745273247904751445438685554880859319891663352873789336596575177/8192), (2402029026953963733299584176417226518305153509889840797822399720238834908044141426192472384062238271570590936352727360855716469319532296408538931761385592929567907366964960195885/8192), (20034088406989950175283296592043292215431951046531762594788795850272074969704109509356243305458003967430674411217671129743525851450279205153325769694541661250829623664235898488895/65536), (3731187419570298440601178490404473932186428854665363084380556279263581597595762710367766561989516900319908588331189195468644785893317753245201119562278745873241528904780434349337/16384), (8146322860253377471041762383310610967190380401378080438470104606561529770631321051262279078584597731407735731604603924706271640072240157237026527715091057153115938103502409789359/65536), (3282545479815177333836229696922114886773248095110863245787075860694195323890556934085552760226107139737794454538706618876258794253925911420059536101167413406103973894074981824033/65536), (15505944468576603227941330735609218394413397400771838967002844264671082571347713175812193403081576064405889867685497315304840331655588831043219659980330729423897952787260038000495/1048576), (1635584283933023000020886958896943738388387703055813778542270199205275350273579279118800224701062002818890770534526068436304179490529393297421017975960620887369153082715513000165/524288), (936166982081406727089889817318175487894367612362889180175524443072130781821806443641079590812882304804379788375393188407582388101663485586288326137858441024086069907769226216297/2097152), (81586242442587162912340779805435887752057998171603912211361124199220447692492574093180706487810477730248045592223817508210780028182610391096270294786379192006843597006459504081/2097152), (26199700775865590135502312716121173697695153184560494392203207523555792372049039010062274051127498528735916383070752585168234603147344235437600770698092996890965242450941408081/16777216)]

theorem b65x_regIdentity_1_0_4_1 (x : ℝ) :
    (b65x_regPoly_1_0_4.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_1_0_4_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_4, b65x_regCoeff_1_0_4_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_4_1 : ∀ i, 0 < b65x_regCoeff_1_0_4_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_4_1]

def b65x_regCoeff_1_0_4_2 : Fin 13 → ℚ :=
  ![(26199700775865590135502312716121173697695153184560494392203207523555792372049039010062274051127498528735916383070752585168234603147344235437600770698092996890965242450941408081/16777216), (72624822097615985394839254834218787775140382317836625107106619313561235963456202904199053484526531298127156263189138250092551371960877336745866346710078588004999988045553664567/8388608), (756595056336201674174763211643153356521275186614307143286782012487494366376770580252960500045413221859344301100042360341472265821310608645413054536965330828057601834153848526553/33554432), (1221520287419329693229855743973393433094839406511301665367555205937752564044926963207951194156404627938931830805871012810666007948595891237460977111974194642519193807682550936595/33554432), (10874634077375925687397803480820105046538559126876854022700390871835891004714669478936073395717941364789348949776333266165737884826251568493461310070148449353631081062529348228495/268435456), (2193610178794905245508127200610098414441746122926173512416828094683722482343768161728220470642696909051048574583858024626845027600718828668232674679009455223240164810705408362631/67108864), (5256268074530068649474052108790525266202829838248414674806820828670182513967155391936802884699401235227996581623004992601107986118700033125773923897727402028049604506021772064991/268435456), (2352028216209478857437142993775401706702032852380022850300646627989668241658110716435394172940591961859690060791526954238888337509750294213628550556756317479358942691720178496991/268435456), (12465495665163758080352312473351694468601662849563905527911677179949040960452586145933817163122080577844881866070235142765807139410275994552016753249108717681063533178558431264895/4294967296), (1488232334973112330104003034005390992855837092726723528060781707868349729693061991464684426120675190387736867053918958652054063342943433983107047459722791295938380204814774547195/2147483648), (971286358111125513468912111169472467898667983783046565478924164517049946530221726036018618021401540181438197700461684661981430152753543031412468879862576737354633731121758734073/8589934592), (97151416016239765143300514620445628731506665867266618509012183520290036033497098525474240600849787455489631491274724695128593529730805879942984807607205444187125468742539869167/8589934592), (36068813123840990471948772049122568090541349637972641066924227106518032220062788349926261329416086706473349368972182905513256084459927390797840128487216892007894426276605370241/68719476736)]

theorem b65x_regIdentity_1_0_4_2 (x : ℝ) :
    (b65x_regPoly_1_0_4.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_1_0_4_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_4, b65x_regCoeff_1_0_4_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_4_2 : ∀ i, 0 < b65x_regCoeff_1_0_4_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_4_2]

def b65x_regCoeff_1_0_4_3 : Fin 13 → ℚ :=
  ![(36068813123840990471948772049122568090541349637972641066924227106518032220062788349926261329416086706473349368972182905513256084459927390797840128487216892007894426276605370241/68719476736), (2763755838820801568136450381730518885029345761662826172940124449816015156672816631076135846849618165982604153910456005352793680912244073112633894463611307959139452521819060389/2147483648), (1514127427537710368163141696294586424586617047267382093072226349110263565959848376446996792089817342142927129281236078193113955365838598062220459536388400093649342869616176897/536870912), (135254632821603598690807506550047052881413024645945937796898624366246769049368422816715688398108895680603198777338534828273873920718191733942806062355031577766892424494088785/33554432), (152467819203342569713264723561316713653182227642728605492819521710734554864472667372476586734435700378685931916470665290545332021341490897836462762253538162514895480578821295/16777216), (4594745461640130067208713918978933319917566068901902854661082556645727036334134916125032347030320541158711708919927342756822525488301839090912381118196302108012297548756037/262144), (1913037054421800814229227158193636966505003844006059437683052987951596859528057663655984618808048180360516190480819672114752651516687123303423628362855587708347057137284679/65536), (140992294082893054809264332106308308080650278014117337552143701994582195735202375966496345171591871311248775067953809631663509174229586938784161244360661169135834371484613/4096), (129308399684478099993854967386425230614210333514452191443512977294834571961785217081164798913950257848676685616622649115787441783680584155948726210209614774304106511213295/4096), (2679101359350145453950222566867516545531669734856610010206320684016905130277229942087637666169269775616371389220630236827903351975474502968535742802356487566890739968465/128), (336520182779502412755015349429759766966380235755422225715615567138122660602429578810007368167284453927214812417816017028724445675058613617161239682465232398377401991297/32), (6687873171817322706649618172884986499806982128576162712658593566204727970826873589792026223604100217941730987657990942141991255553979257528063766985193828820949229861/2), (642621162855773625992232954480147369991595123657757775217721336151152084683348947528781632451847549699558707728163953665834092274530204709878732242504550499032015041)]

theorem b65x_regIdentity_1_0_4_3 (x : ℝ) :
    (b65x_regPoly_1_0_4.comp (C (7/8) + C ((1) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_1_0_4_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_4, b65x_regCoeff_1_0_4_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_4_3 : ∀ i, 0 < b65x_regCoeff_1_0_4_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_4_3]

theorem b65x_regPoly_positive_1_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_1_0_4.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      12 b65x_regCoeff_1_0_4_0 b65x_regIdentity_1_0_4_0
      b65x_regCoeff_positive_1_0_4_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      12 b65x_regCoeff_1_0_4_1 b65x_regIdentity_1_0_4_1
      b65x_regCoeff_positive_1_0_4_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      12 b65x_regCoeff_1_0_4_2 b65x_regIdentity_1_0_4_2
      b65x_regCoeff_positive_1_0_4_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (7/8) (1) (by norm_num)
    12 b65x_regCoeff_1_0_4_3 b65x_regIdentity_1_0_4_3
    b65x_regCoeff_positive_1_0_4_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_1_0_4 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_1_0 4)).eval₂ (Rat.castHom ℝ) t =
      (1600 : ℝ) * b65x_regPoly_1_0_4.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_1_0, b65x_certP5_1_0, b65x_certP7_1_0,
    b65x_certN_1_0, b65x_certD_1_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_1_0_4,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_1_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_1_0 4)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_1_0_4]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_1_0_4 t ht)

def b65x_regPoly_1_0_5 : ℚ[X] :=
  C (4986930057764875649156627301229322760436266972204358998885079267994718982230449812734695594508196850493954713974098985793504321177604566851879911033880576000000000000000000000000) + X * (C (-62755476719218495445046589535939523546975136944016333006967447034942964128328842955799878738069711672864452661363947269228088718867846492511767650095040000000000000000000000000000) + X * (C (362358916625575949415585794373491923049163503758233764248454581541635752312419874267088759309846919573696825316495984043760185734138811933248661977796256112436800000000000000000000) + X * (C (-1269468700632137118054512258094302872871010366279627806833785279617071615136882831970723808482683406806488091875805806288005755823161793127895404253374042848000000000000000000000000) + X * (C (3005251215994649597708086681576626284961781612512388757042257269333781073880417826655660224981280709585459527578157247884070041153825589692193944006290139935896831480000000000000000) + X * (C (-5064556622867559878727759984769284816819878346627239051115434657664278314242451982576815795728489826451804397036393691427883871104847127043870719388693359479227000000000000000000000) + X * (C (6229968552710623059421560187469793515883206941006012582194965292346288957657379465833252027667695900994390511845267809841847366303403732537637724886233213429875698794915000000000000) + X * (C (-5636199487245648547573317220600004433219111331446010222633959908952258285717829293197560436389034157201520877225548525887988459997462140872757638000363023054507957790000000000000000) + X * (C (3721826558679564837013096972369759574144850660551198731498253123829339535255087519478979647485067214583413339602367784790236694026670255399330363292803417001877275197600286825000000) + X * (C (-1749438808036698426684759129424312540463235917788428943950372194894007849144683861992503972507421916156349470371782331620764823375148774366883220037768316154403707371685000000000000) + X * (C (555614496554842244688126542786982625157372762584895403062017477003408865659077212099487343034230934808521269434630418998470733380147571704341512249967053132558567642408421366620000) + X * (C (-107049828985919264507569719732502277541762483684353922972769690069376401215442223427056140138086279012133745919104219955171703623223834761215477534491792780560197507224378200000000) + X * (C (9462253864161167650720604287747222772685333963198764489866973886196020460038024604931334319348052817841991930614897925395768714461826251072348402882214559221488113525009700165009) + X * (0)))))))))))))

def b65x_regCoeff_1_0_5_0 : Fin 13 → ℚ :=
  ![(4986930057764875649156627301229322760436266972204358998885079267994718982230449812734695594508196850493954713974098985793504321177604566851879911033880576000000000000000000000000), (28465422333569260067356232846782111351747635194444141483137227698465145722600976274916407765063506369495230237007214194908007494697331555966675107359046912000000000000000000000000), (74571991013174055250477608026840903442721242912956303450207918380874088199506019950362766005619307825270727813912819092556843677483448686721517547162462044109200000000000000000000), (118562706914686751857827247704056058268194931535140756830025939399862091450595109188517787709168109188328640693557461294198255747659031855474699462659011645092000000000000000000000), (127417274084328345086956191337736618923817459357383093795546539382149319220199627153847345144895284879071640778586464667517311456435641295386963794485301926907551967500000000000000), (97511506534104769565431060188269996525253918635938335842729009073360493629012936995609179066446783866396666777879811427514104184290756730153779489104709233326571990000000000000000), (54491142815031814581753012172040554916773691645426170638698296174887426415337947119018116864199840266943268514720213280910653922223034894964991393305874684512356633670546875000000), (22403911612385974255689242619019035100871098044295339597869631278993364342163067481335633446698981405435056188306390186437609723184750956757412061794136678352094771788906250000000), (26905174360795955123396015658993509151145041224832273151290932355823631099137167668715676263920463921341902260164696394191330276081797513505268013287194453200357540507816981640625/4), (1438130310890423366908513690360330253000035198691738060344525031794790171902145985361133208642938034830954366056771308474772831928289901202885354188593203206363285069369716015625), (6651401484041257140156067078912930003191853369649838690805407829748023427568133482587961565491706642064518800616083979732514727677921996827379346571911194351125871697040786456875/32), (291748547176887776850856901371657906506458417013967384787127846403892309207032188556096283630332521030447111224994787744792073521861826967655314509643761386526342727175669269375/16), (3007502473916158009886580910661676643710066508764032078137804826529123276643466866663643814553991490963716367864274484550783473531436392377911017298956594748240331394527966645009/4096)]

theorem b65x_regIdentity_1_0_5_0 (x : ℝ) :
    (b65x_regPoly_1_0_5.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_1_0_5_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_5, b65x_regCoeff_1_0_5_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_5_0 : ∀ i, 0 < b65x_regCoeff_1_0_5_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_5_0]

def b65x_regCoeff_1_0_5_1 : Fin 13 → ℚ :=
  ![(3007502473916158009886580910661676643710066508764032078137804826529123276643466866663643814553991490963716367864274484550783473531436392377911017298956594748240331394527966645009/4096), (8395615245924604370524386508168983776977259889982376076864061268913001700541141732382632178644642072724832192378803945290358556383770605471259027073408623996477048011508866565081/2048), (86572066456565416488283272123062486302888015293508970077646111372981998436966237823781051059480129075744366680740913180461915653879259221815801829657176982012162533195389432967673/8192), (136247185529503200881932393705901961776989305915606255358827877320677064574379217813023496425412926551595100419919534467947327697836622468407067043351488969747187442073393812638365/8192), (1166272743531510862438874097957517213527729435963533039564262563225595012230104231488445428925479477439743647032020001026608017947765947852051828112211586566535621637154859819235855/65536), (223434512310058412823183998368788604836202510347301075819762413786767704875564653607737078468302398877755326624499866023008384842043632797243576022301462859643533712263514450781513/16384), (502920578918781058413620694257716071796555758508853788242491148109386481346060874684527014903923587050768324584115079518510763223359425841478232995734897306684925001560836737230591/65536), (209368528718695206852049225883701431277824266321927479020839755548114859006105804710567068169437898096431751616589160808651355053481334754274919846140860246883250859552030199233617/65536), (1023890737850456785390604076294141822870434349927444545319289227470804569009626086415538170721542256410831392318184031746930578322255358105116717184441630774637848268608015624104255/1048576), (112030792389732055992325668620588506027769320920428223222756844276764984993877730935084511404398885052205300264038061935194713539517999141331757939833739175744830626746579546368085/524288), (66641412590841497804391645288975474737984882987087057671616532464701701898481299816131902438525311196205785466451286670526849738631683194429732282093908005342913992158670820102553/2097152), (6046676555472052579693548991840536294248382981116034692216301263688012653235238981698102936887992763128139688665633420028664783526202961472679116191886651420753623517897728467969/2097152), (2025149486737011217981224335940797882558786542119034395193544165480703914339468943312606767039521704152075703620528790408913653679509015811966588526111461782608114948383702627969/16777216)]

theorem b65x_regIdentity_1_0_5_1 (x : ℝ) :
    (b65x_regPoly_1_0_5.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_1_0_5_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_5, b65x_regCoeff_1_0_5_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_5_1 : ∀ i, 0 < b65x_regCoeff_1_0_5_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_5_1]

def b65x_regCoeff_1_0_5_2 : Fin 13 → ℚ :=
  ![(2025149486737011217981224335940797882558786542119034395193544165480703914339468943312606767039521704152075703620528790408913653679509015811966588526111461782608114948383702627969/16777216), (6132992269688995802443921039786108354532312916839240172309294961950309922584742526417255029579709811112401955253492273622893316063175219362341064351229853201965787499657866715783/8388608), (69873742601947382438441742007368079231112581450384866686396980199758199925695929844222231895624146185075186937238585989771002671882119559479362583301698183266787803942142803145097/33554432), (123375614219763025130398005323774360350837275603689406083212028355695020049080930425337196610904486523678853972280872678911916024886955157947932338272302755243157931178660054453155/33554432), (1200640208901775919788321949147915683187454161038402361380455647149492704660159233401536432727608343265244592886154570073429967585228463618077874794576185399726472060346493325916255/268435456), (264589229721700815424033935668435551429903998028751528233064954593753269567204898086612625586795895054077872617500715971494906620724372918946738099959958455552596397906600793000919/67108864), (692405491040443056761569740436987034219907165570003763535683788821582135698610760565229796012509866288731473904638452608325441755011576578615961334218249628195574639141093573520559/268435456), (338458637005771607035583112536162021465703703821676720995660809962727533835975199822854680282303918700246544876265896695865034538920273454862907869195296273664067193757106674800559/268435456), (1961742205099475896973769710396120804439033864208945466832593471269196454216509141326634302644773694807663924244429488024389416254657204335769836968400453186129527764468787611339855/4294967296), (256705826502930898227353896304065365286115916358493095787238894789190503407044660964628537888971581679624904796798657515785679632800714304341005893971445201080970541519945933932555/2147483648), (184249620209562469131563126013763858980693450854243681981244495653635820220249844839707991275030783521600185547066960584997627648854850352338612624874863085148339395029266602225577/8589934592), (20352845410244544600228680224374716264875852691664487361400194036332015781620080170768044287366905719951318272225054132594799682697977011482512231918914289087037063387139894101183/8589934592), (8375794166792459538742303279534648898745957025241603939452949607739258866858311470511945644525489937213992693879700208354930316377784897674233015652130419612553495886867516069809/68719476736)]

theorem b65x_regIdentity_1_0_5_2 (x : ℝ) :
    (b65x_regPoly_1_0_5.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_1_0_5_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_5, b65x_regCoeff_1_0_5_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_5_2 : ∀ i, 0 < b65x_regCoeff_1_0_5_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_5_2]

def b65x_regCoeff_1_0_5_3 : Fin 13 → ℚ :=
  ![(8375794166792459538742303279534648898745957025241603939452949607739258866858311470511945644525489937213992693879700208354930316377784897674233015652130419612553495886867516069809/68719476736), (1193634272533208503999557403557307607840504596015081114239663696721440204738713560191948161552391022922664952353511623117497816608844420385046703759369242437655856068365663527061/2147483648), (805514293020853294064260581385219675752579591912368127024222744357938476933272475606576451393751600670808903509117283976545941872891107685814564948690785777986835298676060143953/536870912), (90694627422137016386109403102347257503235566554167592373205311037296365348551323747281142654757310590986189524088743375150679122858924967135942745777459430689534704865723210465/33554432), (62259420529116477172742031136146220556474231176397219957343201317831541449213466289961006923933652493126463271953694253961538660573116641625119943309494223963486136218041163455/16777216), (1026784326099444424283234816210971206426995054669781717556074103045399914926754624668935551161007338273848842532189788385870573441486277404054723540126650136575496242630621813/262144), (218402687967332260746307011392542712412074314729455169417320353981490620311779850016912817423830492523941742456465821993685459968358410561795881750543584440472054010843097271/65536), (8950087799593785257706281148963505321607351402345522339706101784426756919743461843173021470048417996827361013375046944195967966530203632013333227769680406303895468550030037/4096), (4616995027503277091805755000433081863529773629221069803468637421195490752822041474575047034909057918890846786901556881495331091718834009093380177206448414667870065114171455/4096), (49876618560405501376426110988993523701046266450508480663273182760461750765287691906962425755892513259032742341907948562445138970499294392142671745358063124577035535494785/128), (3054464665737967252880724746106309892207314721465892730394326979131625336668508814348849485317322332646578410670179323548675558392392908719319926798338191953908354409553/32), (769535627946119946496588622927944419221878029565411848297456088353540903366054507840223857034495214242116788493145293746511050143093472635022654512778433286485795189/2), (553368508009284004267523498578456081021410618976709494621031336631674000408192631912656385331509720020531590991113875419542207862220600431167798559539339691785009)]

theorem b65x_regIdentity_1_0_5_3 (x : ℝ) :
    (b65x_regPoly_1_0_5.comp (C (7/8) + C ((1) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_1_0_5_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_1_0_5, b65x_regCoeff_1_0_5_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_1_0_5_3 : ∀ i, 0 < b65x_regCoeff_1_0_5_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_1_0_5_3]

theorem b65x_regPoly_positive_1_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_1_0_5.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      12 b65x_regCoeff_1_0_5_0 b65x_regIdentity_1_0_5_0
      b65x_regCoeff_positive_1_0_5_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      12 b65x_regCoeff_1_0_5_1 b65x_regIdentity_1_0_5_1
      b65x_regCoeff_positive_1_0_5_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      12 b65x_regCoeff_1_0_5_2 b65x_regIdentity_1_0_5_2
      b65x_regCoeff_positive_1_0_5_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (7/8) (1) (by norm_num)
    12 b65x_regCoeff_1_0_5_3 b65x_regIdentity_1_0_5_3
    b65x_regCoeff_positive_1_0_5_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_1_0_5 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_1_0 5)).eval₂ (Rat.castHom ℝ) t =
      (64 : ℝ) * b65x_regPoly_1_0_5.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_1_0, b65x_certP5_1_0, b65x_certP7_1_0,
    b65x_certN_1_0, b65x_certD_1_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_1_0_5,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_1_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_1_0 5)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_1_0_5]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_1_0_5 t ht)

theorem b65x_certFactors_ne_zero_1_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1))
    (j : Fin 6) : b65x_cpEval (b65x_certFactors_1_0 j) t ≠ 0 := by
  apply b65x_cpEval_ne_zero
  fin_cases j

  · exact b65x_certFactor_norm_positive_1_0_0 t ht

  · exact b65x_certFactor_norm_positive_1_0_1 t ht

  · exact b65x_certFactor_norm_positive_1_0_2 t ht

  · exact b65x_certFactor_norm_positive_1_0_3 t ht

  · exact b65x_certFactor_norm_positive_1_0_4 t ht

  · exact b65x_certFactor_norm_positive_1_0_5 t ht

theorem b65x_certND_ratio_1_0 (t : ℝ) :
    b65b_inverseNormalization (b65x_piece 1 0 t) =
      b65x_cpEval b65x_certN_1_0 t / b65x_cpEval b65x_certD_1_0 t := by
  have hQ : (1 + t ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hQc : (((1 + t ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ
  push_cast at hQc
  have hrel : b65x_cpEval b65x_certD_1_0 t =
      (5000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 6).1 : ℂ) - b65x_piece 1 0 t *
          (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ))) := by
    norm_num [b65x_cpEval, b65x_certD_1_0, Polynomial.eval₂_pow,
      b65x_piece, b65x_centre, b65x_radius, b65x_et, mr_centre, mr_basePoint,
      b65b_vertex0, b65b_track, b65b_radius, b65b_boxCentre]
    push_cast
    field_simp [hQc]
    <;> ring
  have hnrel : b65x_cpEval b65x_certN_1_0 t =
      (5000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 0).1 : ℂ) * ((b65b_boxCentre 6).1 : ℂ)) := by
    norm_num [b65x_cpEval, b65x_certN_1_0, Polynomial.eval₂_pow, b65b_boxCentre]
    all_goals push_cast
    all_goals ring
  unfold b65b_inverseNormalization
  rw [hnrel, hrel]
  have hLQ : (5000000000000 : ℂ) * (1) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    norm_num
  exact (mul_div_mul_left _ _ hLQ).symm

theorem b65x_piece_regular_1_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    ((b65b_boxCentre 6).1 : ℂ) - b65x_piece 1 0 t *
        (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
      b65b_inverseNormalization (b65x_piece 1 0 t) ∈ b65s_regular := by

  have h0 := b65x_certFactors_ne_zero_1_0 t ht 0

  have h1 := b65x_certFactors_ne_zero_1_0 t ht 1

  have h2 := b65x_certFactors_ne_zero_1_0 t ht 2

  have h3 := b65x_certFactors_ne_zero_1_0 t ht 3

  have h4 := b65x_certFactors_ne_zero_1_0 t ht 4

  have h5 := b65x_certFactors_ne_zero_1_0 t ht 5

  change b65x_cpEval b65x_certD_1_0 t ≠ 0 at h0
  change b65x_cpEval (b65x_cpSub b65x_certN_1_0 (b65x_cpScale 3 b65x_certD_1_0)) t ≠ 0 at h1
  change b65x_cpEval (b65x_cpSub b65x_certN_1_0 b65x_certD_1_0) t ≠ 0 at h2
  change b65x_cpEval (b65x_cpAdd b65x_certN_1_0 (b65x_cpScale 2 b65x_certD_1_0)) t ≠ 0 at h3
  change b65x_cpEval b65x_certP5_1_0 t ≠ 0 at h4
  change b65x_cpEval b65x_certP7_1_0 t ≠ 0 at h5
  norm_num only [b65x_certFactors_1_0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, b65x_certP5_1_0, b65x_certP7_1_0,
    b65x_cpEval_sub, b65x_cpEval_add, b65x_cpEval_mul, b65x_cpEval_pow,
    b65x_cpEval_scale] at h0 h1 h2 h3 h4 h5
  have hN : b65x_cpEval b65x_certN_1_0 t ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [b65x_cpEval, b65x_certN_1_0, Polynomial.eval₂_pow,
      pow_two, Complex.mul_re] at hr
    skip
  have hreg : b65b_inverseNormalization (b65x_piece 1 0 t) ∈ b65s_regular := by
    rw [b65x_certND_ratio_1_0]
    exact b65x_regular_of_homogeneous _ _ h0 hN h1 h2 h3
      (by simpa only [mul_assoc] using h4) (by simpa only [mul_assoc] using h5)
  refine ⟨?_, hreg⟩
  intro h
  apply hreg.1
  simp [b65b_inverseNormalization, h]

end HodgeLean.Foundations.Program

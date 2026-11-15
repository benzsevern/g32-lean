import HodgeLean.Foundations.Program.BraidBridgesInterval
import HodgeLean.Foundations.Program.BraidBridgesRegular10Piece2

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

def b65x_certN_11_0 : b65x_CPoly := (C (291668908382000) + X * (0), C (0) + X * (0))
def b65x_certD_11_0 : b65x_CPoly := (C (2228834950000000) + X * (C (-1977615245997117) + X * (0)), C (-4112139000000000) + X * (C (4298820229129983) + X * (0)))

def b65x_certP5_11_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_11_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_11_0 (b65x_cpScale 3 b65x_certD_11_0)) 4))
    (b65x_cpScale (5) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_11_0 b65x_certD_11_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_11_0 (b65x_cpScale 2 b65x_certD_11_0)) 3)))

def b65x_certP7_11_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_11_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_11_0 (b65x_cpScale 3 b65x_certD_11_0)) 4))
    (b65x_cpScale (-7) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_11_0 b65x_certD_11_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_11_0 (b65x_cpScale 2 b65x_certD_11_0)) 3)))

def b65x_certFactors_11_0 : Fin 6 → b65x_CPoly :=
  ![b65x_certD_11_0,
    b65x_cpSub b65x_certN_11_0 (b65x_cpScale 3 b65x_certD_11_0),
    b65x_cpSub b65x_certN_11_0 b65x_certD_11_0,
    b65x_cpAdd b65x_certN_11_0 (b65x_cpScale 2 b65x_certD_11_0),
    b65x_certP5_11_0, b65x_certP7_11_0]

def b65x_regPoly_11_0_0 : ℚ[X] :=
  C (10938696194831251250000000000000) + X * (C (-22085124296125561132476150000000) + X * (C (11195408711788698563580340945989) + X * (0)))

def b65x_regCoeff_11_0_0_0 : Fin 3 → ℚ :=
  ![(10938696194831251250000000000000), (10834830241599721933761925000000), (10779944898862581298628040945989/4)]

theorem b65x_regIdentity_11_0_0_0 (x : ℝ) :
    (b65x_regPoly_11_0_0.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_0_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_0, b65x_regCoeff_11_0_0_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_0_0 : ∀ i, 0 < b65x_regCoeff_11_0_0_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_0_0]

def b65x_regCoeff_11_0_0_1 : Fin 3 → ℚ :=
  ![(10779944898862581298628040945989/4), (10670174213388300028360272837967/4), (10756325969891573482509268513901/16)]

theorem b65x_regIdentity_11_0_0_1 (x : ℝ) :
    (b65x_regPoly_11_0_0.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_0_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_0, b65x_regCoeff_11_0_0_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_0_1 : ∀ i, 0 < b65x_regCoeff_11_0_0_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_0_1]

def b65x_regCoeff_11_0_0_2 : Fin 3 → ℚ :=
  ![(10756325969891573482509268513901/16), (43075878251636727074497837967/2), (48980610494388681104190945989)]

theorem b65x_regIdentity_11_0_0_2 (x : ℝ) :
    (b65x_regPoly_11_0_0.comp (C (3/4) + C ((1) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_0_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_0, b65x_regCoeff_11_0_0_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_0_2 : ∀ i, 0 < b65x_regCoeff_11_0_0_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_0_2]

theorem b65x_regPoly_positive_11_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_11_0_0.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_11_0_0_0 b65x_regIdentity_11_0_0_0
      b65x_regCoeff_positive_11_0_0_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_11_0_0_1 b65x_regIdentity_11_0_0_1
      b65x_regCoeff_positive_11_0_0_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (3/4) (1) (by norm_num)
    2 b65x_regCoeff_11_0_0_2 b65x_regIdentity_11_0_0_2
    b65x_regCoeff_positive_11_0_0_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_11_0_0 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_11_0 0)).eval₂ (Rat.castHom ℝ) t =
      (2 : ℝ) * b65x_regPoly_11_0_0.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_11_0, b65x_certP5_11_0, b65x_certP7_11_0,
    b65x_certN_11_0, b65x_certD_11_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_11_0_0,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_11_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_11_0 0)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_11_0_0]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_11_0_0 t ht)

def b65x_regPoly_11_0_1 : ℚ[X] :=
  C (96540555559049186352228962000000) + X * (C (-197035692025131311660757945918000) + X * (C (100758678406098287072223068513901) + X * (0)))

def b65x_regCoeff_11_0_1_0 : Fin 3 → ℚ :=
  ![(96540555559049186352228962000000), (94563265105532716874078951041000), (92849516592032409159623024677901/4)]

theorem b65x_regIdentity_11_0_1_0 (x : ℝ) :
    (b65x_regPoly_11_0_1.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_1_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_1, b65x_regCoeff_11_0_1_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_1_0 : ∀ i, 0 < b65x_regCoeff_11_0_1_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_1_0]

def b65x_regCoeff_11_0_1_1 : Fin 3 → ℚ :=
  ![(92849516592032409159623024677901/4), (89422019565031793730711171951703/4), (87048690298095825356575657609109/16)]

theorem b65x_regIdentity_11_0_1_1 (x : ℝ) :
    (b65x_regPoly_11_0_1.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_1_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_1, b65x_regCoeff_11_0_1_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_1_1 : ∀ i, 0 < b65x_regCoeff_11_0_1_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_1_1]

def b65x_regCoeff_11_0_1_2 : Fin 3 → ℚ :=
  ![(87048690298095825356575657609109/16), (82302031764223888608304628923921/16), (81772044270610540079138953773149/64)]

theorem b65x_regIdentity_11_0_1_2 (x : ℝ) :
    (b65x_regPoly_11_0_1.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_1_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_1, b65x_regCoeff_11_0_1_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_1_2 : ∀ i, 0 < b65x_regCoeff_11_0_1_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_1_2]

def b65x_regCoeff_11_0_1_3 : Fin 3 → ℚ :=
  ![(81772044270610540079138953773149/64), (80712069283383843020807603471605/64), (96518778457191498838897667307725/256)]

theorem b65x_regIdentity_11_0_1_3 (x : ℝ) :
    (b65x_regPoly_11_0_1.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_1_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_1, b65x_regCoeff_11_0_1_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_1_3 : ∀ i, 0 < b65x_regCoeff_11_0_1_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_1_3]

def b65x_regCoeff_11_0_1_4 : Fin 3 → ℚ :=
  ![(96518778457191498838897667307725/256), (1975838646725956977261257979515/8), (263541940016161763694084595901)]

theorem b65x_regIdentity_11_0_1_4 (x : ℝ) :
    (b65x_regPoly_11_0_1.comp (C (15/16) + C ((1) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_1_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_1, b65x_regCoeff_11_0_1_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_1_4 : ∀ i, 0 < b65x_regCoeff_11_0_1_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_1_4]

theorem b65x_regPoly_positive_11_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_11_0_1.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_11_0_1_0 b65x_regIdentity_11_0_1_0
      b65x_regCoeff_positive_11_0_1_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_11_0_1_1 b65x_regIdentity_11_0_1_1
      b65x_regCoeff_positive_11_0_1_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_11_0_1_2 b65x_regIdentity_11_0_1_2
      b65x_regCoeff_positive_11_0_1_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      2 b65x_regCoeff_11_0_1_3 b65x_regIdentity_11_0_1_3
      b65x_regCoeff_positive_11_0_1_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (15/16) (1) (by norm_num)
    2 b65x_regCoeff_11_0_1_4 b65x_regIdentity_11_0_1_4
    b65x_regCoeff_positive_11_0_1_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_11_0_1 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_11_0 1)).eval₂ (Rat.castHom ℝ) t =
      (2 : ℝ) * b65x_regPoly_11_0_1.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_11_0, b65x_certP5_11_0, b65x_certP7_11_0,
    b65x_certN_11_0, b65x_certD_11_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_11_0_1,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_11_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_11_0 1)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_11_0_1]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_11_0_1 t ht)

def b65x_regPoly_11_0_2 : ℚ[X] :=
  C (10331149714059475454028962000000) + X * (C (-21508315416125981621967015306000) + X * (C (11195408711788698563580340945989) + X * (0)))

def b65x_regCoeff_11_0_2_0 : Fin 3 → ℚ :=
  ![(10331149714059475454028962000000), (9908141720055960097074416347000), (9503376735774637135762158333989/4)]

theorem b65x_regIdentity_11_0_2_0 (x : ℝ) :
    (b65x_regPoly_11_0_2.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_2_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_2, b65x_regCoeff_11_0_2_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_2_0 : ∀ i, 0 < b65x_regCoeff_11_0_2_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_2_0]

def b65x_regCoeff_11_0_2_1 : Fin 3 → ℚ :=
  ![(9503376735774637135762158333989/4), (8693846767211991213137642307967/4), (7957288837538114873082276841901/16)]

theorem b65x_regIdentity_11_0_2_1 (x : ℝ) :
    (b65x_regPoly_11_0_2.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_2_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_2, b65x_regCoeff_11_0_2_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_2_1 : ∀ i, 0 < b65x_regCoeff_11_0_2_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_2_1]

def b65x_regCoeff_11_0_2_2 : Fin 3 → ℚ :=
  ![(7957288837538114873082276841901/16), (6484172978190362192971545909769/16), (5302945274397687843137417217461/64)]

theorem b65x_regIdentity_11_0_2_2 (x : ℝ) :
    (b65x_regPoly_11_0_2.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_2_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_2, b65x_regCoeff_11_0_2_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_2_2 : ∀ i, 0 < b65x_regCoeff_11_0_2_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_2_2]

def b65x_regCoeff_11_0_2_3 : Fin 3 → ℚ :=
  ![(5302945274397687843137417217461/64), (2940489866812339143469159832845/64), (1745587081447303764907311407525/256)]

theorem b65x_regIdentity_11_0_2_3 (x : ℝ) :
    (b65x_regPoly_11_0_2.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_2_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_2, b65x_regCoeff_11_0_2_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_2_3 : ∀ i, 0 < b65x_regCoeff_11_0_2_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_2_3]

def b65x_regCoeff_11_0_2_4 : Fin 3 → ℚ :=
  ![(1745587081447303764907311407525/256), (2846955673611840537598237371935/512), (6041660797526562625849257401069/4096)]

theorem b65x_regIdentity_11_0_2_4 (x : ℝ) :
    (b65x_regPoly_11_0_2.comp (C (15/16) + C ((61/64) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_2_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_2, b65x_regCoeff_11_0_2_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_2_4 : ∀ i, 0 < b65x_regCoeff_11_0_2_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_2_4]

def b65x_regCoeff_11_0_2_5 : Fin 3 → ℚ :=
  ![(6041660797526562625849257401069/4096), (347749450302881550652782657199/1024), (1636186428868415535085553543429/1024)]

theorem b65x_regIdentity_11_0_2_5 (x : ℝ) :
    (b65x_regPoly_11_0_2.comp (C (61/64) + C ((31/32) - (61/64)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_2_5).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_2, b65x_regCoeff_11_0_2_5, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_2_5 : ∀ i, 0 < b65x_regCoeff_11_0_2_5 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_2_5]

def b65x_regCoeff_11_0_2_6 : Fin 3 → ℚ :=
  ![(1636186428868415535085553543429/1024), (142525307384448907956371186659/16), (18243009722192395642287639989)]

theorem b65x_regIdentity_11_0_2_6 (x : ℝ) :
    (b65x_regPoly_11_0_2.comp (C (31/32) + C ((1) - (31/32)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_2_6).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_2, b65x_regCoeff_11_0_2_6, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_2_6 : ∀ i, 0 < b65x_regCoeff_11_0_2_6 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_2_6]

theorem b65x_regPoly_positive_11_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_11_0_2.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_11_0_2_0 b65x_regIdentity_11_0_2_0
      b65x_regCoeff_positive_11_0_2_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_11_0_2_1 b65x_regIdentity_11_0_2_1
      b65x_regCoeff_positive_11_0_2_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      2 b65x_regCoeff_11_0_2_2 b65x_regIdentity_11_0_2_2
      b65x_regCoeff_positive_11_0_2_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      2 b65x_regCoeff_11_0_2_3 b65x_regIdentity_11_0_2_3
      b65x_regCoeff_positive_11_0_2_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h4 : t ≤ (61/64 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (15/16) (61/64) (by norm_num)
      2 b65x_regCoeff_11_0_2_4 b65x_regIdentity_11_0_2_4
      b65x_regCoeff_positive_11_0_2_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h5 : t ≤ (31/32 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (61/64) (31/32) (by norm_num)
      2 b65x_regCoeff_11_0_2_5 b65x_regIdentity_11_0_2_5
      b65x_regCoeff_positive_11_0_2_5 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (31/32) (1) (by norm_num)
    2 b65x_regCoeff_11_0_2_6 b65x_regIdentity_11_0_2_6
    b65x_regCoeff_positive_11_0_2_6 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_11_0_2 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_11_0 2)).eval₂ (Rat.castHom ℝ) t =
      (2 : ℝ) * b65x_regPoly_11_0_2.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_11_0, b65x_certP5_11_0, b65x_certP7_11_0,
    b65x_certN_11_0, b65x_certD_11_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_11_0_2,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_11_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_11_0 2)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_11_0_2]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_11_0_2 t ht)

def b65x_regPoly_11_0_3 : ℚ[X] :=
  C (11274370967260919464182240500000) + X * (C (-22373528736125350887730717347000) + X * (C (11195408711788698563580340945989) + X * (0)))

def b65x_regCoeff_11_0_3_0 : Fin 3 → ℚ :=
  ![(11274370967260919464182240500000), (175213198396488040633763653000), (96250942924267140031864098989)]

theorem b65x_regIdentity_11_0_3_0 (x : ℝ) :
    (b65x_regPoly_11_0_3.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_11_0_3_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_3, b65x_regCoeff_11_0_3_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_3_0 : ∀ i, 0 < b65x_regCoeff_11_0_3_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_3_0]

theorem b65x_regPoly_positive_11_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_11_0_3.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_11_0_3_0 b65x_regIdentity_11_0_3_0
    b65x_regCoeff_positive_11_0_3_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_11_0_3 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_11_0 3)).eval₂ (Rat.castHom ℝ) t =
      (8 : ℝ) * b65x_regPoly_11_0_3.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_11_0, b65x_certP5_11_0, b65x_certP7_11_0,
    b65x_certN_11_0, b65x_certD_11_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_11_0_3,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_11_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_11_0 3)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_11_0_3]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_11_0_3 t ht)

def b65x_regPoly_11_0_4 : ℚ[X] :=
  C (1566435244871510025358757415984027705699661982568758649036122197769528759248027822351083815038595424739330580000679548805944295332296695120798464469043840000000000000000000000000000000000) + X * (C (-19134348284733911925774349737575485600776819928209649260798755881974700664863452260256816771508790944123756023843560284976690155320023734801283749801953395040000000000000000000000000000000) + X * (C (107152239441999655772487290571440985725470685888048915683730269138440274343523506632387035336675935011200273843308809981752624072423421382365399779569712350359620000000000000000000000000000) + X * (C (-363754791049981209720933557509668945897461275434518768976436839080965834620213049481355442759411622651991557505304000805170235161006754781976490117406217222318297500000000000000000000000000) + X * (C (833724807423619311366577322405920920561739603075957492219259369049889031712270288106629968585053862848142924932004369626317635176063716942783445338726947451926882977290000000000000000000000) + X * (C (-1359176528813852834103689637460093781665680666660260166893599453125599904253548378243285238773206035615013377796634606881310561758851804858625542614296898128281609604727600000000000000000000) + X * (C (1616056003323690065054002084836198135219589023985364646717535746349020969985972013268533907188178875711569785019483438865572749074181150503180973981272303011266679179265496505000000000000000) + X * (C (-1412026604237454730591766425867620868228008589754801129112655068573327921720915351353925771422885547444981120492833256517729522879596758940054780720753730269255695472836940475455000000000000) + X * (C (899817837404783498357900229658035455326846334644305114878404837693852050008735964568408022649852393670404231721213895885843455420741789600997957910561663147576529902952818663493702500000000) + X * (C (-407850652688905748778260884366562558822827296834887959386542777874583985697652791844969404432586924366372720793824179269069192048898209379790710789580637222591524377882404909786030550000000) + X * (C (124809555794976529750676092328428950037867528966054783488613807202899641033751902402154110354395565726103055144261309796026046357891598336906575113041835229027283927383788972412729580500000) + X * (C (-23152926365771952704785581757351169296097672342637409994850280221975166009925011012232058520818574683137246848970191558971860287647316895153215164008660140722133017107029015136846375091000) + X * (C (1968972806759817498434940242737489199777779838744418097821224050315954648494325267516458918641421653868979980359207844385685167565975165815132632034507772396695440841151193980919176295561) + X * (0)))))))))))))

def b65x_regCoeff_11_0_4_0 : Fin 13 → ℚ :=
  ![(1566435244871510025358757415984027705699661982568758649036122197769528759248027822351083815038595424739330580000679548805944295332296695120798464469043840000000000000000000000000000000000), (9230048796091164341417914123020589668007533826720279158034088432246994778544607738084597394708749624810088948086374443182986466327548474048939698727549382480000000000000000000000000000000), (24933870455983060025040888541140904203272852716397228822923474986538113039501725501855798383417931592915228609732471149258683655777306682156987975938577854869905000000000000000000000000000), (40832425765301115836233545473054087309057143430168991203252164715972015282103319155974136088762627175751176864560617754184046487737329327706797247884430159509262812500000000000000000000000), (45148066976093202141043916942819735069255043863203496864160922039988517875455622547092752264461542176280276485250037638910846832719779694500492025263249491383070498580625000000000000000000), (35508007678591456379334235141446663615319119930843348016961060011272660984926645898407502475407061826278576361604404810584532756615050815088027463590499768210902438497262500000000000000000), (20368399533156979261194452729963937057392623587990034088807132923646138581507423532368618420816749235116057509709248177846147997422113729610471774141982775159411221399360882890625000000000), (8586407388044041710795683391748436846115836792662987540282421151764577488901061904290170854310252592405859697292938497030919091256804611189389100250810421539849544587114199879257812500000), (2640044964589538802313093384562595430430933997472573000883140181781029824382249312440988400823252502005263718624580519275217124105014029909125573703915461432015043639004703941186337890625), (2309552779624851650491114783968878869820386434248564082024618382580621451669888768968766058922736549169898416015065575302498679022310754687741662767995831693205634929421610780965542578125/4), (2728338784189951360917341800361334148665798485898473668039583965447143935448768020558893766511827533967644798784792781393333733767761095448938629792347318134449420451679081285793946265625/32), (1953914554191642719932542446240015392659282355757107054574595543889651196049178179211263963657220776707846014860839121960983828710784475423154657694120560223557183918094514060023168363625/256), (1283056487327317475619701935434302298308843005738483631943585296714497700685145658164729831545956507688149832202763634774852216102256383066371868134896905037633663664989496409140348113561/4096)]

theorem b65x_regIdentity_11_0_4_0 (x : ℝ) :
    (b65x_regPoly_11_0_4.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_11_0_4_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_4, b65x_regCoeff_11_0_4_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_4_0 : ∀ i, 0 < b65x_regCoeff_11_0_4_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_4_0]

def b65x_regCoeff_11_0_4_1 : Fin 13 → ℚ :=
  ![(1283056487327317475619701935434302298308843005738483631943585296714497700685145658164729831545956507688149832202763634774852216102256383066371868134896905037633663664989496409140348113561/4096), (3731850169179286400847147633948659114142457628617924469193885494871874521969598206637512629284725462361964430381516225129734630077169545904728182437589904444474237312527411442170459567549/2048), (39848016617776499295570144239749104450286933881955691034084983325955113215226374478920274620399759906438419363186009339604736363859754367731687511526781257762864463032389923959379502730617/8192), (64547787620005149783746074215556227568400418417478541698223289608138803743394282416855056571582152056812403730186819018068282651836565946635220878009687233853567476362250003162553103660585/8192), (565311932906432159631411419978443619025469025238144595673608015079465933150237235018844614997790709668018737394601891336998915361277179857791478548751822210407855397735042652552909864038295/65536), (110159486550991051072838507655978260418537281195710351783439837138157822295726653213418912624739593689932228313144460603657268279835759563184191859789789296417748356877456704323686458544477/16384), (250750455620529553079127067886692636592134890191703803936238553481656435698161481216835442914421122594146147499221622842161069930648287690932579541857062994689808551233909612792610037661839/65536), (104965308055296181080127829207952834158063345446731815977792649802294201147627803441126704835436042695036750518285342353598672970902503538023403395493508977454023764453387068230003696087293/65536), (513253161150314473293209634612456605773016678822642612133840985645736471466719002731504709739872232192003846147732893598774284802075405213648877023217267741301069699121478665355917462711895/1048576), (55838780398340223339371961962601630851640727601356045706954500053168534006711152133558755327521208450054604494781692335543504208182550773254952143753858715732554606083185647807531306371465/524288), (32844277502053761062346051503643254041873083013794943500805918431467005751816261884040864454343198667031503650337541008868916506579808488702453444804481719380050942284239096327346306310137/2097152), (2930616836400073264574685529650697158780926116905066890020244165962499756650620767866200013075363570577881069428645003191895577183354848800255948844462852091897894531347037727803571495901/2097152), (959935680144105872154745159027699037475246358298345479849953069500254517628585865435603219735761662196081925050857475654070144809381939729284573399690340463770466048291025734758219725401/16777216)]

theorem b65x_regIdentity_11_0_4_1 (x : ℝ) :
    (b65x_regPoly_11_0_4.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_11_0_4_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_4, b65x_regCoeff_11_0_4_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_4_1 : ∀ i, 0 < b65x_regCoeff_11_0_4_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_4_1]

def b65x_regCoeff_11_0_4_2 : Fin 13 → ℚ :=
  ![(959935680144105872154745159027699037475246358298345479849953069500254517628585865435603219735761662196081925050857475654070144809381939729284573399690340463770466048291025734758219725401/16777216), (2778187448496806320243335371947897019715364990874975538609089293577291145356031253188028951471127818608975186600427274502840148917727759963049262908287359990138405371925156157216834536807/8388608), (29636584606204817355485028331907605338558253038319552035987505460393646865073108212199212352946017024082045176873693883404282846502830012773546831456861519129510107341582048462505046225713/33554432), (48140223914428565246645281319725079156883146353875060849857689367675272649621945958314593003418385910532783028163720034104500359738983321841791680759965454662846184067466462770948438914995/33554432), (424240466972578244077900764380385900837263107761853300206309689056482354843783212490854214231001485763178552443199560996874487599464180926595494978591276598890863640026183256801194919329895/268435456), (83446208103669922030476178182076586317026059240468216042340603158619192185254799917205748063141374790694885483404895787512858512959253932485840984014923626392249513279549932654405171340951/67108864), (192279735302786699879074574690646341408340085539721910339339572143988593604455613096601804143927971222055707140388057832430863363496025846637632506557942111745005458309521041198123569785511/268435456), (81695142109586245223922458257802851670956543052608826393707467813612145940086755697601857723307283837300405833061642079907114682985851199510251330319991928655074682393633063983084932492511/268435456), (406473955930833034914446223683117943927229906935015908850714563766306035390368030301626430901787584569756396387861831223538217831260010381641822543452354615750098114259956777108652703994295/4294967296), (45109578539236008228353617204563238267066732485291951042880399951845121781280612624640991587964938447434913348059288886250145575611421298712992853784935959035738092660285148521219960087595/2147483648), (27136733896658792258785169827668065503524919683342326755837705625641663553095369288132731760146998554705084279501567036998074659331345346325536460124035227675264203714919184717136738943633/8589934592), (2483618335521844533459649168575759478647640952711881087698359633875923219979077262128238244261583581383224005095250254545256154876150742060516424024712931440220915064743289457076675283407/8589934592), (837297856356628101841231515739472175401108982306206599513124129432883658580356974392191600537040010289440653541426017615593750610095234601855436435221950120802393320573814838847841510761/68719476736)]

theorem b65x_regIdentity_11_0_4_2 (x : ℝ) :
    (b65x_regPoly_11_0_4.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_11_0_4_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_4, b65x_regCoeff_11_0_4_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_4_2 : ∀ i, 0 < b65x_regCoeff_11_0_4_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_4_2]

def b65x_regCoeff_11_0_4_3 : Fin 13 → ℚ :=
  ![(837297856356628101841231515739472175401108982306206599513124129432883658580356974392191600537040010289440653541426017615593750610095234601855436435221950120802393320573814838847841510761/68719476736), (7068808387009943016011344660664261888921498551684677710253188605681938940498415262084139337384112371274488882256949575381274238533740436262471320238229730546566224244538764866712312219/2147483648), (7997485934183742714595508650246172594588446236610038150430621978532090419215604765863325257155006489106108392070001144814563886823235178462783371417193123555190741843919146464290785237/536870912), (413509218297645727488453559082618312478243111056029470627741124937814176040906102189090748752467436444120531065832306387429475191445667005236397081815730821316093515463610341841830235/33554432), (427799491177969970400147812518486508500884441585266447237334057810378335683285414039817193239499085556176378942091282068518682842094395507665615164691955033929155413614681430142603695/16777216), (3788508754143950345271305103710881512501658472500236192397278378666877928631072398765185084995517776115756508675825241443674847160137365499894271398075227197098127862783091792525427/262144), (496324474590869870428671602559161258526390277047488850582740054892364499103077881968904229427716176081278639148483295460531517678310143266161731570293029462502041520752762893504059/65536), (8838537949284411026954995091674956461454349799479529523095052070411833773470918532310053320969092354514340789980322692252319936700341746695547308004205043694239835716055891862223/4096), (4185433774791877691932087893365209705876550363937717664818934142653837884245233314204529893585722597994528315770034696270286633877424479489606305075153987292527777159015584580695/4096), (59674543765475198485477257129550976027931418239205222146165543532260054159811525630123032902453929726820471451343268386904155328429470379501313313051036130046933498491571482015/128), (5414589930667245693103630188623324121352978887503940166425231104748318864900179036623884333287681761922373685832394614314504150140616511700607259357773048627644721169564021637/32), (710405519743242133005801868774407203436433359001484278993672680440942210665346421106514802458246145170328715535135515756753807863893849390213285086879821001456543749773031/2), (226280759873154266138297425729046109518200923759937524877993871955854167419154340408801759221916231476077272879080036768260063827916424344431455179280934509474331704561)]

theorem b65x_regIdentity_11_0_4_3 (x : ℝ) :
    (b65x_regPoly_11_0_4.comp (C (7/8) + C ((1) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_11_0_4_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_4, b65x_regCoeff_11_0_4_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_4_3 : ∀ i, 0 < b65x_regCoeff_11_0_4_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_4_3]

theorem b65x_regPoly_positive_11_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_11_0_4.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      12 b65x_regCoeff_11_0_4_0 b65x_regIdentity_11_0_4_0
      b65x_regCoeff_positive_11_0_4_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      12 b65x_regCoeff_11_0_4_1 b65x_regIdentity_11_0_4_1
      b65x_regCoeff_positive_11_0_4_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      12 b65x_regCoeff_11_0_4_2 b65x_regIdentity_11_0_4_2
      b65x_regCoeff_positive_11_0_4_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (7/8) (1) (by norm_num)
    12 b65x_regCoeff_11_0_4_3 b65x_regIdentity_11_0_4_3
    b65x_regCoeff_positive_11_0_4_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_11_0_4 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_11_0 4)).eval₂ (Rat.castHom ℝ) t =
      (102400 : ℝ) * b65x_regPoly_11_0_4.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_11_0, b65x_certP5_11_0, b65x_certP7_11_0,
    b65x_certN_11_0, b65x_certD_11_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_11_0_4,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_11_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_11_0 4)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_11_0_4]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_11_0_4 t ht)

def b65x_regPoly_11_0_5 : ℚ[X] :=
  C (77920782152576182018072301581708168131816671440693109357579363562417484097350778323979618664190575788968042405845296653023505018400071357060623609904384000000000000000000000000000000000000) + X * (C (-949648905435343346239922235669126352174095237772989947114539076598097264957133062115935450124854318729054939426692733810962184621217378251293568855630381584000000000000000000000000000000000) + X * (C (5306677356723214447125743362692254335430410599804160435798031178623477209920179091154914709054087064351398330068574816530715163945631160478418148583588480706154500000000000000000000000000000) + X * (C (-17979218062915189245426062073488688696902753792586665631661897289999599986818672353844061316550910203706449119121338500357913790190915884298308189141972473667103655500000000000000000000000000) + X * (C (41133840807282859333277554316871922202819147602745133612425520210652266318554959405429420839006597688003865348844379462701437250037698851479340519082124809288046236440250000000000000000000000) + X * (C (-66949287959022287993661978838367370502643824038717557589657616892348723719299138653840759742657144666679474524951326730535765051946346293159391026757243873643647185420343000000000000000000000) + X * (C (79488537807406145702999427502192456539857465005205580809908777401661154496509146850572379986870081844041293622587975632756312194288913278613760580097654127073927767985188659625000000000000000) + X * (C (-69367948083197297122869909917323588680833721962263097453738303514907094422807827069147311284620839576873599444778045020943379077827788744045249242021006701221757301100649661308875000000000000) + X * (C (44160478007243701495067836275494761750407929254914601693393489398057903173749848775458998248000297003438406473470698140186500830427526738738045181705747500229950025666489637560301562500000000) + X * (C (-20000662185953317378773327993727055765929052234710276169376391033438864920459899689724241601948799408523782695945266249319634700912859719670598766864000245781950725483117290929652822750000000) + X * (C (6117324160106533333635896348380260965363291615491052496596443943907363065665879509451901759539104814912526980289421521227924923198014987455678265644557049473389943449669010436155637564500000) + X * (C (-1134493391922825682534493506110207295508785944789233089747663730876783134486325539599370867520110159473725095599539386389621154094718527862507543036424346895384517838244421741705472379459000) + X * (C (96479667531231057423312071894136970789111212098476486793239978465481777776221938108306487013429661039580019037601184374898573210732783124941498969690880847438076601216408505065039638482489) + X * (0)))))))))))))

def b65x_regCoeff_11_0_5_0 : Fin 13 → ℚ :=
  ![(77920782152576182018072301581708168131816671440693109357579363562417484097350778323979618664190575788968042405845296653023505018400071357060623609904384000000000000000000000000000000000000), (460224933113242511096906501145934841494752438401822338733682824449961176689642808829787698907859750103089039156797192930800967910192167159080698891037417208000000000000000000000000000000000), (1246371981356443220654635448885607743599979157285340617419780868485888295640964300533738533413401015149938214456123247271938106784116919303491066693619365464538625000000000000000000000000000), (2046518308038455484514145514619372055675230953632328398554976162592914741544125706744070335754786793939148180333184812645759713054751212301520898465353628996998293062500000000000000000000000), (2269117459921137371542344982660200798139113203179795412937122465483965540565850986062796901650471570675866026754005893328987161408527979777355497536447774969249402340015625000000000000000000), (1789784641508749004917955837112532751724969776133062200302265433894950587145589945593860736126752521599752541553855885718174341727328542417171934188935989915327693925739281250000000000000000), (1029750195724949961636173229997039985115690840239044309053401890591179042950172191360470780275898729109251274258654667850539260129944706298487754903314098294586080584506041556640625000000000), (435437219350281176867122258784451045629930385497801811693538219934147365603116799209851547690548328402189591433899691045983139100692316784216875332523306316255037317537517610868164062500000), (134306776256684607264673763418604632240367676836983900398759870971146607872368124938475084232145547548424817226273109365336820772168452963227559279526637232942019582637783601451373291015625), (117873331572539786810997746831130808972659360773352203397800893593270431364986755688280506733743900146523302648954610512184311750915296670398073493398452396688282898350928884357497478515625/4), (139704625203484396371223119508296243204766723735354662186174367424914424826465824703733579202336722526694673389274546330923809209651359207076040481600220731147155918672686612358631283265625/32), (100383431873479157833265682909200491804285208879070302983118343191903370311207615757018141677649327827299947212677405412622888235195531242506114216911429545042438887159784258341650609817625/256), (66139510986909753524353904411262549714674530163571736624202038791592851943685084558040910078931013909406228660485704274340695561573404845871688271446572875100116253680534409879063137564489/4096)]

theorem b65x_regIdentity_11_0_5_0 (x : ℝ) :
    (b65x_regPoly_11_0_5.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_11_0_5_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_5, b65x_regCoeff_11_0_5_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_5_0 : ∀ i, 0 < b65x_regCoeff_11_0_5_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_5_0]

def b65x_regCoeff_11_0_5_1 : Fin 13 → ℚ :=
  ![(66139510986909753524353904411262549714674530163571736624202038791592851943685084558040910078931013909406228660485704274340695561573404845871688271446572875100116253680534409879063137564489/4096), (193721871388271150386122408064560980214929935955864417685344976356722186248335297994295623999781813875456269093661716818574707113378518642820737575373437695731290734485672655544965798809901/2048), (2083304761536700496509248970647006994032110633568944169759922433635110454009472334924309959492638826394922944930990105725867877113367980455143854177428870806948639927987618722838392993800233/8192), (3398846018847086566558267429702818933382222140307140609256072053587329324151853629179257255871701745531275055291192316970287236280343227128442981639738308688712900087162120622707229279368665/8192), (29979123856983430693636465487338089915992554111707607532905775368682565369228985314360391521347422458826149043038921382568751158370522618425605291819778401675546775441559051008361471337876455/65536), (5882721762949723539851037215479990256929509516253619421472094264813582154194279628317732896062749011491009200404695068492486994437061751452581614611390569995765795686777017983265595028679373/16384), (13481587942869011333820774901828622917602771768336691668018751528312954912537826123122753201995787772434486180655037603319767113853784521123449443462869935806146488929805688516622956725430111/65536), (5680433389695426410902836889250646685598220669129235260738788684087831369633529254344733239714806027267788269964872379687046970788318043620673733890195101258785833298454093679596112148277357/65536), (27949689073265417956986792545492919157721791916688031442325725911409442727249434449415109442052727795549154937909107601779416622899888550290265042368766756578960366104041165439220302072882855/1048576), (3058775151051521346223199326641019766705026095835009738488035088603700758789610966929673729153573313584781728257788658757191131304156249320832158215363788956331339104883437742681054012201785/524288), (1809176157876710867340728731934198410479695010008842148166899010522544426304595635003177772027882828850188239214166412621728739872165798911717845785758810114079328876393408470714182369196713/2097152), (162264156631815198217585014844005431709476748247377085648140704939499620789245448761452943618637103780713150111656425925807716443206227113966280847465847478553456861352691765452744123299149/2097152), (53403961300553429077651275450606438625865767446267994653143537356302604377666166873708986425721397093882503304083789932368983609327972357014470474403412576202850587584456336896789246544649/16777216)]

theorem b65x_regIdentity_11_0_5_1 (x : ℝ) :
    (b65x_regPoly_11_0_5.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_11_0_5_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_5, b65x_regCoeff_11_0_5_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_5_1 : ∀ i, 0 < b65x_regCoeff_11_0_5_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_5_1]

def b65x_regCoeff_11_0_5_2 : Fin 13 → ℚ :=
  ![(53403961300553429077651275450606438625865767446267994653143537356302604377666166873708986425721397093882503304083789932368983609327972357014470474403412576202850587584456336896789246544649/16777216), (156107338441350465263691449367447084213838410521657780582010426327724197820504604340474990594218366283516229513441257539705419597539296985197672574699018228718741565554723501165614972303543/8388608), (1678812462371605740704121777158188928149982202923187699096653584898101261204834864992491498890688553229720623430903038193884520955849006636620042175356908419507634319601852901440911425059937/33554432), (2743735730015277215561108651508930462170175726655108250368515006527802427440113898372707148189925163842539322812241870264496722974572047476284096920496967087419849568289818794917859106834755/33554432), (24281332172071528752603514128560048622954594515804562202357498379184006862474100116878530625569705000747260843520034699206029485559523178148020593206522323818206201148854189606009328647164855/268435456), (4787553043251557230179312602654562364140249617845567864125960267237294732238092789512521452376358211591867114333793286668284012299742608616934997922428601698635668590968280109012275475706599/67108864), (11040350928572147868265159900238575254301958259797192541985301238390257629775331946239979491551733624206731732103838655008048899940539313567705888731092054099276132549693889359068031559490039/268435456), (4687771107259578831824821389917791587222817059198194801430921763677408950111226733499354682277407812628586589256835046272146631877967530063744832024533368573603822105556352745271570012133039/268435456), (23279737686246250324863257223979593175874773529092627398124088556427203519402590987645298780922880637706713810941580847938754007750236891874788419445328605551218035380556826664052184095720455/4294967296), (2575722441923653626157290529732327319371703186719073308489707495225463127242882201726072387618622782259134815713536868767855589149418992894082197851361663350678944938547617263098835644292155/2147483648), (1543132479833971056777381601890846704359213515205974177204265284993570494600142808835024070475750826345553590836992762019609794854419716324705874190661558021165604538435732499268713648238017/8589934592), (140490926988834146249820313601774058400171196218480019328840023765746998683944348377575559618663291383662021871562759459564420084763377719641289649927696169740142234256946081020870368886943/8589934592), (47051548367962766023680340882536781568575580757099638343318849346394060708420590817194535424081558172248136490072395531380185090554385772622724405104841229569447049353477771955837354027289/68719476736)]

theorem b65x_regIdentity_11_0_5_2 (x : ℝ) :
    (b65x_regPoly_11_0_5.comp (C (3/4) + C ((7/8) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_11_0_5_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_5, b65x_regCoeff_11_0_5_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_5_2 : ∀ i, 0 < b65x_regCoeff_11_0_5_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_5_2]

def b65x_regCoeff_11_0_5_3 : Fin 13 → ℚ :=
  ![(47051548367962766023680340882536781568575580757099638343318849346394060708420590817194535424081558172248136490072395531380185090554385772622724405104841229569447049353477771955837354027289/68719476736), (142482081333996601713482440739282917316837834376936706432189596586052549007896620599599699579407440782909184667526040863292825645462716514321940346088178726644738975667407785560795448471715/34359738368), (1602037422094718431166306254242635234481203644843126745375876258774714182520832722206899433191671619896524013853188272235850700123565580775122411288328182861089416889808945573203660045980425/137438953472), (2767700862127937155227767620402986519744438586603607968615124889116176112965183386026946209880522738623217959421646270164541953627349966229563856781070192332392769173300882995088939272394375/137438953472), (26236041751387627532496778939370824610633089636841144472208481939650347885400946775098178953099053693583147577381939586941159812036976926849200044547746152457749058625674147923551931747784375/1099511627776), (5628304113068150407890903902665031027630114135116290768653087305581515766094200280137395729379038422049980130888985185002555800331048035239722142009284400797975199671431730934070086981371875/274877906944), (14377531656541109484307362845223442609212280453456623558276590776333573249874561843295660863694059242781882216625511550140926176922768546109411007593144374564702191385289965969318788925609375/1099511627776), (6898681653261624180381021134866776996227679508239726657341478083044485602951959700813783664685646369488464900197606581174387702582750435656472954812949115094085793159957665840161342499921875/1099511627776), (39553495252620425013374757855498867914124558993807335153472456832115244029773587554415835112610627768267584946079983246021002822995124890279334637731137126069738870155763598805482451896484375/17592186044416), (5167519687615729127364047070315254711491033839275687088215668468465338946230236288387246436894088638424567059720164687115403617693476066030135140839043758633176492729964035634412921396484375/8796093022208), (3742245737387552799503456326798209983051927081139211417985634943497628400876191910160230374039837103486203294152880698055689086203515284408234065488151472905872714096760139291347909541015625/35184372088832), (422083305200482883225988894329193755741320331867138437162573905281732444485326611195307836839347730183387199301614677133493698848485096233622347924912398448352904517066640778762936669921875/35184372088832), (179802119772953626550019350736979914887602686300598215796371482188346496300559332474022829108993643033753506232408612121861031592416653709875084149775357384665005625789220216026135009765625/281474976710656)]

theorem b65x_regIdentity_11_0_5_3 (x : ℝ) :
    (b65x_regPoly_11_0_5.comp (C (7/8) + C ((15/16) - (7/8)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_11_0_5_3).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_5, b65x_regCoeff_11_0_5_3, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_5_3 : ∀ i, 0 < b65x_regCoeff_11_0_5_3 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_5_3]

def b65x_regCoeff_11_0_5_4 : Fin 13 → ℚ :=
  ![(179802119772953626550019350736979914887602686300598215796371482188346496300559332474022829108993643033753506232408612121861031592416653709875084149775357384665005625789220216026135009765625/281474976710656), (14665381764797249553008644735218248615185965879332026278317567660413380552043923278345081310954149864734164924451394904011174491095608112000363065551709213205264045037627483664433544921875/4398046511104), (6091921491943735073161550404316946063027631687217295651394811554921078126835381804784551940171519680711728362294406267816277407603011557725315438791648449000843755817786082616027470703125/549755813888), (426257423452979986279120441609441321902599727071597317522212849387843570290083853014121109639886886282414633277158647506338113750656283603389997986672553502641872526520566155864326171875/17179869184), (183586601227360985519297141974066370901535343968841769609532001815844812696205877107867466550568232278784500949681012474086851218857954622302852821243482983444874044714830355792912109375/4294967296), (1937739359893610281626202928095931371182067824187154535952056481444067829578095554839898935684026849539826286250735823907605153945057283245759145421117549385496288952470189728656796875/33554432), (253321114053111971004231235756445704072603332639731552243352127180652308772478806976611426726283578019542573234368432906256472379244011897952451303959077392796256071416085280772046875/4194304), (6365965957546090452342071837659542112977041589233079484432052560834231516635567703778030234412294279687445160992076096669648622052636808883908692817462492312607209475368427337884375/131072), (2083477897792791651230906547811846988381709854174063683429251064837807882804540726574781743752411503679601060151442841986438444863995900323154253892863743752407310974065747639034375/65536), (19157529293182982233488068535623131001838380217908596784164828935132800933571018457075535219503412080832978138219467954810298420919026651426480784034022645043621243778524358864375/1024), (1270691182926925692341373808909490168439989823100879450899122995914125490171510414345372009331341209496930907969174326546293065458012124489049775696743173399600892524951781288325/128), (15387127356748099170622294999958475458108576711559107951590331565440215095703496244163870866285335409462943410094405714652141452560710992543475986188961966128530122151933442255/4), (782042147614421463638806938750859878762976669936760900077444589980228221384725130317589952996882287433073536480533071323959896481016989208825063164800459342146288944573523489)]

theorem b65x_regIdentity_11_0_5_4 (x : ℝ) :
    (b65x_regPoly_11_0_5.comp (C (15/16) + C ((1) - (15/16)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_11_0_5_4).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_11_0_5, b65x_regCoeff_11_0_5_4, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_11_0_5_4 : ∀ i, 0 < b65x_regCoeff_11_0_5_4 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_11_0_5_4]

theorem b65x_regPoly_positive_11_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_11_0_5.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      12 b65x_regCoeff_11_0_5_0 b65x_regIdentity_11_0_5_0
      b65x_regCoeff_positive_11_0_5_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      12 b65x_regCoeff_11_0_5_1 b65x_regIdentity_11_0_5_1
      b65x_regCoeff_positive_11_0_5_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h2 : t ≤ (7/8 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (3/4) (7/8) (by norm_num)
      12 b65x_regCoeff_11_0_5_2 b65x_regIdentity_11_0_5_2
      b65x_regCoeff_positive_11_0_5_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h3 : t ≤ (15/16 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (7/8) (15/16) (by norm_num)
      12 b65x_regCoeff_11_0_5_3 b65x_regIdentity_11_0_5_3
      b65x_regCoeff_positive_11_0_5_3 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (15/16) (1) (by norm_num)
    12 b65x_regCoeff_11_0_5_4 b65x_regIdentity_11_0_5_4
    b65x_regCoeff_positive_11_0_5_4 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_11_0_5 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_11_0 5)).eval₂ (Rat.castHom ℝ) t =
      (4096 : ℝ) * b65x_regPoly_11_0_5.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_11_0, b65x_certP5_11_0, b65x_certP7_11_0,
    b65x_certN_11_0, b65x_certD_11_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_11_0_5,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_11_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_11_0 5)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_11_0_5]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_11_0_5 t ht)

theorem b65x_certFactors_ne_zero_11_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1))
    (j : Fin 6) : b65x_cpEval (b65x_certFactors_11_0 j) t ≠ 0 := by
  apply b65x_cpEval_ne_zero
  fin_cases j

  · exact b65x_certFactor_norm_positive_11_0_0 t ht

  · exact b65x_certFactor_norm_positive_11_0_1 t ht

  · exact b65x_certFactor_norm_positive_11_0_2 t ht

  · exact b65x_certFactor_norm_positive_11_0_3 t ht

  · exact b65x_certFactor_norm_positive_11_0_4 t ht

  · exact b65x_certFactor_norm_positive_11_0_5 t ht

theorem b65x_certND_ratio_11_0 (t : ℝ) :
    b65b_inverseNormalization (b65x_piece 11 0 t) =
      b65x_cpEval b65x_certN_11_0 t / b65x_cpEval b65x_certD_11_0 t := by
  have hQ : (1 + t ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hQc : (((1 + t ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ
  push_cast at hQc
  have hrel : b65x_cpEval b65x_certD_11_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 6).1 : ℂ) - b65x_piece 11 0 t *
          (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ))) := by
    norm_num [b65x_cpEval, b65x_certD_11_0, Polynomial.eval₂_pow,
      b65x_piece, b65x_centre, b65x_radius, b65x_et, mr_centre, mr_basePoint,
      b65b_vertex0, b65b_track, b65b_radius, b65b_boxCentre]
    push_cast
    field_simp [hQc]
    <;> ring
  have hnrel : b65x_cpEval b65x_certN_11_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 0).1 : ℂ) * ((b65b_boxCentre 6).1 : ℂ)) := by
    norm_num [b65x_cpEval, b65x_certN_11_0, Polynomial.eval₂_pow, b65b_boxCentre]
    all_goals push_cast
    all_goals ring
  unfold b65b_inverseNormalization
  rw [hnrel, hrel]
  have hLQ : (50000000000000 : ℂ) * (1) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    norm_num
  exact (mul_div_mul_left _ _ hLQ).symm

theorem b65x_piece_regular_11_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    ((b65b_boxCentre 6).1 : ℂ) - b65x_piece 11 0 t *
        (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
      b65b_inverseNormalization (b65x_piece 11 0 t) ∈ b65s_regular := by

  have h0 := b65x_certFactors_ne_zero_11_0 t ht 0

  have h1 := b65x_certFactors_ne_zero_11_0 t ht 1

  have h2 := b65x_certFactors_ne_zero_11_0 t ht 2

  have h3 := b65x_certFactors_ne_zero_11_0 t ht 3

  have h4 := b65x_certFactors_ne_zero_11_0 t ht 4

  have h5 := b65x_certFactors_ne_zero_11_0 t ht 5

  change b65x_cpEval b65x_certD_11_0 t ≠ 0 at h0
  change b65x_cpEval (b65x_cpSub b65x_certN_11_0 (b65x_cpScale 3 b65x_certD_11_0)) t ≠ 0 at h1
  change b65x_cpEval (b65x_cpSub b65x_certN_11_0 b65x_certD_11_0) t ≠ 0 at h2
  change b65x_cpEval (b65x_cpAdd b65x_certN_11_0 (b65x_cpScale 2 b65x_certD_11_0)) t ≠ 0 at h3
  change b65x_cpEval b65x_certP5_11_0 t ≠ 0 at h4
  change b65x_cpEval b65x_certP7_11_0 t ≠ 0 at h5
  norm_num only [b65x_certFactors_11_0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, b65x_certP5_11_0, b65x_certP7_11_0,
    b65x_cpEval_sub, b65x_cpEval_add, b65x_cpEval_mul, b65x_cpEval_pow,
    b65x_cpEval_scale] at h0 h1 h2 h3 h4 h5
  have hN : b65x_cpEval b65x_certN_11_0 t ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [b65x_cpEval, b65x_certN_11_0, Polynomial.eval₂_pow,
      pow_two, Complex.mul_re] at hr
    skip
  have hreg : b65b_inverseNormalization (b65x_piece 11 0 t) ∈ b65s_regular := by
    rw [b65x_certND_ratio_11_0]
    exact b65x_regular_of_homogeneous _ _ h0 hN h1 h2 h3
      (by simpa only [mul_assoc] using h4) (by simpa only [mul_assoc] using h5)
  refine ⟨?_, hreg⟩
  intro h
  apply hreg.1
  simp [b65b_inverseNormalization, h]

end HodgeLean.Foundations.Program

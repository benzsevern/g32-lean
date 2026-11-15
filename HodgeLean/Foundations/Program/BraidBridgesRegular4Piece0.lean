import HodgeLean.Foundations.Program.BraidBridgesInterval
import HodgeLean.Foundations.Program.BraidBridgesRegular3Piece2

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

def b65x_certN_4_0 : b65x_CPoly := (C (291668908382000) + X * (0), C (0) + X * (0))
def b65x_certD_4_0 : b65x_CPoly := (C (2228834950000000) + X * (C (-2273299727518203) + X * (0)), C (-4112139000000000) + X * (C (4038532723486194) + X * (0)))

def b65x_certP5_4_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_4_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_4_0 (b65x_cpScale 3 b65x_certD_4_0)) 4))
    (b65x_cpScale (5) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_4_0 b65x_certD_4_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_4_0 (b65x_cpScale 2 b65x_certD_4_0)) 3)))

def b65x_certP7_4_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_4_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_4_0 (b65x_cpScale 3 b65x_certD_4_0)) 4))
    (b65x_cpScale (-7) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_4_0 b65x_certD_4_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_4_0 (b65x_cpScale 2 b65x_certD_4_0)) 3)))

def b65x_certFactors_4_0 : Fin 6 → b65x_CPoly :=
  ![b65x_certD_4_0,
    b65x_cpSub b65x_certN_4_0 (b65x_cpScale 3 b65x_certD_4_0),
    b65x_cpSub b65x_certN_4_0 b65x_certD_4_0,
    b65x_cpAdd b65x_certN_4_0 (b65x_cpScale 2 b65x_certD_4_0),
    b65x_certP5_4_0, b65x_certP7_4_0]

def b65x_regPoly_4_0_0 : ℚ[X] :=
  C (4375478477932500500000000000000) + X * (C (-8669527119816736766624340000000) + X * (C (4295527641960630298563720990969) + X * (0)))

def b65x_regCoeff_4_0_0_0 : Fin 3 → ℚ :=
  ![(4375478477932500500000000000000), (81429836048264233375660000000), (1479000076394031939380990969)]

theorem b65x_regIdentity_4_0_0_0 (x : ℝ) :
    (b65x_regPoly_4_0_0.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_4_0_0_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_4_0_0, b65x_regCoeff_4_0_0_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_4_0_0_0 : ∀ i, 0 < b65x_regCoeff_4_0_0_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_4_0_0_0]

theorem b65x_regPoly_positive_4_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_4_0_0.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_4_0_0_0 b65x_regIdentity_4_0_0_0
    b65x_regCoeff_positive_4_0_0_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_4_0_0 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_4_0 0)).eval₂ (Rat.castHom ℝ) t =
      (5 : ℝ) * b65x_regPoly_4_0_0.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_4_0, b65x_certP5_4_0, b65x_certP7_4_0,
    b65x_certN_4_0, b65x_certD_4_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_4_0_0,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_4_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_4_0 0)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_4_0_0]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_4_0_0 t ht)

def b65x_regPoly_4_0_1 : ℚ[X] :=
  C (38616222223619674540891584800000) + X * (C (-77230083058410232121565926944800) + X * (C (38659748777645672687073488918721) + X * (0)))

def b65x_regCoeff_4_0_1_0 : Fin 3 → ℚ :=
  ![(38616222223619674540891584800000), (2361388829116960217242655200), (45887942855115106399146773921)]

theorem b65x_regIdentity_4_0_1_0 (x : ℝ) :
    (b65x_regPoly_4_0_1.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_4_0_1_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_4_0_1, b65x_regCoeff_4_0_1_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_4_0_1_0 : ∀ i, 0 < b65x_regCoeff_4_0_1_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_4_0_1_0]

theorem b65x_regPoly_positive_4_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_4_0_1.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_4_0_1_0 b65x_regIdentity_4_0_1_0
    b65x_regCoeff_positive_4_0_1_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_4_0_1 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_4_0 1)).eval₂ (Rat.castHom ℝ) t =
      (5 : ℝ) * b65x_regPoly_4_0_1.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_4_0, b65x_certP5_4_0, b65x_certP7_4_0,
    b65x_certN_4_0, b65x_certD_4_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_4_0_1,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_4_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_4_0 1)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_4_0_1]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_4_0_1 t ht)

def b65x_regPoly_4_0_2 : ℚ[X] :=
  C (4132459885623790181611584800000) + X * (C (-8404306779836603840606628981600) + X * (C (4295527641960630298563720990969) + X * (0)))

def b65x_regCoeff_4_0_2_0 : Fin 3 → ℚ :=
  ![(4132459885623790181611584800000), (4062766381329278442919855109200), (4016753624782583343796802227769/4)]

theorem b65x_regIdentity_4_0_2_0 (x : ℝ) :
    (b65x_regPoly_4_0_2.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_4_0_2_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_4_0_2, b65x_regCoeff_4_0_2_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_4_0_2_0 : ∀ i, 0 < b65x_regCoeff_4_0_2_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_4_0_2_0]

def b65x_regCoeff_4_0_2_1 : Fin 3 → ℚ :=
  ![(4016753624782583343796802227769/4), (3924728111689193145550696464907/4), (3927425589587069505579297939521/16)]

theorem b65x_regIdentity_4_0_2_1 (x : ℝ) :
    (b65x_regPoly_4_0_2.comp (C (1/2) + C ((3/4) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_4_0_2_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_4_0_2, b65x_regCoeff_4_0_2_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_4_0_2_1 : ∀ i, 0 < b65x_regCoeff_4_0_2_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_4_0_2_1]

def b65x_regCoeff_4_0_2_2 : Fin 3 → ℚ :=
  ![(3927425589587069505579297939521/16), (1348738948938180014300737307/2), (23680747747816639568676809369)]

theorem b65x_regIdentity_4_0_2_2 (x : ℝ) :
    (b65x_regPoly_4_0_2.comp (C (3/4) + C ((1) - (3/4)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_4_0_2_2).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_4_0_2, b65x_regCoeff_4_0_2_2, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_4_0_2_2 : ∀ i, 0 < b65x_regCoeff_4_0_2_2 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_4_0_2_2]

theorem b65x_regPoly_positive_4_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_4_0_2.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      2 b65x_regCoeff_4_0_2_0 b65x_regIdentity_4_0_2_0
      b65x_regCoeff_positive_4_0_2_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  by_cases h1 : t ≤ (3/4 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (1/2) (3/4) (by norm_num)
      2 b65x_regCoeff_4_0_2_1 b65x_regIdentity_4_0_2_1
      b65x_regCoeff_positive_4_0_2_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (3/4) (1) (by norm_num)
    2 b65x_regCoeff_4_0_2_2 b65x_regIdentity_4_0_2_2
    b65x_regCoeff_positive_4_0_2_2 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_4_0_2 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_4_0 2)).eval₂ (Rat.castHom ℝ) t =
      (5 : ℝ) * b65x_regPoly_4_0_2.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_4_0, b65x_certP5_4_0, b65x_certP7_4_0,
    b65x_certN_4_0, b65x_certD_4_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_4_0_2,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_4_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_4_0 2)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_4_0_2]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_4_0_2 t ht)

def b65x_regPoly_4_0_3 : ℚ[X] :=
  C (4509748386904367785672896200000) + X * (C (-8802137289806803229633195509200) + X * (C (4295527641960630298563720990969) + X * (0)))

def b65x_regCoeff_4_0_3_0 : Fin 3 → ℚ :=
  ![(4509748386904367785672896200000), (217359484001932341712596890800), (3138739058194854603421681769)]

theorem b65x_regIdentity_4_0_3_0 (x : ℝ) :
    (b65x_regPoly_4_0_3.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_4_0_3_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_4_0_3, b65x_regCoeff_4_0_3_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_4_0_3_0 : ∀ i, 0 < b65x_regCoeff_4_0_3_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_4_0_3_0]

theorem b65x_regPoly_positive_4_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_4_0_3.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_4_0_3_0 b65x_regIdentity_4_0_3_0
    b65x_regCoeff_positive_4_0_3_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_4_0_3 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_4_0 3)).eval₂ (Rat.castHom ℝ) t =
      (20 : ℝ) * b65x_regPoly_4_0_3.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_4_0, b65x_certP5_4_0, b65x_certP7_4_0,
    b65x_certN_4_0, b65x_certD_4_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_4_0_3,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_4_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_4_0 3)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_4_0_3]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_4_0_3 t ht)

def b65x_regPoly_4_0_4 : ℚ[X] :=
  C (6416118762993705063869470375870577482545815480601635426451956522063989797879921960350039306398086859732298055682783431909147833681087263214790510465203568640000000000000000000000000000) + X * (C (-76830355475298269163706050417389567144905221108692595496587995967079874765907601346740357924947890143160964884917393755039201492213240378007147558281948378562560000000000000000000000000) + X * (C (421700700426059880675080548636627747106186594420756411695247259124749651327329223498274029973427412823340832410565149251447616455490148641933258330764805291102576640000000000000000000000) + X * (C (-1402881866965259712637330801917127643330485282586954538541564726822571565839007846239479383796026084388189848809155635245616157295032379359462736553753210398096578191360000000000000000000) + X * (C (3150435222119045630633553269748907002570442626185929125499449083650545775846059623169329817720068835393959146539188391383711173642489351111952343764896521720744803780106240000000000000000) + X * (C (-5031367350759850528134711185996657711865137479147525269681235552685308095696112561033784023994035143402792264507537252795883029287809054484999475953675833796767100615947776000000000000000) + X * (C (5859445464733939679078774220485883876209366295202746627860369921673627642604813239565792735824902749139350632886627633052956261935353514750419653370012749928374731776486314790400000000000) + X * (C (-5013733961541712382886804857679303244804346882697855466794841333891953962816878857576683414518085089170013272084689369566772635051584815564460279325506679527230508195290677284672000000000) + X * (C (3128386232282716964415831300714566906042128966543815109331584780154220293337035603461239187540661222944557690779488622894202488979671681421245270382022554983921209100516942420591760000000) + X * (C (-1388174470944148868173409133738837432311949837047483106413824803047049463271756574221443006328307867098321609181937314162357972663038960948208477666616660905975901622360794210372564800000) + X * (C (415813214528238363012116432296238971732736683276687227480957737071275667976770657910578769837406246557080169263706315193604294451560206405080148824397434697622755425542744011871704384000) + X * (C (-75490964184290189114786104729594011918607907100192868780565384472434898082348927937758079866888453630327502364950211213962742509299669039955349427548129502777248928568259463261748067600) + X * (C (6282017017565729592188190329302459635298801276942034597767095927152520697771759224799216588011195500390428488401229959713138579795249491125039022201712377502373983583383093549650657681) + X * (0)))))))))))))

def b65x_regCoeff_4_0_4_0 : Fin 13 → ℚ :=
  ![(6416118762993705063869470375870577482545815480601635426451956522063989797879921960350039306398086859732298055682783431909147833681087263214790510465203568640000000000000000000000000000), (38578247418275326184580619301752146218097175212873327369129480281227940191605262850830292714303097245207094225734704305390173258066426969573912346441468634398720000000000000000000000000), (106322058349959023983771904670972431327591754227087765838406967418471428279415347850599133128417190160781572910659328166150052929651474453620176702843920770921564160000000000000000000000), (177602869982404949657402117565242362024341650971835129583683102718433882059570872207398956430577401714007387840252445479351503850821411696957658207284066618323969326080000000000000000000), (200267441809473633401894775985896808263953829890476753681195726343784958617132923051441571896885410294701165924549927893243511084554193992582228205452755679980686970976640000000000000000), (160597399653205198270116979604034753254774205553218326305492664751275087023011661307994903281808743705433821768882283970716866053295844838670110861870346895923727334684752000000000000000), (93912657561280413013904361499450367097475288519008266585416129668725149404373753099669119454224302247230856314919566930874848745846956763250947565070364164171301130174942668600000000000), (40350336860816257312001473716094983317438883405994634356391318046003199473938971668380869624655802587727477255297420975400006996968897199026966095627054949826908016005995595313500000000), (12642365444359310351934620074174906926790049662863610977701369503511636038922109258977296305684273745057980787509802285609685682748910149117860289256746540722595582136252253897936562500), (2816946915915069286004935418184637926967458674888645560239448636988830219459615427757018340336223556832593068338994038872565050625699949305951228024643000188830059133253008264612334375), (847412361772798373855606911215666089593448858490048500408616607353894791473143286577765583235024364493048361657489673723159497640231421020576112024582233147048988054380022980622178875/2), (4944351859796222026310232260638555380632960444989300590691639367149535187158837490289072695754279943310632013086602797930998983319757022201073592370278941290493048417482031358163241775/128), (6611624468081973595979992173822651131927488139217931631843691129959008865953584469495337481752790186200284828100161430561605657848821993666545937288301843366056153387150737096613658481/4096)]

theorem b65x_regIdentity_4_0_4_0 (x : ℝ) :
    (b65x_regPoly_4_0_4.comp (C (0) + C ((1/2) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_4_0_4_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_4_0_4, b65x_regCoeff_4_0_4_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_4_0_4_0 : ∀ i, 0 < b65x_regCoeff_4_0_4_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_4_0_4_0]

def b65x_regCoeff_4_0_4_1 : Fin 13 → ℚ :=
  ![(6611624468081973595979992173822651131927488139217931631843691129959008865953584469495337481752790186200284828100161430561605657848821993666545937288301843366056153387150737096613658481/4096), (57465965061032682699047478913731873250622637696592532764515921278885849225403447329721662241250785358326431954073099960821040267437892195343442383789764936196266491524085857188008343/512), (18208398473974059074672071165132793829497208585707974583394462085262723615269711815728979631678443494162760001637463733907572771751618569024480222465683161005742958841447709163245673/512), (554421392751917193585048182568544540378240855558611622183253262811447295530025289167408256443989206612840651808526024365350745290162599502433706188705277074924997287998843848185955/128), (182303169494368786524359337415458355893558045716459397087143121664783066739982606516397149378599160950645935458163052091802435920340528551458719828722160389418253496465345927142095/256), (3004304057996194967357162135366960457546940214631818828565823461464395037858413794866710747544331502938987213132294119203577015947133164326866094603539860015198075198544287978119/16), (207042043164695976156222388844392230841826384222662743984716987390122982330800393724272039731957492749210311820905414128626968454066794281886450115508526743543807509922753268911/16), (7240410312079106094757166061543508174843121744080333274943253773973953010023576337138163773472721094482849553387377327553929503366950276440673543282199657871037035828873285519/4), (4807662758107385561643600112160377443659996473144804154389478490686842807565738264686261004666624078052070970101302297797911116345464727179101902005544213647495704090801816095/16), (4719558780093451889935508239183086804020025666192896826315499154632073322925747504441204581476064521069209240576042586316099716868902536859889386153409576703136255499964955/2), (4216914686450653941185094348041020967800069729458229536051864132547047672882208513044361274437623622216808634844530480804683015274623617022374884261985082899893557291388873/2), (109762546194185611927322471327274908756306506740726574324551904139722352825785176667197124508117349253280861187120516965847295404363181913461270504789720007114026316194686), (2360665298108487929403273172698774326183208037237237681115647660434475530362585221385605736590472948427912383579063119309877037719378520058498553152708117358106802174081)]

theorem b65x_regIdentity_4_0_4_1 (x : ℝ) :
    (b65x_regPoly_4_0_4.comp (C (1/2) + C ((1) - (1/2)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_4_0_4_1).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_4_0_4, b65x_regCoeff_4_0_4_1, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_4_0_4_1 : ∀ i, 0 < b65x_regCoeff_4_0_4_1 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_4_0_4_1]

theorem b65x_regPoly_positive_4_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_4_0_4.eval₂ (Rat.castHom ℝ) t := by

  by_cases h0 : t ≤ (1/2 : ℚ)
  · exact b65x_bernstein_interval_eval_pos _ (0) (1/2) (by norm_num)
      12 b65x_regCoeff_4_0_4_0 b65x_regIdentity_4_0_4_0
      b65x_regCoeff_positive_4_0_4_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

  exact b65x_bernstein_interval_eval_pos _ (1/2) (1) (by norm_num)
    12 b65x_regCoeff_4_0_4_1 b65x_regIdentity_4_0_4_1
    b65x_regCoeff_positive_4_0_4_1 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_4_0_4 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_4_0 4)).eval₂ (Rat.castHom ℝ) t =
      (25000000 : ℝ) * b65x_regPoly_4_0_4.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_4_0, b65x_certP5_4_0, b65x_certP7_4_0,
    b65x_certN_4_0, b65x_certD_4_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_4_0_4,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_4_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_4_0 4)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_4_0_4]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_4_0_4 t ht)

def b65x_regPoly_4_0_5 : ℚ[X] :=
  C (319163523696952041546024147278676656667921086221078975928645073151662014862748788015020518048524598431613101694342335090784276555366692278520314306168356864000000000000000000000000000000) + X * (C (-3811974404489060058054203658128021169150225034130865596688889891785089169091728643724907672082207280871429980446176001461749129360172849856943049363458683109376000000000000000000000000000) + X * (C (20874170785132949538515866482416267464588067629635585743449922571297086003172177645882859003468051491493293867759477061854890689851694618126771478780470220276315136000000000000000000000000) + X * (C (-69298413316360110917875270807580354777379141925928804698117003322650375970690704652479470918836951951756266089327046872328931996084597544132291735626849774497590789120000000000000000000000) + X * (C (155337946992904443726485298845893263494123725451341230182117716211103182560166612152230350469311697234173496841580798845994551189192224593067307279501384665988333635327744000000000000000000) + X * (C (-247687143515247748508161418727377362804186923150164677997799570344925364839160889521426389269413045499724509934987028273964368720151169499616286718746598265425473228886166016000000000000000) + X * (C (288063421861658989264951775157519901375970891718616203428008244830669065839627530439309560655107762018458319041755027492403700709352896321498800084294539279045826215927470025408000000000000) + X * (C (-246211844823202651366525448123228899967583789538223045237675982517475116377798068881300762339095396750758301993049369259740248065327531647174754823100771307114634710131793045221440000000000) + X * (C (153491451957096453257198877470456844471964367282691557267925120243337425844343481110730743959401153169607047277950795688724952833207507756496588864717352715447066809256778852730518800000000) + X * (C (-68064779512828406767863155415964238807144228246102896990496682615165345693781288779811300542786755192088425090768744917691985280998624944780525318986502544686664568318505599115514600000000) + X * (C (20379238862807688306392039712363545602536436519580229628099972090325689789872384641469994675071946037229798031104411535749778114453129999005958152021360465103540651197487912116725659680000) + X * (C (-3699057245030219266624519131750106584011787447909450570247703839149310006035097468950145913477534227886047615882560349484174382955683782957812121949858345636085197499844713699825655312400) + X * (C (307818833860720750017221326135820522129641262570159695290587700430473514190816202015161612812548579519130995931660268025943790409967225065126912087883906497616325195585771583932882226369) + X * (0)))))))))))))

def b65x_regCoeff_4_0_5_0 : Fin 13 → ℚ :=
  ![(319163523696952041546024147278676656667921086221078975928645073151662014862748788015020518048524598431613101694342335090784276555366692278520314306168356864000000000000000000000000000000), (17987879874364440498086109216098710864828000522082114454850986034855009261256812455338544500087900307927239885932019627662189304227457485300722310561599258624000000000000000000000000000), (7244899752123641957219963400693944018383944787276591162708589670798124104582573900228801766394898394028794678135161767412519543994960082738679989536259097179136000000000000000000000000), (677501400530414427505220850020032181796461866819622795194435506223030790729764783711121997574170202906036483357385796313629803514196278024484544663367329880570880000000000000000000000), (79965942525685160202598223558545008298499424615985323681081151653423623688197469157896296921665427864651894260407253854818235096963053350640563550542577157653247744000000000000000000), (4541573950628679118319292995175141125707307385569073981931173771048994545391775260330419520359898832707703971422261306059537849663169129128898286823919663765415785984000000000000000), (381957199603703647251907556459528140650288382113163684784261608391105805603871096630787780531519876786565447924953883936185641561023983243332137414773695676821139913408000000000000), (15366992372095411320329476131255494414897686227032454289208260550197101586558092108277013109750179747244067707685151265798180859603286329328293051263331200057204771226560000000000), (754767310612113244421036560496262681633825664011021060266801306716527761273930114628954422856030890882943870587518753274134842275891569125218587768737090316133447743318800000000), (27495873803395159174890456555197009397354363013528948049633909173336757633538168991008314118948556421624500561850583936973307612393754099984004720050487197933307752160600000000), (486263977193986998934881788711172087682369465596530380605532087104235141116026447899213072235672559139053496348754053600343513638240908004324534630633624109824058894659680000), (67438751015266491497904590786077677937189115017643895239570643676410162338508515121731443067919243002364719567202129590035320674890063421379108120211374538449957064047600), (3087278035335478524955608196303829794376189163983509677973031960714237529792225827718453315587553173144028145006937020459317935120688752874278948757187802397086593969)]

theorem b65x_regIdentity_4_0_5_0 (x : ℝ) :
    (b65x_regPoly_4_0_5.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_4_0_5_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_4_0_5, b65x_regCoeff_4_0_5_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_4_0_5_0 : ∀ i, 0 < b65x_regCoeff_4_0_5_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_4_0_5_0]

theorem b65x_regPoly_positive_4_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_4_0_5.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    12 b65x_regCoeff_4_0_5_0 b65x_regIdentity_4_0_5_0
    b65x_regCoeff_positive_4_0_5_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_4_0_5 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_4_0 5)).eval₂ (Rat.castHom ℝ) t =
      (1000000 : ℝ) * b65x_regPoly_4_0_5.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_4_0, b65x_certP5_4_0, b65x_certP7_4_0,
    b65x_certN_4_0, b65x_certD_4_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_4_0_5,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_4_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_4_0 5)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_4_0_5]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_4_0_5 t ht)

theorem b65x_certFactors_ne_zero_4_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1))
    (j : Fin 6) : b65x_cpEval (b65x_certFactors_4_0 j) t ≠ 0 := by
  apply b65x_cpEval_ne_zero
  fin_cases j

  · exact b65x_certFactor_norm_positive_4_0_0 t ht

  · exact b65x_certFactor_norm_positive_4_0_1 t ht

  · exact b65x_certFactor_norm_positive_4_0_2 t ht

  · exact b65x_certFactor_norm_positive_4_0_3 t ht

  · exact b65x_certFactor_norm_positive_4_0_4 t ht

  · exact b65x_certFactor_norm_positive_4_0_5 t ht

theorem b65x_certND_ratio_4_0 (t : ℝ) :
    b65b_inverseNormalization (b65x_piece 4 0 t) =
      b65x_cpEval b65x_certN_4_0 t / b65x_cpEval b65x_certD_4_0 t := by
  have hQ : (1 + t ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hQc : (((1 + t ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ
  push_cast at hQc
  have hrel : b65x_cpEval b65x_certD_4_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 6).1 : ℂ) - b65x_piece 4 0 t *
          (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ))) := by
    norm_num [b65x_cpEval, b65x_certD_4_0, Polynomial.eval₂_pow,
      b65x_piece, b65x_centre, b65x_radius, b65x_et, mr_centre, mr_basePoint,
      b65b_vertex0, b65b_track, b65b_radius, b65b_boxCentre]
    push_cast
    field_simp [hQc]
    <;> ring
  have hnrel : b65x_cpEval b65x_certN_4_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 0).1 : ℂ) * ((b65b_boxCentre 6).1 : ℂ)) := by
    norm_num [b65x_cpEval, b65x_certN_4_0, Polynomial.eval₂_pow, b65b_boxCentre]
    all_goals push_cast
    all_goals ring
  unfold b65b_inverseNormalization
  rw [hnrel, hrel]
  have hLQ : (50000000000000 : ℂ) * (1) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    norm_num
  exact (mul_div_mul_left _ _ hLQ).symm

theorem b65x_piece_regular_4_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    ((b65b_boxCentre 6).1 : ℂ) - b65x_piece 4 0 t *
        (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
      b65b_inverseNormalization (b65x_piece 4 0 t) ∈ b65s_regular := by

  have h0 := b65x_certFactors_ne_zero_4_0 t ht 0

  have h1 := b65x_certFactors_ne_zero_4_0 t ht 1

  have h2 := b65x_certFactors_ne_zero_4_0 t ht 2

  have h3 := b65x_certFactors_ne_zero_4_0 t ht 3

  have h4 := b65x_certFactors_ne_zero_4_0 t ht 4

  have h5 := b65x_certFactors_ne_zero_4_0 t ht 5

  change b65x_cpEval b65x_certD_4_0 t ≠ 0 at h0
  change b65x_cpEval (b65x_cpSub b65x_certN_4_0 (b65x_cpScale 3 b65x_certD_4_0)) t ≠ 0 at h1
  change b65x_cpEval (b65x_cpSub b65x_certN_4_0 b65x_certD_4_0) t ≠ 0 at h2
  change b65x_cpEval (b65x_cpAdd b65x_certN_4_0 (b65x_cpScale 2 b65x_certD_4_0)) t ≠ 0 at h3
  change b65x_cpEval b65x_certP5_4_0 t ≠ 0 at h4
  change b65x_cpEval b65x_certP7_4_0 t ≠ 0 at h5
  norm_num only [b65x_certFactors_4_0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, b65x_certP5_4_0, b65x_certP7_4_0,
    b65x_cpEval_sub, b65x_cpEval_add, b65x_cpEval_mul, b65x_cpEval_pow,
    b65x_cpEval_scale] at h0 h1 h2 h3 h4 h5
  have hN : b65x_cpEval b65x_certN_4_0 t ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [b65x_cpEval, b65x_certN_4_0, Polynomial.eval₂_pow,
      pow_two, Complex.mul_re] at hr
    skip
  have hreg : b65b_inverseNormalization (b65x_piece 4 0 t) ∈ b65s_regular := by
    rw [b65x_certND_ratio_4_0]
    exact b65x_regular_of_homogeneous _ _ h0 hN h1 h2 h3
      (by simpa only [mul_assoc] using h4) (by simpa only [mul_assoc] using h5)
  refine ⟨?_, hreg⟩
  intro h
  apply hreg.1
  simp [b65b_inverseNormalization, h]

end HodgeLean.Foundations.Program

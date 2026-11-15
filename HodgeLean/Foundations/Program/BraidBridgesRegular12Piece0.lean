import HodgeLean.Foundations.Program.BraidBridgesInterval
import HodgeLean.Foundations.Program.BraidBridgesRegular11Piece2

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

def b65x_certN_12_0 : b65x_CPoly := (C (291668908382000) + X * (0), C (0) + X * (0))
def b65x_certD_12_0 : b65x_CPoly := (C (2228834950000000) + X * (C (-1694629913257221) + X * (0)), C (-4112139000000000) + X * (C (4110926321984622) + X * (0)))

def b65x_certP5_12_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_12_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_12_0 (b65x_cpScale 3 b65x_certD_12_0)) 4))
    (b65x_cpScale (5) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_12_0 b65x_certD_12_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_12_0 (b65x_cpScale 2 b65x_certD_12_0)) 3)))

def b65x_certP7_12_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_12_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_12_0 (b65x_cpScale 3 b65x_certD_12_0)) 4))
    (b65x_cpScale (-7) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_12_0 b65x_certD_12_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_12_0 (b65x_cpScale 2 b65x_certD_12_0)) 3)))

def b65x_certFactors_12_0 : Fin 6 → b65x_CPoly :=
  ![b65x_certD_12_0,
    b65x_cpSub b65x_certN_12_0 (b65x_cpScale 3 b65x_certD_12_0),
    b65x_cpSub b65x_certN_12_0 b65x_certD_12_0,
    b65x_cpAdd b65x_certN_12_0 (b65x_cpScale 2 b65x_certD_12_0),
    b65x_certP5_12_0, b65x_certP7_12_0]

def b65x_regPoly_12_0_0 : ℚ[X] :=
  C (875095695586500100000000000000) + X * (C (-1654540066619414722490556000000) + X * (C (790859430707687536192420525029) + X * (0)))

def b65x_regCoeff_12_0_0_0 : Fin 3 → ℚ :=
  ![(875095695586500100000000000000), (95651324553585477509444000000), (11415059674772913701864525029)]

theorem b65x_regIdentity_12_0_0_0 (x : ℝ) :
    (b65x_regPoly_12_0_0.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_12_0_0_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_12_0_0, b65x_regCoeff_12_0_0_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_12_0_0_0 : ∀ i, 0 < b65x_regCoeff_12_0_0_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_12_0_0_0]

theorem b65x_regPoly_positive_12_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_12_0_0.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_12_0_0_0 b65x_regIdentity_12_0_0_0
    b65x_regCoeff_positive_12_0_0_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_12_0_0 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_12_0 0)).eval₂ (Rat.castHom ℝ) t =
      (25 : ℝ) * b65x_regPoly_12_0_0.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_12_0, b65x_certP5_12_0, b65x_certP7_12_0,
    b65x_certN_12_0, b65x_certD_12_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_12_0_0,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_12_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_12_0 0)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_12_0_0]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_12_0_0 t ht)

def b65x_regPoly_12_0_1 : ℚ[X] :=
  C (7723244444723934908178316960000) + X * (C (-14772235593916040422643261658720) + X * (C (7117734876369187825731784725261) + X * (0)))

def b65x_regCoeff_12_0_1_0 : Fin 3 → ℚ :=
  ![(7723244444723934908178316960000), (674253295531829393713372261280), (68743727177082311266840026541)]

theorem b65x_regIdentity_12_0_1_0 (x : ℝ) :
    (b65x_regPoly_12_0_1.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_12_0_1_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_12_0_1, b65x_regCoeff_12_0_1_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_12_0_1_0 : ∀ i, 0 < b65x_regCoeff_12_0_1_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_12_0_1_0]

theorem b65x_regPoly_positive_12_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_12_0_1.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_12_0_1_0 b65x_regIdentity_12_0_1_0
    b65x_regCoeff_positive_12_0_1_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_12_0_1 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_12_0 1)).eval₂ (Rat.castHom ℝ) t =
      (25 : ℝ) * b65x_regPoly_12_0_1.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_12_0, b65x_certP5_12_0, b65x_certP7_12_0,
    b65x_certN_12_0, b65x_certD_12_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_12_0_1,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_12_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_12_0 1)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_12_0_1]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_12_0_1 t ht)

def b65x_regPoly_12_0_2 : ℚ[X] :=
  C (826491977124758036322316960000) + X * (C (-1614998398066517362566641886240) + X * (C (790859430707687536192420525029) + X * (0)))

def b65x_regCoeff_12_0_2_0 : Fin 3 → ℚ :=
  ![(826491977124758036322316960000), (37985556182998710077992033760), (2353009765928209948095598789)]

theorem b65x_regIdentity_12_0_2_0 (x : ℝ) :
    (b65x_regPoly_12_0_2.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_12_0_2_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_12_0_2, b65x_regCoeff_12_0_2_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_12_0_2_0 : ∀ i, 0 < b65x_regCoeff_12_0_2_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_12_0_2_0]

theorem b65x_regPoly_positive_12_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_12_0_2.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_12_0_2_0 b65x_regIdentity_12_0_2_0
    b65x_regCoeff_positive_12_0_2_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_12_0_2 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_12_0 2)).eval₂ (Rat.castHom ℝ) t =
      (25 : ℝ) * b65x_regPoly_12_0_2.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_12_0, b65x_certP5_12_0, b65x_certP7_12_0,
    b65x_certN_12_0, b65x_certD_12_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_12_0_2,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_12_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_12_0 2)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_12_0_2]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_12_0_2 t ht)

def b65x_regPoly_12_0_3 : ℚ[X] :=
  C (901949677380873557134579240000) + X * (C (-1674310900895863402452513056880) + X * (C (790859430707687536192420525029) + X * (0)))

def b65x_regCoeff_12_0_3_0 : Fin 3 → ℚ :=
  ![(901949677380873557134579240000), (129588453865883711816645423120), (18498207192697690874486708149)]

theorem b65x_regIdentity_12_0_3_0 (x : ℝ) :
    (b65x_regPoly_12_0_3.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_12_0_3_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_12_0_3, b65x_regCoeff_12_0_3_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_12_0_3_0 : ∀ i, 0 < b65x_regCoeff_12_0_3_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_12_0_3_0]

theorem b65x_regPoly_positive_12_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_12_0_3.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_12_0_3_0 b65x_regIdentity_12_0_3_0
    b65x_regCoeff_positive_12_0_3_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_12_0_3 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_12_0 3)).eval₂ (Rat.castHom ℝ) t =
      (100 : ℝ) * b65x_regPoly_12_0_3.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_12_0, b65x_certP5_12_0, b65x_certP7_12_0,
    b65x_certN_12_0, b65x_certD_12_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_12_0_3,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_12_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_12_0 3)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_12_0_3]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_12_0_3 t ht)

def b65x_regPoly_12_0_4 : ℚ[X] :=
  C (410631600831597124087646104055716958882932190758504667292925217412095347064315005462402515609477559022867075563698139642185461355589584845746592669773028392960000000000000000000000) + X * (C (-4699774703308743208092339268075366947162295214588606080998222956805362558506732980026017034061871863723081103080238848367487800517577596837228919779413878248570880000000000000000000) + X * (C (24672872102906514197526364565684318607234884245777415625177128505599618265790852917819071103613634617770749414040281695831602186071023547177428811569489575195865251840000000000000000) + X * (C (-78562063106809564075824140962708967887994989994147364438216221975562079865080840858051708030432126229672199228051871717241862240347982555800242085638650824589294391787520000000000000) + X * (C (168982723203198818990194669649098750084195517334508082593396200748249356568308044102890712840216555598530584136122446880007632844914721711934420858207127147000262222879784960000000000) + X * (C (-258666297262232632898246539377344011423950573213273863126166196019994747974073343292573343590124290354288738393603202425157632979037008948420949427445982871707114274686559846400000000) + X * (C (288930353521236707774846249213995322174877648394848633674278882060432181490350321697767537226158081567962423290642106747672046895835403785100887501948485273356005240010735982182400000) + X * (C (-237290507043176088645117851497827413338994724090930781819633083331090839634227607690044420617226853859308307406591905532492499206000105264706856048508549171173526574801881213972480000) + X * (C (142206832194695397328904559319532582279334259024912681688793419995511740516390070466245723605656548062737770598165642680664481904214460219841745108661524624946408433369158055976576000) + X * (C (-60648901468346114958545492202529780580927254026001131519593547501083173393456031111211703117427679107660782790375658796503594907685064595900947325846280555346121228510443235993075200) + X * (C (17472421909657661707951632185694482560064764512490455298426054765833478638805436614733644028158206074599649382413701266077598380618225203276388532759303857801478976264837730795696640) + X * (C (-3052969435896893399219400807557140947007501406366106134396243503439227363464622664097441241937244008415213461188835769412737975323889594715523933307934575884434169003200359932534640) + X * (C (244678487243815024721517026374787703687295646923967425303019638431295680074207651616645327700406229550747321914907295556931249945819198746235539924296145223292831546447738569173321) + X * (0)))))))))))))

def b65x_regCoeff_12_0_4_0 : Fin 13 → ℚ :=
  ![(410631600831597124087646104055716958882932190758504667292925217412095347064315005462402515609477559022867075563698139642185461355589584845746592669773028392960000000000000000000000), (227804506670422280959413980593236559432891074513449926516879652139781606265047085522813153251858844551323803684138827338737735749497421311730192257862462466949120000000000000000000), (77036021395749098295275484532601474723161475364056775529740329938923028461580498051449759158563012326084267361731580173476829846582581787185810200956788396945571840000000000000000), (18001423226068753642987842246767044672697628124484163096348286800138429106675620436619566386330428296590866951399302143132090125193755990705829538547870149159726612480000000000000), (3216238403828284612648715656724783083122465505312727712180466275834386393843681879974835423511533175335111259446879499287340595479353218330216020659753011553829592104960000000000), (444633734979603749246987298117021704909433271242633058035962329291892098689696616573591976276015740652000312900929328562679102562641082917610812012307780145224800999833600000000), (49253296188842204199970168789911293608493958876040727365944854655391067062471595603510488735783255960336736867371702369039316885959027831464353373297299814974087115937382400000), (4360914794953240899023876921504382096146003025210947515150160262501520417844494135301548096071694441521444238933577559085017778714299197227828238182619313116565215664721920000), (315258974280614697805283209978392481405878015479265850052494370695010138367612895983391273263530341278771991867072480180765577732285574992689433775055629268248624294850176000), (18187514713073907194109578469767738873844151990026856263362448298168139889871423745082313337810128340205691946701712166930598174002161580112607515530142535048779627836428800), (816437743254471899300726731115928543226581699479427718972303032894127252625812387250181295414367179490623610500312699885649269339881270738174909067621043756186057287127040), (25655006867841872891640776083569176922913894722950420219299191631959349201031321279305806187540230642153830220140358937929269612707571411994842422733570071468196017937040), (474963186873948393279242239963404911887853664115643494335717974069860531103015902844287106468835971071616276663814043614694541105205213187774967211437121359811225756121)]

theorem b65x_regIdentity_12_0_4_0 (x : ℝ) :
    (b65x_regPoly_12_0_4.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_12_0_4_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_12_0_4, b65x_regCoeff_12_0_4_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_12_0_4_0 : ∀ i, 0 < b65x_regCoeff_12_0_4_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_12_0_4_0]

theorem b65x_regPoly_positive_12_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_12_0_4.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    12 b65x_regCoeff_12_0_4_0 b65x_regIdentity_12_0_4_0
    b65x_regCoeff_positive_12_0_4_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_12_0_4 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_12_0 4)).eval₂ (Rat.castHom ℝ) t =
      (390625000000 : ℝ) * b65x_regPoly_12_0_4.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_12_0, b65x_certP5_12_0, b65x_certP7_12_0,
    b65x_certN_12_0, b65x_certD_12_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_12_0_4,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_12_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_12_0 4)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_12_0_4]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_12_0_4 t ht)

def b65x_regPoly_12_0_5 : ℚ[X] :=
  C (20426465516604930658945545425835306026746949518149054459433284681706368951215922432961313155105574299623238508437909445810193699543468305825300115594774839296000000000000000000000000) + X * (C (-233287727639181306803685000484300757064606830949451464819705209784537932652570636651582617269565484188770429325008320915538746884435939616760316110032715118542848000000000000000000000) + X * (C (1222215161771177590855812514777299925507420690166397298660988814045886721015059638789295294301629508155045814461572893396320553746274350035010031364282254037183430656000000000000000000) + X * (C (-3884204547542554118124507861935385666906997554901190651860747391504434621757794352203956578404681754892623894544735864180270649264519894226057049767739048805461016903680000000000000000) + X * (C (8339691021671163287977696823722975593747874021478735959063189697964113520534437571914412763124204366907648975471547458174151189359945231812818048340439776019785384763703296000000000000) + X * (C (-12744775234017380936922848867795511270812010698281512288548411964950557017275774793678523647389344005588216661462808992234218331827894750695160442084702142093063583176193835008000000000) + X * (C (14214953888073392069665453636566968160747295609106834570433592869556007595409102549396368330658032870054659407735911662927255865412167716210440065068890558573628344808075574816768000000) + X * (C (-11659418799692129683265675422483498242043056339819338476653181119580455504585709181005584334436116338150903830901908526475298202490109738828575325820843634996771280662125844983705600000) + X * (C (6979986066045226104755662959039248673596590751550658441892275423837125368820208211307834889027024357549228648280672055743906816462722437465653172765186813001379695903840500931850880000) + X * (C (-2974382823641717471641992963649464437100131297936224999427250672093266307205204304102958442753600543979576393395153048917282469394178318161872906302966878154422155371249792846260160000) + X * (C (856402785939400373541192508027153160325405833605208072133734770161046378847763441362783256932248115369980279847780157422787365279544056277361417976681671710289657922732254517167084800) + X * (C (-149595502358947776561750639570299906403367568911939200585415931668522140809766510540774620854924956412345459598252952701224160790870590141060672732088794218337274281156817636694197360) + X * (C (11989245874946936211354334292364597480677486699274403839847962283133488323636174929215621057319905247986618773830457482289631247345140738565541456290511115941348745775939189889492729) + X * (0)))))))))))))

def b65x_regCoeff_12_0_5_0 : Fin 13 → ℚ :=
  ![(20426465516604930658945545425835306026746949518149054459433284681706368951215922432961313155105574299623238508437909445810193699543468305825300115594774839296000000000000000000000000), (11829858560077861103661544625722915256356563268337188693494206395938494762020432543953140591701407406708432776246592434183577510085680053143285277104582953009152000000000000000000000), (4196881836108639505683507555121795562044217920268779966828295408589812617033516197333172573377085853704833443383386748867122187347922435116361783177527126748102656000000000000000000), (944463667334661198962252884839275498162538535743750740676840780247461768919955103441308908738042192573109051875497506546423453809954483791903254134624691636649656320000000000000000), (157743745692866938709137161852806998439989680188794229076109484998113569698704401809963354350827017477798390097107998292909903698709971827410887505319335840692150583296000000000000), (19208582561853782766283032713073272882122128255497657299449123037719540986228892873271118293795151375895517905149181601197256439740553267291954346477133926725120952532992000000000), (1803158237917406204076627167231240069101907422940681438846601150260386607762895003560537573363570462019514856633198260510962073956105847993991940107368677277809291017760768000000), (123792642536657407175234807092192987977828696107252712277243860533194456506408819914616397400343446433409860539183568711914692106963217769658337345436417707701961644748902400000), (6433640726542790008235293936717689068273280801629359262117996536970720079833073173957146297670717450337419711330669315212803011767562987233307119402512454903111392984842880000), (217476945083125419133387274189041250766960387465941345952234151422752924782131233329590279437329747495927840835386359280468954539508512526450534095543192195845608099447360000), (4758072786937642294573017665617172025488311426778212221329884891780505059413790060071418334458794692016481661408396432960596317095564568944171042006390403042806815955884800), (2360147650474029395003422339611423132065331292461684565045988888000108651711162915351338760211712450042928421602291119256747968178722798089599511846906894063512343012240), (345657565933385137101841051325600718588350532947245917614603731949491227147331614371736313851884889168689054555533169176186864268993145910905704405721274981015500169)]

theorem b65x_regIdentity_12_0_5_0 (x : ℝ) :
    (b65x_regPoly_12_0_5.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_12_0_5_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_12_0_5, b65x_regCoeff_12_0_5_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_12_0_5_0 : ∀ i, 0 < b65x_regCoeff_12_0_5_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_12_0_5_0]

theorem b65x_regPoly_positive_12_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_12_0_5.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    12 b65x_regCoeff_12_0_5_0 b65x_regIdentity_12_0_5_0
    b65x_regCoeff_positive_12_0_5_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_12_0_5 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_12_0 5)).eval₂ (Rat.castHom ℝ) t =
      (15625000000 : ℝ) * b65x_regPoly_12_0_5.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_12_0, b65x_certP5_12_0, b65x_certP7_12_0,
    b65x_certN_12_0, b65x_certD_12_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_12_0_5,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_12_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_12_0 5)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_12_0_5]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_12_0_5 t ht)

theorem b65x_certFactors_ne_zero_12_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1))
    (j : Fin 6) : b65x_cpEval (b65x_certFactors_12_0 j) t ≠ 0 := by
  apply b65x_cpEval_ne_zero
  fin_cases j

  · exact b65x_certFactor_norm_positive_12_0_0 t ht

  · exact b65x_certFactor_norm_positive_12_0_1 t ht

  · exact b65x_certFactor_norm_positive_12_0_2 t ht

  · exact b65x_certFactor_norm_positive_12_0_3 t ht

  · exact b65x_certFactor_norm_positive_12_0_4 t ht

  · exact b65x_certFactor_norm_positive_12_0_5 t ht

theorem b65x_certND_ratio_12_0 (t : ℝ) :
    b65b_inverseNormalization (b65x_piece 12 0 t) =
      b65x_cpEval b65x_certN_12_0 t / b65x_cpEval b65x_certD_12_0 t := by
  have hQ : (1 + t ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hQc : (((1 + t ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ
  push_cast at hQc
  have hrel : b65x_cpEval b65x_certD_12_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 6).1 : ℂ) - b65x_piece 12 0 t *
          (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ))) := by
    norm_num [b65x_cpEval, b65x_certD_12_0, Polynomial.eval₂_pow,
      b65x_piece, b65x_centre, b65x_radius, b65x_et, mr_centre, mr_basePoint,
      b65b_vertex0, b65b_track, b65b_radius, b65b_boxCentre]
    push_cast
    field_simp [hQc]
    <;> ring
  have hnrel : b65x_cpEval b65x_certN_12_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 0).1 : ℂ) * ((b65b_boxCentre 6).1 : ℂ)) := by
    norm_num [b65x_cpEval, b65x_certN_12_0, Polynomial.eval₂_pow, b65b_boxCentre]
    all_goals push_cast
    all_goals ring
  unfold b65b_inverseNormalization
  rw [hnrel, hrel]
  have hLQ : (50000000000000 : ℂ) * (1) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    norm_num
  exact (mul_div_mul_left _ _ hLQ).symm

theorem b65x_piece_regular_12_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    ((b65b_boxCentre 6).1 : ℂ) - b65x_piece 12 0 t *
        (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
      b65b_inverseNormalization (b65x_piece 12 0 t) ∈ b65s_regular := by

  have h0 := b65x_certFactors_ne_zero_12_0 t ht 0

  have h1 := b65x_certFactors_ne_zero_12_0 t ht 1

  have h2 := b65x_certFactors_ne_zero_12_0 t ht 2

  have h3 := b65x_certFactors_ne_zero_12_0 t ht 3

  have h4 := b65x_certFactors_ne_zero_12_0 t ht 4

  have h5 := b65x_certFactors_ne_zero_12_0 t ht 5

  change b65x_cpEval b65x_certD_12_0 t ≠ 0 at h0
  change b65x_cpEval (b65x_cpSub b65x_certN_12_0 (b65x_cpScale 3 b65x_certD_12_0)) t ≠ 0 at h1
  change b65x_cpEval (b65x_cpSub b65x_certN_12_0 b65x_certD_12_0) t ≠ 0 at h2
  change b65x_cpEval (b65x_cpAdd b65x_certN_12_0 (b65x_cpScale 2 b65x_certD_12_0)) t ≠ 0 at h3
  change b65x_cpEval b65x_certP5_12_0 t ≠ 0 at h4
  change b65x_cpEval b65x_certP7_12_0 t ≠ 0 at h5
  norm_num only [b65x_certFactors_12_0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, b65x_certP5_12_0, b65x_certP7_12_0,
    b65x_cpEval_sub, b65x_cpEval_add, b65x_cpEval_mul, b65x_cpEval_pow,
    b65x_cpEval_scale] at h0 h1 h2 h3 h4 h5
  have hN : b65x_cpEval b65x_certN_12_0 t ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [b65x_cpEval, b65x_certN_12_0, Polynomial.eval₂_pow,
      pow_two, Complex.mul_re] at hr
    skip
  have hreg : b65b_inverseNormalization (b65x_piece 12 0 t) ∈ b65s_regular := by
    rw [b65x_certND_ratio_12_0]
    exact b65x_regular_of_homogeneous _ _ h0 hN h1 h2 h3
      (by simpa only [mul_assoc] using h4) (by simpa only [mul_assoc] using h5)
  refine ⟨?_, hreg⟩
  intro h
  apply hreg.1
  simp [b65b_inverseNormalization, h]

end HodgeLean.Foundations.Program

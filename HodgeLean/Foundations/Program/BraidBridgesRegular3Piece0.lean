import HodgeLean.Foundations.Program.BraidBridgesInterval
import HodgeLean.Foundations.Program.BraidBridgesRegular2Piece2

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

def b65x_certN_3_0 : b65x_CPoly := (C (291668908382000) + X * (0), C (0) + X * (0))
def b65x_certD_3_0 : b65x_CPoly := (C (2228834950000000) + X * (C (-2348883827751117) + X * (0)), C (-4112139000000000) + X * (C (3832930432539681) + X * (0)))

def b65x_certP5_3_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_3_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_3_0 (b65x_cpScale 3 b65x_certD_3_0)) 4))
    (b65x_cpScale (5) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_3_0 b65x_certD_3_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_3_0 (b65x_cpScale 2 b65x_certD_3_0)) 3)))

def b65x_certP7_3_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_3_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_3_0 (b65x_cpScale 3 b65x_certD_3_0)) 4))
    (b65x_cpScale (-7) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_3_0 b65x_certD_3_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_3_0 (b65x_cpScale 2 b65x_certD_3_0)) 3)))

def b65x_certFactors_3_0 : Fin 6 → b65x_CPoly :=
  ![b65x_certD_3_0,
    b65x_cpSub b65x_certN_3_0 (b65x_cpScale 3 b65x_certD_3_0),
    b65x_cpSub b65x_certN_3_0 b65x_certD_3_0,
    b65x_cpAdd b65x_certN_3_0 (b65x_cpScale 2 b65x_certD_3_0),
    b65x_certP5_3_0, b65x_certP7_3_0]

def b65x_regPoly_3_0_0 : ℚ[X] :=
  C (437547847793250050000000000000) + X * (C (-839872683388590430351926000000) + X * (C (404172218739191303155386686589) + X * (0)))

def b65x_regCoeff_3_0_0_0 : Fin 3 → ℚ :=
  ![(437547847793250050000000000000), (35223012197909669648074000000), (1847383143850922803460686589)]

theorem b65x_regIdentity_3_0_0_0 (x : ℝ) :
    (b65x_regPoly_3_0_0.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_3_0_0_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_3_0_0, b65x_regCoeff_3_0_0_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_3_0_0_0 : ∀ i, 0 < b65x_regCoeff_3_0_0_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_3_0_0_0]

theorem b65x_regPoly_positive_3_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_3_0_0.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_3_0_0_0 b65x_regIdentity_3_0_0_0
    b65x_regCoeff_positive_3_0_0_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_3_0_0 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_3_0 0)).eval₂ (Rat.castHom ℝ) t =
      (50 : ℝ) * b65x_regPoly_3_0_0.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_3_0, b65x_certP5_3_0, b65x_certP7_3_0,
    b65x_certN_3_0, b65x_certD_3_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_3_0_0,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_3_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_3_0 0)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_3_0_0]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_3_0_0 t ht)

def b65x_regPoly_3_0_1 : ℚ[X] :=
  C (3861622222361967454089158480000) + X * (C (-7476642584662557631562794476720) + X * (C (3637549968652721728398480179301) + X * (0)))

def b65x_regCoeff_3_0_1_0 : Fin 3 → ℚ :=
  ![(3861622222361967454089158480000), (246601860061377276615522483280), (22529606352131550924844182581)]

theorem b65x_regIdentity_3_0_1_0 (x : ℝ) :
    (b65x_regPoly_3_0_1.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_3_0_1_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_3_0_1, b65x_regCoeff_3_0_1_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_3_0_1_0 : ∀ i, 0 < b65x_regCoeff_3_0_1_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_3_0_1_0]

theorem b65x_regPoly_positive_3_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_3_0_1.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_3_0_1_0 b65x_regIdentity_3_0_1_0
    b65x_regCoeff_positive_3_0_1_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_3_0_1 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_3_0 1)).eval₂ (Rat.castHom ℝ) t =
      (50 : ℝ) * b65x_regPoly_3_0_1.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_3_0, b65x_certP5_3_0, b65x_certP7_3_0,
    b65x_certN_3_0, b65x_certD_3_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_3_0_1,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_3_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_3_0 1)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_3_0_1]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_3_0_1 t ht)

def b65x_regPoly_3_0_2 : ℚ[X] :=
  C (413245988562379018161158480000) + X * (C (-812468828110338349817079492240) + X * (C (404172218739191303155386686589) + X * (0)))

def b65x_regCoeff_3_0_2_0 : Fin 3 → ℚ :=
  ![(413245988562379018161158480000), (14023149014419686505237467760), (4949379191231971499465674349)]

theorem b65x_regIdentity_3_0_2_0 (x : ℝ) :
    (b65x_regPoly_3_0_2.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_3_0_2_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_3_0_2, b65x_regCoeff_3_0_2_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_3_0_2_0 : ∀ i, 0 < b65x_regCoeff_3_0_2_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_3_0_2_0]

theorem b65x_regPoly_positive_3_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_3_0_2.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_3_0_2_0 b65x_regIdentity_3_0_2_0
    b65x_regCoeff_positive_3_0_2_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_3_0_2 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_3_0 2)).eval₂ (Rat.castHom ℝ) t =
      (50 : ℝ) * b65x_regPoly_3_0_2.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_3_0, b65x_certP5_3_0, b65x_certP7_3_0,
    b65x_certN_3_0, b65x_certD_3_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_3_0_2,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_3_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_3_0 2)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_3_0_2]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_3_0_2 t ht)

def b65x_regPoly_3_0_3 : ℚ[X] :=
  C (450974838690436778567289620000) + X * (C (-853574611027716470619349253880) + X * (C (404172218739191303155386686589) + X * (0)))

def b65x_regCoeff_3_0_3_0 : Fin 3 → ℚ :=
  ![(450974838690436778567289620000), (48375066353157086515229986120), (1572446401911611103327052709)]

theorem b65x_regIdentity_3_0_3_0 (x : ℝ) :
    (b65x_regPoly_3_0_3.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_3_0_3_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_3_0_3, b65x_regCoeff_3_0_3_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_3_0_3_0 : ∀ i, 0 < b65x_regCoeff_3_0_3_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_3_0_3_0]

theorem b65x_regPoly_positive_3_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_3_0_3.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_3_0_3_0 b65x_regIdentity_3_0_3_0
    b65x_regCoeff_positive_3_0_3_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_3_0_3 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_3_0 3)).eval₂ (Rat.castHom ℝ) t =
      (200 : ℝ) * b65x_regPoly_3_0_3.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_3_0, b65x_certP5_3_0, b65x_certP7_3_0,
    b65x_certN_3_0, b65x_certD_3_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_3_0_3,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_3_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_3_0 3)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_3_0_3]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_3_0_3 t ht)

def b65x_regPoly_3_0_4 : ℚ[X] :=
  C (6416118762993705063869470375870577482545815480601635426451956522063989797879921960350039306398086859732298055682783431909147833681087263214790510465203568640000000000000000000000) + X * (C (-74393320060248162704236739333582331883830224018114653523218536037160637759407912637555357700584214399341341148108098156013399321223933865008525827276168704163840000000000000000000) + X * (C (395500040568773422436009406288731231646845877612383066599042617798361346040208741086600290170747961207364744541088547116350669539397054439869450465792087925489418240000000000000000) + X * (C (-1274807259633342990793786248377368136398378952041890278915080768764807175463059571267447656871626427713942439880395121496107477923641150188432351834435178476697330237440000000000000) + X * (C (2774696236742545853954110260869221801916132901182443302032188907203434876162466976471447097557181516181127085596867436045876609895190113444908937920543669072705099954954240000000000) + X * (C (-4296282460840670423008247687867301238307589719552703107459467754339896301167505089282782514543783473389100325530563490029474099563871117166586591203020408883421294947046195200000000) + X * (C (4852504134546759679758724033976756384121788942102192436074446918862928049588231517284628807246122032039140678063120072622389287799320274946865498317489452538341397853576110182400000) + X * (C (-4028230081436233510986059357281999840180893392774302039678397885229200072450014461747996161273350299106789393193268558608160686669223758362108274279448329371469065204201630471680000) + X * (C (2439260973400529870046030158768994565540521163411890780328780790740826343868093237814551264308484306366512838849080636923045123737366567774555565284678505399225295629015403140256000) + X * (C (-1050772275288558157742599495382866844847977204307101700813212620562486011989792026607408017311852032888323749727068870868189798355518337065895694482205479849679575572056989972259200) + X * (C (305655116648176327996740799890571235880894246361063353005325166972541070952981500340813880026425445546105716001295327306524069459761844351750475791285445419884903339054122615147040) + X * (C (-53906342668703897055964986347857162875037259408124878659980916963071905178957065639802297738767879510384386536934570127382932908038103067021122377913799465060182936415826062963640) + X * (C (4359119257978283054981334627917502966547874898478791647095963881551870646072612200491751451146911698985676916980616609781297749607428651590442445505027483108306425197459569471961) + X * (0)))))))))))))

def b65x_regCoeff_3_0_4_0 : Fin 13 → ℚ :=
  ![(6416118762993705063869470375870577482545815480601635426451956522063989797879921960350039306398086859732298055682783431909147833681087263214790510465203568640000000000000000000000), (2600105095676298062196905176864597906719561749104971594204942227607239815151150886645113976192827917446235520085303026896374682949113293568960298306274119516160000000000000000000), (637358263628166904790318426783694772737235132829815989467851845817657346796551456593949686595335556941663586963173906207034028885541296951840056457667709927178240000000000000000), (106670599357398884570633854442972619496908817994237117756362029048963705175475810019218711300501537036814634757306106674778212852229542047144625641207149985652162560000000000000), (13703378200106846783154480665091466978525271560493516039821536600588452579969138066679466859540763224879147437565869506727525476319108057583550978949719219348617994240000000000), (1394961280150555954769756295908813648464543420854828082636769555375603422109456676528499366644367095349705869365027373227345737853406754863304018623584658604944747724800000000), (116866490423958025035367869621536954473130284904006271378810822331906195128038988757123097302859371992761819083467090237520937633359004164863610952800003142418011463782400000), (7758862360907808064827978592050034180758795203603588327330719334521457777593905570187027930811513281567546699880990206835287245672467162240130221576873432069282371422720000), (416694668757814948559263711664642307741932220155721709331660565395783764915568972110252060854754529426652298632555001871707268948707677338767241178259631594388871517856000), (15190557392219163328384889964520430224132423434779017145493466141861400373867296365085329979641312643635418294520089832953128569787274260817963881020035159371129519964800), (338115633758785180252277794110659975206227506383314745905830578849893043909167076980983907922876683021512461224571716423936149696220643884368397672603261509540359105440), (138326881791025908255458571664687305520438802623493980156092143082207763210206605097381316970680478419592804557110532758147119030521205092235462845915382124147576840), (19570950207087745061570068946816706063973840085085443047198379975891124626541932891087402007776710770547811272807971157702600731460026656903132544636693800372161)]

theorem b65x_regIdentity_3_0_4_0 (x : ℝ) :
    (b65x_regPoly_3_0_4.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_3_0_4_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_3_0_4, b65x_regCoeff_3_0_4_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_3_0_4_0 : ∀ i, 0 < b65x_regCoeff_3_0_4_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_3_0_4_0]

theorem b65x_regPoly_positive_3_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_3_0_4.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    12 b65x_regCoeff_3_0_4_0 b65x_regIdentity_3_0_4_0
    b65x_regCoeff_positive_3_0_4_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_3_0_4 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_3_0 4)).eval₂ (Rat.castHom ℝ) t =
      (25000000000000 : ℝ) * b65x_regPoly_3_0_4.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_3_0, b65x_certP5_3_0, b65x_certP7_3_0,
    b65x_certN_3_0, b65x_certD_3_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_3_0_4,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_3_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_3_0 4)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_3_0_4]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_3_0_4 t ht)

def b65x_regPoly_3_0_5 : ℚ[X] :=
  C (319163523696952041546024147278676656667921086221078975928645073151662014862748788015020518048524598431613101694342335090784276555366692278520314306168356864000000000000000000000000) + X * (C (-3690547291684045359602117618859749241382411560156806731267887134019291855058100796396874920121161671947231080292353777165040182938169367653305409359329646936064000000000000000000000) + X * (C (19572771977242480055871214198777107839981643610200076789152741115784933081608005573213467081546978268071683051787379933156336750268749348241480253611414412936226816000000000000000000) + X * (C (-62954570153394057620617615558313878137369352963637623210419076274362813340853335553176311414525079169908943872171637819869655730419423375723771628046928674605622261760000000000000000) + X * (C (136772258905857191772377572140936418077923387836302414403694585789032116626609271353654457587389377299319935698542853632389861786357342973072576670256690875517703935591424000000000000) + X * (C (-211442888342383462827659336315540169275380951942644501849491590439229393445966268398614297569815103215784589570393750032632361292885982743843787545795126701697452714716360704000000000) + X * (C (238504520540001470076554965729457961359177578099576354235819930109848939548159964223051388510124220655496654116985962337880678158005786734474075737947112292170664247201490016768000000) + X * (C (-197780325962941223151203994878043512692103676519399485064404830570206247257407381884701055993409982662681522816021201736828309763857889038689317140517433421152455882908441218649600000) + X * (C (119665176537594344090498130521038553409849064423846114787169571335722568126330577731166070882250788009678613227140585131133391703169029948705467000122863622333378643598802105637280000) + X * (C (-51517680529070716542584755100991021082287734204738447596664723183665112329271485656663909297824850917965842506147382828440004697862279539889615176985131916270396491664046612486960000) + X * (C (14979934742206690115195488404255505717188066517473767115740784291046006114932469420942757322567273424379511026014949952526015041460952730292000694338301503658158887017539171544032800) + X * (C (-2641410790766490955742284331045000980876825710998119054339064931190523353768896216350312589199626096008834940309793936241763712493867050284034996517776173787948963884375477085218360) + X * (C (213596843640935869694085396767957645360845870025460790707702230196041661657557997824095821106198673250298168932050213879283589730764003927931679829746346672307014834675518904126089) + X * (0)))))))))))))

def b65x_regCoeff_3_0_5_0 : Fin 13 → ℚ :=
  ![(319163523696952041546024147278676656667921086221078975928645073151662014862748788015020518048524598431613101694342335090784276555366692278520314306168356864000000000000000000000000), (139414992679379138950172148484370638632641474496140979875853743800652323294884659783371296461133509232126140039754243924371135726230939688938362314690635431936000000000000000000000), (41544332716815842285514111712525524857908139066415156496557469582415656910316821839197151416823373138605880398082500332656990603087994437461494865899849663522816000000000000000000), (9023789737697300103369793479856453357086298376149165676458605791108716835909740434752764956223208665059602378017487589042552849427187033702540661123383353125898240000000000000000), (1507603346051931956216852167687863296203876128243447274183626978326503763520831624468140305687185720535269891292883304700684784820277497406467611926289426750299751424000000000000), (199163636651949425094986899165625304362716177920120391427599908232691272268598817728646482587445906202879698092417377223397377970262655981481845252716375875266655031296000000000), (20981093301762934878484016446712970225989820484552004618071724942173793979433616791853939885059854629166866695483786022346739886153039417481912852802393998812906837088768000000), (1762428391830422979240590405972826595962187973561498347678160793108531559809475154513156640164492438629670687212481253618876063083918680942480729436663627634616668097958400000), (117018348012874480969205447635329991420468919504408290720472669693571010388822516429533768296244416659988644705088747096871636994710218799339874501037599791646001623909280000), (5964101501976303884758197442616036949769016567282063294809375392974677011792837566053881493234663813125694954573881755753579881712215889314856325636807507883669318926160000), (220943048332104237600898712828437016934502534483078359349051067581131955554327252396232269562578273925152824212068423845535672647906165910318706600134636712447248930832800), (5322613684590086720578624600672799677266576790307580701748807750976983308876675561813482502932724681917606869139694176679740581700280691212537554826264097372530451087240), (67564327376735718849296747554542070283591626787412108885591835126581964495938137557194331343605762003404879215925090381314908220453190570875702499229310706800631660529)]

theorem b65x_regIdentity_3_0_5_0 (x : ℝ) :
    (b65x_regPoly_3_0_5.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_3_0_5_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_3_0_5, b65x_regCoeff_3_0_5_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_3_0_5_0 : ∀ i, 0 < b65x_regCoeff_3_0_5_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_3_0_5_0]

theorem b65x_regPoly_positive_3_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_3_0_5.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    12 b65x_regCoeff_3_0_5_0 b65x_regIdentity_3_0_5_0
    b65x_regCoeff_positive_3_0_5_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_3_0_5 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_3_0 5)).eval₂ (Rat.castHom ℝ) t =
      (1000000000000 : ℝ) * b65x_regPoly_3_0_5.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_3_0, b65x_certP5_3_0, b65x_certP7_3_0,
    b65x_certN_3_0, b65x_certD_3_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_3_0_5,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_3_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_3_0 5)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_3_0_5]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_3_0_5 t ht)

theorem b65x_certFactors_ne_zero_3_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1))
    (j : Fin 6) : b65x_cpEval (b65x_certFactors_3_0 j) t ≠ 0 := by
  apply b65x_cpEval_ne_zero
  fin_cases j

  · exact b65x_certFactor_norm_positive_3_0_0 t ht

  · exact b65x_certFactor_norm_positive_3_0_1 t ht

  · exact b65x_certFactor_norm_positive_3_0_2 t ht

  · exact b65x_certFactor_norm_positive_3_0_3 t ht

  · exact b65x_certFactor_norm_positive_3_0_4 t ht

  · exact b65x_certFactor_norm_positive_3_0_5 t ht

theorem b65x_certND_ratio_3_0 (t : ℝ) :
    b65b_inverseNormalization (b65x_piece 3 0 t) =
      b65x_cpEval b65x_certN_3_0 t / b65x_cpEval b65x_certD_3_0 t := by
  have hQ : (1 + t ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hQc : (((1 + t ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ
  push_cast at hQc
  have hrel : b65x_cpEval b65x_certD_3_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 6).1 : ℂ) - b65x_piece 3 0 t *
          (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ))) := by
    norm_num [b65x_cpEval, b65x_certD_3_0, Polynomial.eval₂_pow,
      b65x_piece, b65x_centre, b65x_radius, b65x_et, mr_centre, mr_basePoint,
      b65b_vertex0, b65b_track, b65b_radius, b65b_boxCentre]
    push_cast
    field_simp [hQc]
    <;> ring
  have hnrel : b65x_cpEval b65x_certN_3_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 0).1 : ℂ) * ((b65b_boxCentre 6).1 : ℂ)) := by
    norm_num [b65x_cpEval, b65x_certN_3_0, Polynomial.eval₂_pow, b65b_boxCentre]
    all_goals push_cast
    all_goals ring
  unfold b65b_inverseNormalization
  rw [hnrel, hrel]
  have hLQ : (50000000000000 : ℂ) * (1) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    norm_num
  exact (mul_div_mul_left _ _ hLQ).symm

theorem b65x_piece_regular_3_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    ((b65b_boxCentre 6).1 : ℂ) - b65x_piece 3 0 t *
        (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
      b65b_inverseNormalization (b65x_piece 3 0 t) ∈ b65s_regular := by

  have h0 := b65x_certFactors_ne_zero_3_0 t ht 0

  have h1 := b65x_certFactors_ne_zero_3_0 t ht 1

  have h2 := b65x_certFactors_ne_zero_3_0 t ht 2

  have h3 := b65x_certFactors_ne_zero_3_0 t ht 3

  have h4 := b65x_certFactors_ne_zero_3_0 t ht 4

  have h5 := b65x_certFactors_ne_zero_3_0 t ht 5

  change b65x_cpEval b65x_certD_3_0 t ≠ 0 at h0
  change b65x_cpEval (b65x_cpSub b65x_certN_3_0 (b65x_cpScale 3 b65x_certD_3_0)) t ≠ 0 at h1
  change b65x_cpEval (b65x_cpSub b65x_certN_3_0 b65x_certD_3_0) t ≠ 0 at h2
  change b65x_cpEval (b65x_cpAdd b65x_certN_3_0 (b65x_cpScale 2 b65x_certD_3_0)) t ≠ 0 at h3
  change b65x_cpEval b65x_certP5_3_0 t ≠ 0 at h4
  change b65x_cpEval b65x_certP7_3_0 t ≠ 0 at h5
  norm_num only [b65x_certFactors_3_0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, b65x_certP5_3_0, b65x_certP7_3_0,
    b65x_cpEval_sub, b65x_cpEval_add, b65x_cpEval_mul, b65x_cpEval_pow,
    b65x_cpEval_scale] at h0 h1 h2 h3 h4 h5
  have hN : b65x_cpEval b65x_certN_3_0 t ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [b65x_cpEval, b65x_certN_3_0, Polynomial.eval₂_pow,
      pow_two, Complex.mul_re] at hr
    skip
  have hreg : b65b_inverseNormalization (b65x_piece 3 0 t) ∈ b65s_regular := by
    rw [b65x_certND_ratio_3_0]
    exact b65x_regular_of_homogeneous _ _ h0 hN h1 h2 h3
      (by simpa only [mul_assoc] using h4) (by simpa only [mul_assoc] using h5)
  refine ⟨?_, hreg⟩
  intro h
  apply hreg.1
  simp [b65b_inverseNormalization, h]

end HodgeLean.Foundations.Program

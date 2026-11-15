import HodgeLean.Foundations.Program.BraidBridgesInterval
import HodgeLean.Foundations.Program.BraidBridgesRegular6Piece2

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

def b65x_certN_7_0 : b65x_CPoly := (C (291668908382000) + X * (0), C (0) + X * (0))
def b65x_certD_7_0 : b65x_CPoly := (C (2228834950000000) + X * (C (-1977615245997117) + X * (0)), C (-4112139000000000) + X * (C (3924084332892573) + X * (0)))

def b65x_certP5_7_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_7_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_7_0 (b65x_cpScale 3 b65x_certD_7_0)) 4))
    (b65x_cpScale (5) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_7_0 b65x_certD_7_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_7_0 (b65x_cpScale 2 b65x_certD_7_0)) 3)))

def b65x_certP7_7_0 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_7_0 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_7_0 (b65x_cpScale 3 b65x_certD_7_0)) 4))
    (b65x_cpScale (-7) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_7_0 b65x_certD_7_0) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_7_0 (b65x_cpScale 2 b65x_certD_7_0)) 3)))

def b65x_certFactors_7_0 : Fin 6 → b65x_CPoly :=
  ![b65x_certD_7_0,
    b65x_cpSub b65x_certN_7_0 (b65x_cpScale 3 b65x_certD_7_0),
    b65x_cpSub b65x_certN_7_0 b65x_certD_7_0,
    b65x_cpAdd b65x_certN_7_0 (b65x_cpScale 2 b65x_certD_7_0),
    b65x_certP5_7_0, b65x_certP7_7_0]

def b65x_regPoly_7_0_0 : ℚ[X] :=
  C (10938696194831251250000000000000) + X * (C (-20544158202507754212486150000000) + X * (C (9654699956426593630110365436009) + X * (0)))

def b65x_regCoeff_7_0_0_0 : Fin 3 → ℚ :=
  ![(10938696194831251250000000000000), (1333234187154748287513850000000), (49237948750090667624215436009)]

theorem b65x_regIdentity_7_0_0_0 (x : ℝ) :
    (b65x_regPoly_7_0_0.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_7_0_0_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_7_0_0, b65x_regCoeff_7_0_0_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_7_0_0_0 : ∀ i, 0 < b65x_regCoeff_7_0_0_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_7_0_0_0]

theorem b65x_regPoly_positive_7_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_7_0_0.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_7_0_0_0 b65x_regIdentity_7_0_0_0
    b65x_regCoeff_positive_7_0_0_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_7_0_0 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_7_0 0)).eval₂ (Rat.castHom ℝ) t =
      (2 : ℝ) * b65x_regPoly_7_0_0.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_7_0, b65x_certP5_7_0, b65x_certP7_7_0,
    b65x_certN_7_0, b65x_certD_7_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_7_0_0,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_7_0_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_7_0 0)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_7_0_0]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_7_0_0 t ht)

def b65x_regPoly_7_0_1 : ℚ[X] :=
  C (96540555559049186352228962000000) + X * (C (-183166997182571049380847945918000) + X * (C (86892299607839342670993288924081) + X * (0)))

def b65x_regCoeff_7_0_1_0 : Fin 3 → ℚ :=
  ![(96540555559049186352228962000000), (9914113935527323323609978082000), (265857984317479642374305006081)]

theorem b65x_regIdentity_7_0_1_0 (x : ℝ) :
    (b65x_regPoly_7_0_1.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_7_0_1_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_7_0_1, b65x_regCoeff_7_0_1_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_7_0_1_0 : ∀ i, 0 < b65x_regCoeff_7_0_1_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_7_0_1_0]

theorem b65x_regPoly_positive_7_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_7_0_1.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_7_0_1_0 b65x_regIdentity_7_0_1_0
    b65x_regCoeff_positive_7_0_1_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_7_0_1 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_7_0 1)).eval₂ (Rat.castHom ℝ) t =
      (2 : ℝ) * b65x_regPoly_7_0_1.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_7_0, b65x_certP5_7_0, b65x_certP7_7_0,
    b65x_certN_7_0, b65x_certD_7_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_7_0_1,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_7_0_1 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_7_0 1)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_7_0_1]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_7_0_1 t ht)

def b65x_regPoly_7_0_2 : ℚ[X] :=
  C (10331149714059475454028962000000) + X * (C (-19967349322508174701977015306000) + X * (C (9654699956426593630110365436009) + X * (0)))

def b65x_regCoeff_7_0_2_0 : Fin 3 → ℚ :=
  ![(10331149714059475454028962000000), (694950105610776206080908694000), (18500347977894382162312130009)]

theorem b65x_regIdentity_7_0_2_0 (x : ℝ) :
    (b65x_regPoly_7_0_2.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_7_0_2_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_7_0_2, b65x_regCoeff_7_0_2_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_7_0_2_0 : ∀ i, 0 < b65x_regCoeff_7_0_2_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_7_0_2_0]

theorem b65x_regPoly_positive_7_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_7_0_2.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_7_0_2_0 b65x_regIdentity_7_0_2_0
    b65x_regCoeff_positive_7_0_2_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_7_0_2 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_7_0 2)).eval₂ (Rat.castHom ℝ) t =
      (2 : ℝ) * b65x_regPoly_7_0_2.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_7_0, b65x_certP5_7_0, b65x_certP7_7_0,
    b65x_certN_7_0, b65x_certD_7_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_7_0_2,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_7_0_2 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_7_0 2)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_7_0_2]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_7_0_2 t ht)

def b65x_regPoly_7_0_3 : ℚ[X] :=
  C (11274370967260919464182240500000) + X * (C (-20832562642507543967740717347000) + X * (C (9654699956426593630110365436009) + X * (0)))

def b65x_regCoeff_7_0_3_0 : Fin 3 → ℚ :=
  ![(11274370967260919464182240500000), (1716179292014294960623763653000), (96508281179969126551888589009)]

theorem b65x_regIdentity_7_0_3_0 (x : ℝ) :
    (b65x_regPoly_7_0_3.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 2 b65x_regCoeff_7_0_3_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_7_0_3, b65x_regCoeff_7_0_3_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_7_0_3_0 : ∀ i, 0 < b65x_regCoeff_7_0_3_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_7_0_3_0]

theorem b65x_regPoly_positive_7_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_7_0_3.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    2 b65x_regCoeff_7_0_3_0 b65x_regIdentity_7_0_3_0
    b65x_regCoeff_positive_7_0_3_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_7_0_3 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_7_0 3)).eval₂ (Rat.castHom ℝ) t =
      (8 : ℝ) * b65x_regPoly_7_0_3.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_7_0, b65x_certP5_7_0, b65x_certP7_7_0,
    b65x_certN_7_0, b65x_certD_7_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_7_0_3,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_7_0_3 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_7_0 3)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_7_0_3]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_7_0_3 t ht)

def b65x_regPoly_7_0_4 : ℚ[X] :=
  C (1566435244871510025358757415984027705699661982568758649036122197769528759248027822351083815038595424739330580000679548805944295332296695120798464469043840000000000000000000000000000000000) + X * (C (-17790727106348897721389474276798387974148701508300814791497155968803096207860088738002411088605137530784941588880117003303967576362139869693455777338153395040000000000000000000000000000000) + X * (C (92611235831415761268672652078927805435595885949620858406227683083665280003460669911976278736746606536645410349434718775491608975835088321900412566376235260032020000000000000000000000000000) + X * (C (-292183912728506845670987554498644278014518021994939817138543667268909017613943876297542121201795599180811854748671160110289279123845258606874125407422473378721652300000000000000000000000000) + X * (C (622240909911817747222926730712158681382165876898167525906020365611359320474071468706407622757195619093911387621403270659759963192127410954487792953332716966599349430090000000000000000000000) + X * (C (-942330877614705044553104521498018287374344543241681559016538021034770351036944231363792828924967627259540353780821025696511636241119088701835228379927355339433342894956000000000000000000000) + X * (C (1040589607480885273778670194950854089314814230407276470569898143984142734980252798916211748815568488413132167328284578112755956454885138621623207593225348935999501192045259405000000000000000) + X * (C (-844239384682615058863396223444369872957010346536021645548763713908596273071396049504120697500325760571125633428532316687045235181022770981633104696253056276189365051117580031155000000000000) + X * (C (499437812025092264002551395249052028655322668039222098105625689552098723909391908973084210144081074034632635428983792809847648202455414584354101538177205698120737500413302706223502500000000) + X * (C (-210105201337388631105188536940904895319695803203450406033545995265570662472994847507607231167551487078887199947266099471902187276959912103871964800737141351926969762341424511250782550000000) + X * (C (59661929352609544870558773450072408641545131522260078062495133855599179962204861148478732266604957618302364067514486149993666228408500403240213376622336382461249717952042344389832648500000) + X * (C (-10267728783481511033215549136043208067673975869458161501056421061050395122654236129616749215521289951443039047094858005471111334771577515995333169742345778098719136746229576270539100991000) + X * (C (809902406353887778775966777921651111156124263527708742675074208925899397322110394210091352215844680912606963091381420333671927837985246056343487932018392037461762762123902231789622715441) + X * (0)))))))))))))

def b65x_regCoeff_7_0_4_0 : Fin 13 → ℚ :=
  ![(1566435244871510025358757415984027705699661982568758649036122197769528759248027822351083815038595424739330580000679548805944295332296695120798464469043840000000000000000000000000000000000), (1006495832109222582915614715009944494247242282524288996936310404431248903116245130210594691858007566087025371128037582367363967625420471756125796290372684960000000000000000000000000000000), (297963823097548007066424489091366296137860207849966536143032479620119827369530069121288554637391730806871151798281960340289127783131633245097670613441354592020000000000000000000000000000), (54208608193597918244512583208533017187890709850856179336468792869818022924063149326495600878895435123188957419093200216338907693204705565594685931087294398547700000000000000000000000000), (6781432794731797629749016471122440115479178548890615222851999521623635165858360849733918889563282101435543042245678066631079832843563514266424842433877945378730090000000000000000000000), (612066581533341084973835275718876900786535516208833922163143658207799537112774367960548420730614492313200509220234145679641354313251480085882565670880024369745764000000000000000000000), (40239666230356744099582275300660456757768188466530538483992176697664916086565843259468318106969707360612756317869651419276719375549336128381741217070373291769873259405000000000000000), (1885638970640602129322379424270253415431225664538263966749755382390531575584986691180613054339614162965423873964615235173732246850942730392092217921931859592117976398845000000000000), (59570348982719579024767436740163222571363132683004526227516098751915113459143628000757205866052117198706462396672815441215971469350876385488748463549899108344293625448502500000000), (1132994397124423508901753898388458252328658758162309667137435892268681084291349893378440858546486997603723707652578710864787814539391007177612657672527130621174102093227450000000), (9840175120018254433274683078049777648506274432305288373004219391081318350688444084280733774902104653484226977059187540818775767083575245432510446633251354675811428499998500000), (2686123617880517265396425300719985429651114267204059952412464425810304227723044454742089112533229472073648332622117566392873637399125717241722727386498448677875788546009000), (232610840191762538908186708791094412033237985860871960158516332037728788684284229682879797447330502465042542801087046879657748714379955840270458101494239168803120224441)]

theorem b65x_regIdentity_7_0_4_0 (x : ℝ) :
    (b65x_regPoly_7_0_4.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_7_0_4_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_7_0_4, b65x_regCoeff_7_0_4_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_7_0_4_0 : ∀ i, 0 < b65x_regCoeff_7_0_4_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_7_0_4_0]

theorem b65x_regPoly_positive_7_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_7_0_4.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    12 b65x_regCoeff_7_0_4_0 b65x_regIdentity_7_0_4_0
    b65x_regCoeff_positive_7_0_4_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_7_0_4 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_7_0 4)).eval₂ (Rat.castHom ℝ) t =
      (102400 : ℝ) * b65x_regPoly_7_0_4.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_7_0, b65x_certP5_7_0, b65x_certP7_7_0,
    b65x_certN_7_0, b65x_certD_7_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_7_0_4,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_7_0_4 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_7_0 4)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_7_0_4]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_7_0_4 t ht)

def b65x_regPoly_7_0_5 : ℚ[X] :=
  C (77920782152576182018072301581708168131816671440693109357579363562417484097350778323979618664190575788968042405845296653023505018400071357060623609904384000000000000000000000000000000000000) + X * (C (-882846564744310313624999277332418028308386773093110914394928057607915673577990819600949742164402543786348934259986643438742123877968519309748860519395381584000000000000000000000000000000000) + X * (C (4585540823638497701130103865640867708726374381083050403551503510559544291772368213167528493605839030136981419896851106656960738395088420677348972912122310278684500000000000000000000000000000) + X * (C (-14437935929654576549054267731280561693207651617655807234753561884512830336827508505039536197040493964502050586643494198479682313303983526372620979258062383312370845500000000000000000000000000) + X * (C (30691481599000348635517512807127944148639547113517524503701270177560716552546398408096469580849013637574055781464675621866710506680766864410980731639741297170150718480250000000000000000000000) + X * (C (-46404898302054910127772647279481457064185140256720424034641499065814013324918947145871723845935425729380375243074597383245577789618717575815001551334709985438175205223573000000000000000000000) + X * (C (51172162946530988673678279236501995348865334763522324771609283380452519863525537909784006293852510716702065116926946514798125644914679795034122631592197055817780128043359892125000000000000000) + X * (C (-41467589589564263310499911760904935525258640877296755246249947102374445251068163895924429881831946887185017123757628621237986541735046089179417438788778450123225942457899737591375000000000000) + X * (C (24508165776513957658658706883589332237898307592102420371019068433455582910268274777959646277493298168662162160253291445923134280573812992232680656004185405672165088444131560301026562500000000) + X * (C (-10302724749107319487084419354714045993250792064004811295317772784569276020258692340401253808587120626232728197998193124026706955865812497123787364945360471129384745702484758584010102750000000) + X * (C (2924156699768265293532446172010482424106325714021470819070128267511342987617979685522304367934778780266832626790993135576736866344123507974045407004409895920629879694663474174101262624500000) + X * (C (-503118710390594040627561907666117195316024817603449913551764631991469361010057570351220711560543207620708913307648042268084455403807298283771325317374943126837237700565249237256415948559000) + X * (C (39685217911340501160022372118160904446650088912857728391078636237369070468783409316294476258576389364717741191477689596349924464061277056760830908668901209835626375344071209357691513056609) + X * (0)))))))))))))

def b65x_regCoeff_7_0_5_0 : Fin 13 → ℚ :=
  ![(77920782152576182018072301581708168131816671440693109357579363562417484097350778323979618664190575788968042405845296653023505018400071357060623609904384000000000000000000000000000000000000), (52202821086603870591868341648079989273413284195206397896024305141094135590218520286805681805884365681267574610156916397539936342832336974978622799457226416000000000000000000000000000000000), (17000233521112264447883719377008494034020192144575562807532871992025832839620566939736161633989050559033941822787607930348706951839417836112665452462456854684500000000000000000000000000000), (3483319360093256847717019820920826094487390006080567707890036379097035523849779859029026097683102191541557311716742624279361406647816918018615475379212354474154500000000000000000000000000), (499278555564595704685702538504356822964506132315807575526650215305138675541491492629801395239604011371235027153310966987458967123693174542400565115928539615608980250000000000000000000000), (52958220779988089782061360920035251872806079100830897452710177617106710965481858592007885680840943561556733031859664546687137866013915255725591448031399820104618427000000000000000000000), (4274365493980472569770650486939896471531506010255217463126697757151999034172961417507659732573420112751588126808710273455459291107599736967621412962991367786925348892125000000000000000), (263881826404836924713444939880666415489998351139981583280612666347826260213064400307838097663017043089501195793539311462094666277354944870983574561171983218001226615158625000000000000), (12270699884696683750178717374729647064690750309087494475803008093278180338596046482457730952690581436642024076763116767662412795911955494542309322342173874597476254219151562500000000), (414172943959937755411474896235494177117768043648913620961988031300843909666307610216378233531958084345332377003738338899608012611569878394364471717915774431186949206346147250000000), (9500444390113357205324143106798249943512281603709746587934386256166085433061827329251055221150477767479157001606010389411243705022599514660399337901539075366566189480329374500000), (131203275092664918208386041104897774475684916801887818159552360305024676557210576107556749682171449037677573851480688394017411554540660520685150966396105483329356147051050441000), (817031336327190955441287719918225983067790438242469543192635332904981114921538274339788553889888532798374261286585597422658652333507547635355251964453226252396843997938997609)]

theorem b65x_regIdentity_7_0_5_0 (x : ℝ) :
    (b65x_regPoly_7_0_5.comp (C (0) + C ((1) - (0)) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion 12 b65x_regCoeff_7_0_5_0).eval₂ (Rat.castHom ℝ) x := by
  norm_num [b65x_regPoly_7_0_5, b65x_regCoeff_7_0_5_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Rat.coe_castHom]
  ring

theorem b65x_regCoeff_positive_7_0_5_0 : ∀ i, 0 < b65x_regCoeff_7_0_5_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_7_0_5_0]

theorem b65x_regPoly_positive_7_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < b65x_regPoly_7_0_5.eval₂ (Rat.castHom ℝ) t := by

  exact b65x_bernstein_interval_eval_pos _ (0) (1) (by norm_num)
    12 b65x_regCoeff_7_0_5_0 b65x_regIdentity_7_0_5_0
    b65x_regCoeff_positive_7_0_5_0 t (by push_cast at *; constructor <;> linarith [ht.1, ht.2])

theorem b65x_certFactor_norm_7_0_5 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_7_0 5)).eval₂ (Rat.castHom ℝ) t =
      (4096 : ℝ) * b65x_regPoly_7_0_5.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_7_0, b65x_certP5_7_0, b65x_certP7_7_0,
    b65x_certN_7_0, b65x_certD_7_0, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_7_0_5,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_7_0_5 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    0 < (b65x_cpNorm (b65x_certFactors_7_0 5)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_7_0_5]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_7_0_5 t ht)

theorem b65x_certFactors_ne_zero_7_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1))
    (j : Fin 6) : b65x_cpEval (b65x_certFactors_7_0 j) t ≠ 0 := by
  apply b65x_cpEval_ne_zero
  fin_cases j

  · exact b65x_certFactor_norm_positive_7_0_0 t ht

  · exact b65x_certFactor_norm_positive_7_0_1 t ht

  · exact b65x_certFactor_norm_positive_7_0_2 t ht

  · exact b65x_certFactor_norm_positive_7_0_3 t ht

  · exact b65x_certFactor_norm_positive_7_0_4 t ht

  · exact b65x_certFactor_norm_positive_7_0_5 t ht

theorem b65x_certND_ratio_7_0 (t : ℝ) :
    b65b_inverseNormalization (b65x_piece 7 0 t) =
      b65x_cpEval b65x_certN_7_0 t / b65x_cpEval b65x_certD_7_0 t := by
  have hQ : (1 + t ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hQc : (((1 + t ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ
  push_cast at hQc
  have hrel : b65x_cpEval b65x_certD_7_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 6).1 : ℂ) - b65x_piece 7 0 t *
          (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ))) := by
    norm_num [b65x_cpEval, b65x_certD_7_0, Polynomial.eval₂_pow,
      b65x_piece, b65x_centre, b65x_radius, b65x_et, mr_centre, mr_basePoint,
      b65b_vertex0, b65b_track, b65b_radius, b65b_boxCentre]
    push_cast
    field_simp [hQc]
    <;> ring
  have hnrel : b65x_cpEval b65x_certN_7_0 t =
      (50000000000000 : ℂ) * (1) *
        (((b65b_boxCentre 0).1 : ℂ) * ((b65b_boxCentre 6).1 : ℂ)) := by
    norm_num [b65x_cpEval, b65x_certN_7_0, Polynomial.eval₂_pow, b65b_boxCentre]
    all_goals push_cast
    all_goals ring
  unfold b65b_inverseNormalization
  rw [hnrel, hrel]
  have hLQ : (50000000000000 : ℂ) * (1) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    norm_num
  exact (mul_div_mul_left _ _ hLQ).symm

theorem b65x_piece_regular_7_0 (t : ℝ) (ht : t ∈ Set.Icc (0) (1)) :
    ((b65b_boxCentre 6).1 : ℂ) - b65x_piece 7 0 t *
        (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
      b65b_inverseNormalization (b65x_piece 7 0 t) ∈ b65s_regular := by

  have h0 := b65x_certFactors_ne_zero_7_0 t ht 0

  have h1 := b65x_certFactors_ne_zero_7_0 t ht 1

  have h2 := b65x_certFactors_ne_zero_7_0 t ht 2

  have h3 := b65x_certFactors_ne_zero_7_0 t ht 3

  have h4 := b65x_certFactors_ne_zero_7_0 t ht 4

  have h5 := b65x_certFactors_ne_zero_7_0 t ht 5

  change b65x_cpEval b65x_certD_7_0 t ≠ 0 at h0
  change b65x_cpEval (b65x_cpSub b65x_certN_7_0 (b65x_cpScale 3 b65x_certD_7_0)) t ≠ 0 at h1
  change b65x_cpEval (b65x_cpSub b65x_certN_7_0 b65x_certD_7_0) t ≠ 0 at h2
  change b65x_cpEval (b65x_cpAdd b65x_certN_7_0 (b65x_cpScale 2 b65x_certD_7_0)) t ≠ 0 at h3
  change b65x_cpEval b65x_certP5_7_0 t ≠ 0 at h4
  change b65x_cpEval b65x_certP7_7_0 t ≠ 0 at h5
  norm_num only [b65x_certFactors_7_0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, b65x_certP5_7_0, b65x_certP7_7_0,
    b65x_cpEval_sub, b65x_cpEval_add, b65x_cpEval_mul, b65x_cpEval_pow,
    b65x_cpEval_scale] at h0 h1 h2 h3 h4 h5
  have hN : b65x_cpEval b65x_certN_7_0 t ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [b65x_cpEval, b65x_certN_7_0, Polynomial.eval₂_pow,
      pow_two, Complex.mul_re] at hr
    skip
  have hreg : b65b_inverseNormalization (b65x_piece 7 0 t) ∈ b65s_regular := by
    rw [b65x_certND_ratio_7_0]
    exact b65x_regular_of_homogeneous _ _ h0 hN h1 h2 h3
      (by simpa only [mul_assoc] using h4) (by simpa only [mul_assoc] using h5)
  refine ⟨?_, hreg⟩
  intro h
  apply hreg.1
  simp [b65b_inverseNormalization, h]

end HodgeLean.Foundations.Program

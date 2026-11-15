import HodgeLean.Foundations.Program.BraidBridgesCertificateData

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

def b65x_certP7_0_1 : b65x_CPoly :=
  b65x_cpSub
    (b65x_cpMul (b65x_cpPow b65x_certN_0_1 2)
      (b65x_cpPow (b65x_cpSub b65x_certN_0_1 (b65x_cpScale 3 b65x_certD_0_1)) 4))
    (b65x_cpScale (-7) (b65x_cpMul
      (b65x_cpPow (b65x_cpSub b65x_certN_0_1 b65x_certD_0_1) 3)
      (b65x_cpPow (b65x_cpAdd b65x_certN_0_1 (b65x_cpScale 2 b65x_certD_0_1)) 3)))

def b65x_certFactors_0_1 : Fin 6 → b65x_CPoly :=
  ![b65x_certD_0_1,
    b65x_cpSub b65x_certN_0_1 (b65x_cpScale 3 b65x_certD_0_1),
    b65x_cpSub b65x_certN_0_1 b65x_certD_0_1,
    b65x_cpAdd b65x_certN_0_1 (b65x_cpScale 2 b65x_certD_0_1),
    b65x_certP5_0_1, b65x_certP7_0_1]

def b65x_regPoly_0_1_0 : ℚ[X] :=
  C (16083180253831441) + X * (C (0) + X * (C (17501913911730002) + X * (C (0) + X * (C (1418733657898561) + X * (0)))))

def b65x_regCoeff_0_1_0_0 : Fin 5 → ℚ :=
  ![35003827823460004, 58657786383731520, 70007655646920008, 58657786383731520, 35003827823460004]

theorem b65x_regIdentity_0_1_0_0 :
    b65x_regPoly_0_1_0.comp (C (-1) + C (1 - (-1)) * X) =
      b65x_bernsteinExpansion 4 b65x_regCoeff_0_1_0_0 := by
  norm_num [b65x_regPoly_0_1_0, b65x_regCoeff_0_1_0_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg]
  ring

theorem b65x_regCoeff_positive_0_1_0_0 : ∀ i, 0 < b65x_regCoeff_0_1_0_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_0_1_0_0]

theorem b65x_regPoly_positive_0_1_0 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < b65x_regPoly_0_1_0.eval₂ (Rat.castHom ℝ) t := by
  exact b65x_bernstein_interval_pos b65x_regPoly_0_1_0 (-1) 1 (by norm_num)
    4 b65x_regCoeff_0_1_0_0 b65x_regIdentity_0_1_0_0 b65x_regCoeff_positive_0_1_0_0 t (by simpa using ht)

theorem b65x_certFactor_norm_0_1_0 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_0_1 0)).eval₂ (Rat.castHom ℝ) t =
      (625000000 : ℝ) * b65x_regPoly_0_1_0.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_0_1, b65x_certP7_0_1,
    b65x_certN_0_1, b65x_certD_0_1, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_0_1_0,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_0_1_0 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < (b65x_cpNorm (b65x_certFactors_0_1 0)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_0_1_0]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_0_1_0 t ht)

def b65x_regPoly_0_1_1 : ℚ[X] :=
  C (87714959190718244529114481) + X * (C (0) + X * (C (96540555559049186352228962) + X * (C (0) + X * (C (8825596368330941823114481) + X * (0)))))

def b65x_regCoeff_0_1_1_0 : Fin 5 → ℚ :=
  ![193081111118098372704457924, 315557451289549210824000000, 386162222236196745408915848, 315557451289549210824000000, 193081111118098372704457924]

theorem b65x_regIdentity_0_1_1_0 :
    b65x_regPoly_0_1_1.comp (C (-1) + C (1 - (-1)) * X) =
      b65x_bernsteinExpansion 4 b65x_regCoeff_0_1_1_0 := by
  norm_num [b65x_regPoly_0_1_1, b65x_regCoeff_0_1_1_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg]
  ring

theorem b65x_regCoeff_positive_0_1_1_0 : ∀ i, 0 < b65x_regCoeff_0_1_1_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_0_1_1_0]

theorem b65x_regPoly_positive_0_1_1 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < b65x_regPoly_0_1_1.eval₂ (Rat.castHom ℝ) t := by
  exact b65x_bernstein_interval_pos b65x_regPoly_0_1_1 (-1) 1 (by norm_num)
    4 b65x_regCoeff_0_1_1_0 b65x_regIdentity_0_1_1_0 b65x_regCoeff_positive_0_1_1_0 t (by simpa using ht)

theorem b65x_certFactor_norm_0_1_1 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_0_1 1)).eval₂ (Rat.castHom ℝ) t =
      (1 : ℝ) * b65x_regPoly_0_1_1.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_0_1, b65x_certP7_0_1,
    b65x_certN_0_1, b65x_certD_0_1, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_0_1_1,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_0_1_1 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < (b65x_cpNorm (b65x_certFactors_0_1 1)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_0_1_1]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_0_1_1 t ht)

def b65x_regPoly_0_1_2 : ℚ[X] :=
  C (9148522871636238178014481) + X * (C (0) + X * (C (10331149714059475454028962) + X * (C (0) + X * (C (1182626842423237276014481) + X * (0)))))

def b65x_regCoeff_0_1_2_0 : Fin 5 → ℚ :=
  ![20662299428118950908057924, 31863584116852003608000000, 41324598856237901816115848, 31863584116852003608000000, 20662299428118950908057924]

theorem b65x_regIdentity_0_1_2_0 :
    b65x_regPoly_0_1_2.comp (C (-1) + C (1 - (-1)) * X) =
      b65x_bernsteinExpansion 4 b65x_regCoeff_0_1_2_0 := by
  norm_num [b65x_regPoly_0_1_2, b65x_regCoeff_0_1_2_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg]
  ring

theorem b65x_regCoeff_positive_0_1_2_0 : ∀ i, 0 < b65x_regCoeff_0_1_2_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_0_1_2_0]

theorem b65x_regPoly_positive_0_1_2 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < b65x_regPoly_0_1_2.eval₂ (Rat.castHom ℝ) t := by
  exact b65x_bernstein_interval_pos b65x_regPoly_0_1_2 (-1) 1 (by norm_num)
    4 b65x_regCoeff_0_1_2_0 b65x_regIdentity_0_1_2_0 b65x_regCoeff_positive_0_1_2_0 t (by simpa using ht)

theorem b65x_certFactor_norm_0_1_2 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_0_1 2)).eval₂ (Rat.castHom ℝ) t =
      (1 : ℝ) * b65x_regPoly_0_1_2.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_0_1, b65x_certP7_0_1,
    b65x_certN_0_1, b65x_certD_0_1, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_0_1_2,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_0_1_2 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < (b65x_cpNorm (b65x_certFactors_0_1 2)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_0_1_2]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_0_1_2 t ht)

def b65x_regPoly_0_1_3 : ℚ[X] :=
  C (42078683272682988026364481) + X * (C (0) + X * (C (45097483869043677856728962) + X * (C (0) + X * (C (3018800596360689830364481) + X * (0)))))

def b65x_regCoeff_0_1_3_0 : Fin 5 → ℚ :=
  ![90194967738087355713457924, 156239530705289192784000000, 180389935476174711426915848, 156239530705289192784000000, 90194967738087355713457924]

theorem b65x_regIdentity_0_1_3_0 :
    b65x_regPoly_0_1_3.comp (C (-1) + C (1 - (-1)) * X) =
      b65x_bernsteinExpansion 4 b65x_regCoeff_0_1_3_0 := by
  norm_num [b65x_regPoly_0_1_3, b65x_regCoeff_0_1_3_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg]
  ring

theorem b65x_regCoeff_positive_0_1_3_0 : ∀ i, 0 < b65x_regCoeff_0_1_3_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_0_1_3_0]

theorem b65x_regPoly_positive_0_1_3 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < b65x_regPoly_0_1_3.eval₂ (Rat.castHom ℝ) t := by
  exact b65x_bernstein_interval_pos b65x_regPoly_0_1_3 (-1) 1 (by norm_num)
    4 b65x_regCoeff_0_1_3_0 b65x_regIdentity_0_1_3_0 b65x_regCoeff_positive_0_1_3_0 t (by simpa using ht)

theorem b65x_certFactor_norm_0_1_3 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_0_1 3)).eval₂ (Rat.castHom ℝ) t =
      (1 : ℝ) * b65x_regPoly_0_1_3.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_0_1, b65x_certP7_0_1,
    b65x_certN_0_1, b65x_certD_0_1, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_0_1_3,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_0_1_3 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < (b65x_cpNorm (b65x_certFactors_0_1 3)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_0_1_3]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_0_1_3 t ht)

def b65x_regPoly_0_1_5 : ℚ[X] :=
  C (10851832673587471048950583655684669186187249583785474498282685949745686929652967260421289800335242452749094008093420130963619157632922624591542638038689) + X * (C (0) + X * (C (71825206828563962205136680762607956577668787717725292728114542169356824557546239295198327242587235052170576469667589094720116072998191260803837502339268) + X * (C (0) + X * (C (204743262739987235850385329838343217328430597553244037134864092246042037993540980237492515897643515111662534627297191201803871854103995480977648415178474) + X * (C (0) + X * (C (328050571510751051279879398081390338752590867502142246903489144682971351063765614480799622954588871965242349950974561001774563421237985375704801891636580) + X * (C (0) + X * (C (323590945808991621074963468754415902120405501325552586692308602704953455730441007350727159726804494966371965957456238738697213211866930597168620398526055) + X * (C (0) + X * (C (202792718460297218388629453035572838182526379405383307716064787653975139305190251847596218046659252530800906111510598090610113778719031580529298465391688) + X * (C (0) + X * (C (80932781846630263873603642170992371659294238526849252759373949028973096344730528933190531626933818792594973500305922471308588613254742265668438341998636) + X * (C (0) + X * (C (20378691523948282306372293510905287380802560795575719685252710821688616600731407579739405200987696718479663957322422885556545469307963897029310120891688) + X * (C (0) + X * (C (3228584358898912930845512725398517298672634439086543782361926365433941586389152230039195018592639912360337237403469096131678347453172242793634967901055) + X * (C (0) + X * (C (318461693416104185601573399341820766718266597569923945308128568201314853020034458320014249763972171144882776386581401401346314240008972788144937886580) + X * (C (0) + X * (C (18841683216960853738743886042860685750145734974949872757969435558122727893747443147139364337343135400684810584460181358583114100407919810985633678474) + X * (C (0) + X * (C (607203632837778959013863847103394226509507148383882405594603146626398552678930183361618937577873905959980900620750125355090697389769629595961089268) + X * (C (0) + X * (C (8109296990512091131622787806775793004362052030120685682768633531466157843136819117878877551940604749105621671403924485848788399725474118483913689) + X * (0)))))))))))))))))))))))))

def b65x_regCoeff_0_1_5_0 : Fin 25 → ℚ :=
  ![1246732514441218912289156825307330690109066743051089749721269816998679745557612453183673898627049212623488678493524746448376080294401141712969977758470144, 12197866836104075195967831744516938965412424099011272809071198904061180977053307089282963736627156328687493808974295645833176196335272034784969335296000000, 64625418780732091444317683784863136687243096326910290688200704228796707422260097850019186490474495362577001072146319822233673051822681825441655733101641728, 241889013741362494679574587797384174669667186991116460717962795883709737033445487702401198023769064112747877123863823705055089506455567422634662688256000000, 710167511026573054884612356997802140523598067061679201671454749995949606603536859083263124742797962939832056676386266214751189394873156601916178532059029504, 1725464373974488202726008679502578624829334404222924949374871997430936009989990979647870509377462024708631272204118912767181268919348137273173313441280000000, 3582084492959060613274754375145034364386011655672743168526343753730403872238383599246344336472800970599619867796644618390049079338164316796724115106863431680, 6486482993184643852823069930316481958061083436424198212537590808769100105260013335445049426720760479225163246375529914062936032878952587179519940323840000000, 10389520762243179168381801833500050487744811401128025088418269403118405099189019998729477089148731165604461815617638278779874852291744740134242058990442721280, 14861701466535535130560235026519402639687067807287915588479714016600323543705625703316532937517912375509602575242313242204970393919116074839039880647680000000, 19111249689767921626942683220749212407545558771021361027464207936527214037550788949097151922313194721648601924745040704361376438036502010462735582384708354048, 22188115463029685921686891043507077259153659051472306202813410012963307532193324278919947063481146045964241937062065384429169032399610135110655832906752000000, 23314049191447041778966103864711899899320589976176518213678613943110122463346636351855183114972628019707762865282627145665169545319153422414060291448826413056, 22188115463029685921686891043507077259153659051472306202813410012963307532193324278919947063481146045964241937062065384429169032399610135110655832906752000000, 19111249689767921626942683220749212407545558771021361027464207936527214037550788949097151922313194721648601924745040704361376438036502010462735582384708354048, 14861701466535535130560235026519402639687067807287915588479714016600323543705625703316532937517912375509602575242313242204970393919116074839039880647680000000, 10389520762243179168381801833500050487744811401128025088418269403118405099189019998729477089148731165604461815617638278779874852291744740134242058990442721280, 6486482993184643852823069930316481958061083436424198212537590808769100105260013335445049426720760479225163246375529914062936032878952587179519940323840000000, 3582084492959060613274754375145034364386011655672743168526343753730403872238383599246344336472800970599619867796644618390049079338164316796724115106863431680, 1725464373974488202726008679502578624829334404222924949374871997430936009989990979647870509377462024708631272204118912767181268919348137273173313441280000000, 710167511026573054884612356997802140523598067061679201671454749995949606603536859083263124742797962939832056676386266214751189394873156601916178532059029504, 241889013741362494679574587797384174669667186991116460717962795883709737033445487702401198023769064112747877123863823705055089506455567422634662688256000000, 64625418780732091444317683784863136687243096326910290688200704228796707422260097850019186490474495362577001072146319822233673051822681825441655733101641728, 12197866836104075195967831744516938965412424099011272809071198904061180977053307089282963736627156328687493808974295645833176196335272034784969335296000000, 1246732514441218912289156825307330690109066743051089749721269816998679745557612453183673898627049212623488678493524746448376080294401141712969977758470144]

theorem b65x_regIdentity_0_1_5_0 :
    b65x_regPoly_0_1_5.comp (C (-1) + C (1 - (-1)) * X) =
      b65x_bernsteinExpansion 24 b65x_regCoeff_0_1_5_0 := by
  norm_num [b65x_regPoly_0_1_5, b65x_regCoeff_0_1_5_0, b65x_bernsteinExpansion,
    Fin.sum_univ_succ, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.comp_C,
    Polynomial.comp_X, Polynomial.C_ofNat, map_neg]
  ring

theorem b65x_regCoeff_positive_0_1_5_0 : ∀ i, 0 < b65x_regCoeff_0_1_5_0 i := by
  intro i
  fin_cases i <;> norm_num [b65x_regCoeff_0_1_5_0]

theorem b65x_regPoly_positive_0_1_5 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < b65x_regPoly_0_1_5.eval₂ (Rat.castHom ℝ) t := by
  exact b65x_bernstein_interval_pos b65x_regPoly_0_1_5 (-1) 1 (by norm_num)
    24 b65x_regCoeff_0_1_5_0 b65x_regIdentity_0_1_5_0 b65x_regCoeff_positive_0_1_5_0 t (by simpa using ht)

theorem b65x_certFactor_norm_0_1_5 (t : ℝ) :
    (b65x_cpNorm (b65x_certFactors_0_1 5)).eval₂ (Rat.castHom ℝ) t =
      (256 : ℝ) * b65x_regPoly_0_1_5.eval₂ (Rat.castHom ℝ) t := by
  norm_num [b65x_cpNorm, b65x_certFactors_0_1, b65x_certP7_0_1,
    b65x_certN_0_1, b65x_certD_0_1, b65x_cpSub, b65x_cpAdd,
    b65x_cpMul, b65x_cpPow, b65x_cpConst, b65x_cpScale, b65x_regPoly_0_1_5,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  ring

theorem b65x_certFactor_norm_positive_0_1_5 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < (b65x_cpNorm (b65x_certFactors_0_1 5)).eval₂ (Rat.castHom ℝ) t := by
  rw [b65x_certFactor_norm_0_1_5]
  exact mul_pos (by norm_num) (b65x_regPoly_positive_0_1_5 t ht)

theorem b65x_certFactors_ne_zero_0_1 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (j : Fin 6) : b65x_cpEval (b65x_certFactors_0_1 j) t ≠ 0 := by
  apply b65x_cpEval_ne_zero
  fin_cases j
  · exact b65x_certFactor_norm_positive_0_1_0 t ht
  · exact b65x_certFactor_norm_positive_0_1_1 t ht
  · exact b65x_certFactor_norm_positive_0_1_2 t ht
  · exact b65x_certFactor_norm_positive_0_1_3 t ht
  · change 0 < (b65x_cpNorm b65x_certP5_0_1).eval₂ (Rat.castHom ℝ) t
    rw [b65x_certP5_norm_0_1]
    exact mul_pos (by norm_num) (b65x_regPoly_positive_0_1_4 t ht)
  · exact b65x_certFactor_norm_positive_0_1_5 t ht

theorem b65x_piece_regular_0_1 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ((b65b_boxCentre 6).1 : ℂ) - b65x_piece 0 1 t *
        (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
      b65b_inverseNormalization (b65x_piece 0 1 t) ∈ b65s_regular := by
  have h0 := b65x_certFactors_ne_zero_0_1 t ht 0
  have h1 := b65x_certFactors_ne_zero_0_1 t ht 1
  have h2 := b65x_certFactors_ne_zero_0_1 t ht 2
  have h3 := b65x_certFactors_ne_zero_0_1 t ht 3
  have h4 := b65x_certFactors_ne_zero_0_1 t ht 4
  have h5 := b65x_certFactors_ne_zero_0_1 t ht 5
  change b65x_cpEval b65x_certD_0_1 t ≠ 0 at h0
  change b65x_cpEval (b65x_cpSub b65x_certN_0_1 (b65x_cpScale 3 b65x_certD_0_1)) t ≠ 0 at h1
  change b65x_cpEval (b65x_cpSub b65x_certN_0_1 b65x_certD_0_1) t ≠ 0 at h2
  change b65x_cpEval (b65x_cpAdd b65x_certN_0_1 (b65x_cpScale 2 b65x_certD_0_1)) t ≠ 0 at h3
  change b65x_cpEval b65x_certP5_0_1 t ≠ 0 at h4
  change b65x_cpEval b65x_certP7_0_1 t ≠ 0 at h5
  norm_num only [b65x_certFactors_0_1, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, b65x_certP5_0_1, b65x_certP7_0_1,
    b65x_cpEval_sub, b65x_cpEval_add, b65x_cpEval_mul, b65x_cpEval_pow,
    b65x_cpEval_scale] at h0 h1 h2 h3 h4 h5
  have hN : b65x_cpEval b65x_certN_0_1 t ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [b65x_cpEval, b65x_certN_0_1, Polynomial.eval₂_pow,
      pow_two, Complex.mul_re] at hr
    nlinarith [sq_nonneg t]
  have hreg : b65b_inverseNormalization (b65x_piece 0 1 t) ∈ b65s_regular := by
    rw [b65x_certND_ratio_0_1]
    exact b65x_regular_of_homogeneous _ _ h0 hN h1 h2 h3
      (by simpa only [mul_assoc] using h4) (by simpa only [mul_assoc] using h5)
  refine ⟨?_, hreg⟩
  intro h
  apply hreg.1
  simp [b65b_inverseNormalization, h]

theorem b65x_piece_regular_0_0 (t : ℝ) :
    ((b65b_boxCentre 6).1 : ℂ) - b65x_piece 0 0 t *
        (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
      b65b_inverseNormalization (b65x_piece 0 0 t) ∈ b65s_regular := by
  have he : b65x_piece 0 0 t = b65x_piece 0 1 (-1) := by
    norm_num [b65x_piece, b65x_centre, b65x_radius, b65x_et, mr_basePoint, mr_centre]
    <;> ring
  rw [he]
  exact b65x_piece_regular_0_1 (-1) (by norm_num)

end HodgeLean.Foundations.Program

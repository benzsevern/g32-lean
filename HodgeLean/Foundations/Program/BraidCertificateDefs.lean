import HodgeLean.Foundations.Program.PullbackMonodromy

/-! # Literal braid-certificate data

Integral pairs encode a + bω. Matrices are stored with the exported factor three.
HC no distance; AV milestone no distance.
-/

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- Certificate data.
Source: B65-BRAIDCERT JSON, word.moves. -/
def b65b_word : List b65s_Move :=
  [ .negative 4, .negative 5, .negative 3, .negative 4, .positive 2, .positive 3, .positive 3, .positive 2, .positive 4, .positive 3, .positive 5, .positive 4, .positive 6, .positive 5, .positive 5, .positive 6, .negative 4, .negative 5, .negative 3, .negative 4, .negative 2, .negative 3, .negative 1, .negative 2, .negative 2, .negative 1, .positive 3, .positive 2, .positive 4, .positive 3, .positive 5, .positive 4, .negative 5, .positive 2, .positive 3, .negative 2, .positive 1, .negative 4, .negative 5, .negative 3, .negative 3, .negative 2, .negative 1, .negative 1, .negative 6, .positive 5, .negative 6, .negative 4, .negative 5, .negative 3, .negative 4, .negative 2, .negative 3, .negative 2, .negative 7, .positive 6, .negative 5, .negative 5, .negative 4, .negative 3, .positive 2, .negative 3, .negative 8, .negative 7, .positive 6, .negative 7, .positive 5, .negative 9, .negative 8, .negative 7, .negative 6, .positive 10, .positive 9, .negative 8, .negative 8, .negative 7, .negative 6, .positive 5, .positive 11, .negative 10, .positive 11, .negative 9, .negative 10, .negative 9, .negative 8, .negative 7 ]

example : b65b_word.length = 86 := rfl

/-- Certificate data.
Source: B65-BRAIDCERT JSON, path_moves. -/
def b65b_pathWord : List b65s_Move :=
  [.positive 3, .positive 2]

example : b65b_pathWord.length = 2 := rfl

/-- Certificate data.
Source: B65-BRAIDCERT JSON, T_init. -/
def b65b_initialIntegral : Fin 13 → Matrix (Fin 4) (Fin 4) (ℤ × ℤ) :=
  ![![![(0, 0), (3, 0), (0, 0), (0, 0)], ![(3, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (3, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (-3, 0)]], ![![(1, -1), (1, 2), (1, 2), (0, 0)], ![(1, -1), (1, -1), (-2, -1), (0, 0)], ![(1, -1), (-2, -1), (1, -1), (0, 0)], ![(0, 0), (0, 0), (0, 0), (3, 0)]], ![![(2, 1), (1, 2), (0, 0), (-1, -2)], ![(-2, -1), (2, 1), (0, 0), (1, -1)], ![(0, 0), (0, 0), (3, 0), (0, 0)], ![(2, 1), (1, -1), (0, 0), (2, 1)]], ![![(1, -1), (0, 0), (-1, 1), (2, 1)], ![(0, 0), (3, 0), (0, 0), (0, 0)], ![(-1, -2), (0, 0), (1, -1), (1, 2)], ![(2, 1), (0, 0), (1, -1), (1, -1)]], ![![(2, 1), (-2, -1), (0, 0), (2, 1)], ![(1, 2), (2, 1), (0, 0), (1, -1)], ![(0, 0), (0, 0), (3, 0), (0, 0)], ![(-1, -2), (1, -1), (0, 0), (2, 1)]], ![![(1, -1), (1, -1), (-2, -1), (0, 0)], ![(1, 2), (1, -1), (1, 2), (0, 0)], ![(-2, -1), (1, -1), (1, -1), (0, 0)], ![(0, 0), (0, 0), (0, 0), (3, 0)]], ![![(2, 1), (-2, -1), (0, 0), (-1, 1)], ![(1, 2), (2, 1), (0, 0), (1, 2)], ![(0, 0), (0, 0), (3, 0), (0, 0)], ![(-1, 1), (-2, -1), (0, 0), (2, 1)]], ![![(2, 1), (1, 2), (0, 0), (-1, -2)], ![(-2, -1), (2, 1), (0, 0), (1, -1)], ![(0, 0), (0, 0), (3, 0), (0, 0)], ![(2, 1), (1, -1), (0, 0), (2, 1)]], ![![(1, -1), (0, 0), (2, 1), (2, 1)], ![(0, 0), (3, 0), (0, 0), (0, 0)], ![(2, 1), (0, 0), (1, -1), (-2, -1)], ![(2, 1), (0, 0), (-2, -1), (1, -1)]], ![![(2, 1), (-1, 1), (-1, -2), (0, 0)], ![(-1, 1), (2, 1), (-1, -2), (0, 0)], ![(2, 1), (2, 1), (2, 1), (0, 0)], ![(0, 0), (0, 0), (0, 0), (3, 0)]], ![![(3, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (3, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (-3, -3), (0, 0)], ![(0, 0), (0, 0), (0, 0), (3, 0)]], ![![(3, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (2, 1), (-2, -1), (2, 1)], ![(0, 0), (1, 2), (2, 1), (1, -1)], ![(0, 0), (-1, -2), (1, -1), (2, 1)]], ![![(1, -1), (0, 0), (-1, 1), (2, 1)], ![(0, 0), (3, 0), (0, 0), (0, 0)], ![(-1, -2), (0, 0), (1, -1), (1, 2)], ![(2, 1), (0, 0), (1, -1), (1, -1)]]]

example : b65b_initialIntegral 0 0 0 = (0, 0) := rfl

/-- Certificate data.
Source: B65-BRAIDCERT JSON, T_final. -/
def b65b_finalIntegral : Fin 13 → Matrix (Fin 4) (Fin 4) (ℤ × ℤ) :=
  ![![![(0, 0), (3, 0), (0, 0), (0, 0)], ![(3, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (3, 0), (0, 0)], ![(0, 0), (0, 0), (0, 0), (-3, 0)]], ![![(1, -1), (1, 2), (1, 2), (0, 0)], ![(1, -1), (1, -1), (-2, -1), (0, 0)], ![(1, -1), (-2, -1), (1, -1), (0, 0)], ![(0, 0), (0, 0), (0, 0), (3, 0)]], ![![(2, 1), (-1, 1), (-1, -2), (0, 0)], ![(-1, 1), (2, 1), (-1, -2), (0, 0)], ![(2, 1), (2, 1), (2, 1), (0, 0)], ![(0, 0), (0, 0), (0, 0), (3, 0)]], ![![(2, 1), (1, 2), (0, 0), (-1, -2)], ![(-2, -1), (2, 1), (0, 0), (1, -1)], ![(0, 0), (0, 0), (3, 0), (0, 0)], ![(2, 1), (1, -1), (0, 0), (2, 1)]], ![![(1, -1), (0, 0), (-1, 1), (2, 1)], ![(0, 0), (3, 0), (0, 0), (0, 0)], ![(-1, -2), (0, 0), (1, -1), (1, 2)], ![(2, 1), (0, 0), (1, -1), (1, -1)]], ![![(1, -1), (1, -1), (-2, -1), (0, 0)], ![(1, 2), (1, -1), (1, 2), (0, 0)], ![(-2, -1), (1, -1), (1, -1), (0, 0)], ![(0, 0), (0, 0), (0, 0), (3, 0)]], ![![(2, 1), (-2, -1), (0, 0), (-1, 1)], ![(1, 2), (2, 1), (0, 0), (1, 2)], ![(0, 0), (0, 0), (3, 0), (0, 0)], ![(-1, 1), (-2, -1), (0, 0), (2, 1)]], ![![(2, 1), (1, 2), (0, 0), (-1, -2)], ![(-2, -1), (2, 1), (0, 0), (1, -1)], ![(0, 0), (0, 0), (3, 0), (0, 0)], ![(2, 1), (1, -1), (0, 0), (2, 1)]], ![![(1, -1), (0, 0), (2, 1), (2, 1)], ![(0, 0), (3, 0), (0, 0), (0, 0)], ![(2, 1), (0, 0), (1, -1), (-2, -1)], ![(2, 1), (0, 0), (-2, -1), (1, -1)]], ![![(2, 1), (-1, 1), (-1, -2), (0, 0)], ![(-1, 1), (2, 1), (-1, -2), (0, 0)], ![(2, 1), (2, 1), (2, 1), (0, 0)], ![(0, 0), (0, 0), (0, 0), (3, 0)]], ![![(3, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (3, 0), (0, 0), (0, 0)], ![(0, 0), (0, 0), (-3, -3), (0, 0)], ![(0, 0), (0, 0), (0, 0), (3, 0)]], ![![(3, 0), (0, 0), (0, 0), (0, 0)], ![(0, 0), (2, 1), (-2, -1), (2, 1)], ![(0, 0), (1, 2), (2, 1), (1, -1)], ![(0, 0), (-1, -2), (1, -1), (2, 1)]], ![![(1, -1), (0, 0), (-1, 1), (2, 1)], ![(0, 0), (3, 0), (0, 0), (0, 0)], ![(-1, -2), (0, 0), (1, -1), (1, 2)], ![(2, 1), (0, 0), (1, -1), (1, -1)]]]

example : b65b_finalIntegral 0 0 0 = (0, 0) := rfl

/-- Evaluation of an exported integral matrix in the fixed column representation.
Source: B65-BRAIDCERT JSON, format; G32 Appendix A. -/
def b65b_decode (A : Matrix (Fin 4) (Fin 4) (ℤ × ℤ)) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j ↦ ((A i j).1 + (A i j).2 * g32h_omega) / 3

example : b65b_decode 0 = 0 := by ext i j; simp [b65b_decode]

/-- Cut generators in order 5, minus seven, zero.
Source: B65-BRAIDCERT checker part E, Dof. -/
def b65b_cut : Fin 3 → b4b_Group :=
  ![b4b_generators 0, b4b_generators 1,
    b4b_generators 1 * b4b_generators 2 * (b4b_generators 1)⁻¹]

example : b65b_cut 0 = b4b_generators 0 := rfl

/-- Chronological crossing letters, evaluated in reverse order for column multiplication.
Source: B65-BRAIDCERT checker part E, rhow. -/
def b65b_eval (w : List (Fin 3 × ℤ)) : b4b_Group :=
  ((w.reverse).map (fun a ↦ b65b_cut a.1 ^ a.2)).prod

example : b65b_eval [] = 1 := rfl

/-- Certificate data.
Source: B65-BRAIDCERT crossing words and part F, expanded cut words. -/
def b65b_initialWords : Fin 13 → List (Fin 3 × ℤ) :=
  ![[(2, 1), (2, 1)], [(1, 1)], [(0, 1)], [(2, -1), (1, 1), (2, 1)], [(2, -1), (0, 1), (2, 1)], [(2, -1), (2, -1), (1, 1), (2, 1), (2, 1)], [(2, -1), (2, -1), (0, 1), (2, 1), (2, 1)], [(0, 1)], [(0, 1), (1, 1), (0, -1)], [(0, 1), (1, 1), (2, 1), (0, 1), (2, -1), (1, -1), (0, -1)], [(0, 1), (1, 1), (2, 1), (0, 1), (1, 1), (0, -1), (2, -1), (1, -1), (0, -1)], [(2, -1), (1, -1), (0, 1), (1, 1), (2, 1)], [(2, -1), (1, 1), (2, 1)]]

example : b65b_initialWords 0 = [(2, 1), (2, 1)] := rfl

/-- Certificate data.
Source: B65-BRAIDCERT checker parts E–F. -/
def b65b_initial : Fin 13 → b4b_Group :=
  fun i ↦ b65b_eval (b65b_initialWords i)

example : b65b_initial 0 = b65b_eval [(2, 1), (2, 1)] := rfl

/-- Certificate data.
Source: B65-BRAIDCERT crossing words and part F, expanded cut words. -/
def b65b_finalWords : Fin 13 → List (Fin 3 × ℤ) :=
  ![[(2, 1), (2, 1)], [(1, 1)], [(0, -1), (2, -1), (1, -1), (0, 1), (1, 1), (2, 1), (0, 1)], [(0, 1)], [(2, -1), (1, 1), (2, 1)], [(2, -1), (2, -1), (1, 1), (2, 1), (2, 1)], [(2, -1), (2, -1), (0, 1), (2, 1), (2, 1)], [(0, 1)], [(0, 1), (1, 1), (0, -1)], [(0, 1), (1, 1), (2, 1), (0, 1), (2, -1), (1, -1), (0, -1)], [(0, 1), (1, 1), (2, 1), (0, 1), (1, 1), (0, -1), (2, -1), (1, -1), (0, -1)], [(2, -1), (1, -1), (0, 1), (1, 1), (2, 1)], [(2, -1), (1, 1), (2, 1)]]

example : b65b_finalWords 0 = [(2, 1), (2, 1)] := rfl

/-- Certificate data.
Source: B65-BRAIDCERT checker parts E–F. -/
def b65b_final : Fin 13 → b4b_Group :=
  fun i ↦ b65b_eval (b65b_finalWords i)

example : b65b_final 0 = b65b_eval [(2, 1), (2, 1)] := rfl

/-- Certificate data.
Source: B65-BRAIDCERT JSON, boxes. -/
def b65b_boxCentre : Fin 12 → ℚ × ℚ :=
  ![((-2220277/250000), (0/1)), ((1402233/1000000), (0/1)), ((746023/1000000), (556409/1000000)), ((746023/1000000), (-556409/1000000)), ((-190793/500000), (884017/1000000)), ((-190793/500000), (-884017/1000000)), ((-65683/100000), (0/1)), ((545987/1000000), (0/1)), ((7873/6250), (-78053/250000)), ((7873/6250), (78053/250000)), ((-1766759/1000000), (727483/250000)), ((-1766759/1000000), (-727483/250000))]

example : b65b_boxCentre 0 = (-2220277/250000, 0) := by norm_num [b65b_boxCentre]

/-- Certificate data.
Source: B65-BRAIDCERT JSON, boxes. -/
def b65b_boxFibre : Fin 12 → ℤ :=
  ![5, 5, 5, 5, 5, 5, -7, -7, -7, -7, -7, -7]

example : b65b_boxFibre 0 = 5 := rfl

/-- Certificate data.
Source: B65-BRAIDCERT JSON, boxes. -/
def b65b_boxIndex : Fin 12 → Fin 12 :=
  ![10, 3, 5, 1, 9, 6, 11, 0, 2, 4, 8, 7]

example : b65b_boxIndex 0 = 10 := rfl

/-- Certificate data.
Source: B65-BRAIDCERT JSON, path.vertices. -/
def b65b_vertex0 : Fin 12 → ℚ × ℚ :=
  ![((-137895761/100000000), (0)), ((-69078697/100000000), (-9112919/20000000)), ((-61034701/100000000), (-1314801/10000000)), ((-14642301/25000000), (0)), ((-61034701/100000000), (1314801/10000000)), ((-69078697/100000000), (9112919/20000000)), ((21207303/100000000), (-16908273/25000000)), ((2826577/100000000), (-2226199/12500000)), ((2826577/100000000), (2226199/12500000)), ((21207303/100000000), (16908273/25000000)), ((0), (0)), ((1), (0))]

example : b65b_vertex0 10 = (0, 0) := rfl

/-- Certificate data.
Source: B65-BRAIDCERT JSON, path.vertices. -/
def b65b_vertex1 : Fin 12 → ℚ × ℚ :=
  ![((-12), (0)), ((-11), (0)), ((-10), (0)), ((-9), (0)), ((-8), (0)), ((-7), (0)), ((-6), (0)), ((-5), (0)), ((-4), (0)), ((-3), (0)), ((0), (0)), ((1), (0))]

example : b65b_vertex1 10 = (0, 0) := rfl

/-- The rational straight segment, interpreted in the complex plane.
Source: B65-BRAIDCERT checker part F. -/
def b65b_track (t : ℝ) (i : Fin 12) : ℂ :=
  let a := b65b_vertex0 i
  let b := b65b_vertex1 i
  (1 - (t : ℂ)) * ((a.1 : ℂ) + (a.2 : ℂ) * Complex.I) +
    (t : ℂ) * ((b.1 : ℂ) + (b.2 : ℂ) * Complex.I)

example (i : Fin 12) : b65b_track 0 i =
    ((b65b_vertex0 i).1 : ℂ) + ((b65b_vertex0 i).2 : ℂ) * Complex.I := by
  simp [b65b_track]

example : 0 < Module.finrank ℂ (Fin 4 → ℂ) := by simp
example : b4b_root 0 ≠ 1 := by
  intro h
  have ho := b63_root_order (0 : Fin 13)
  rw [h, orderOf_one] at ho
  norm_num at ho

/-- Rational certificate data in final-mark label order.
Source: B65-BRAIDCERT JSON, lasso_discs and enclosures. -/
def b65b_radius : Fin 12 → ℚ :=
  ![(147451/50000000), (83499/50000000), (13377/20000000), (13377/20000000), (13377/20000000), (83499/50000000), (265529/100000000), (45081/50000000), (45081/50000000), (265529/100000000), (9983/25000000), (36261/10000000)]

example : 0 < b65b_radius 0 := by norm_num [b65b_radius]

/-- Rational certificate data in final-mark label order.
Source: B65-BRAIDCERT JSON, lasso_discs and enclosures. -/
def b65b_enclosure : Fin 12 → Fin 4 → ℚ :=
  ![![(-6953706933331490899074775/5038716849726953128089649), (-1522220701328465264737840496594229861915783861325/1104771605207656310060144646701138820731190608087), (-1347131219116011257000/5038716849726953128089649), (1347131219116011257000/5038716849726953128089649)], ![(-1012082592583735046179919/1464106175567072647720861), (-1011394934732640718529559/1465129592012748984611341), (-75249841226378231938277889432773236100542661634/165008098743994721853176826185284050221964837277), (-75120822909595390936242647465435061259801153194/165008098743994721853176826185284050221964837277)], ![(-37473791691961376651185/61365902511695487998741), (-1086132048501465947001015/1780448826703138726417189), (-417001452829735329233172273267926639855671584090/3168506624669295337016742990909622193313510012421), (-416190236195162932373431345886726549818156163490/3168506624669295337016742990909622193313510012421)], ![(-19478759048326090383204655/33242438319375429207580969), (-647175336096229625415212715427404456201046016306395/1105482512903557233541239469886406387091874893915361), (-1578442065896613499000/33242438319375429207580969), (1578442065896613499000/33242438319375429207580969)], ![(-37473791691961376651185/61365902511695487998741), (-1086132048501465947001015/1780448826703138726417189), (416190236195162932373431345886726549818156163490/3168506624669295337016742990909622193313510012421), (417001452829735329233172273267926639855671584090/3168506624669295337016742990909622193313510012421)], ![(-1012082592583735046179919/1464106175567072647720861), (-1011394934732640718529559/1465129592012748984611341), (75120822909595390936242647465435061259801153194/165008098743994721853176826185284050221964837277), (75249841226378231938277889432773236100542661634/165008098743994721853176826185284050221964837277)], ![(160167027956248642545045006029605632448506426229/756197517555938599352812948961990819661822952533), (2087435984042939175033774642794358947215205249717/9830567728227201791586568336505880655603698382929), (-163172006222229097625344/241105019169658677271389), (-2119864236786370008771192/3136382312405633185150297)], ![(43334932633665718437063245380320758454893561042069/1536150173668988055341509288841396648025706411041721), (3346619325391171461200134653070583075671924578813/118165397974537542718577637603184357540438954695517), (-6981954735562731188826112/39188682543327805579907621), (-6978538473472686480023232/39198821546771549066532101)], ![(43334932633665718437063245380320758454893561042069/1536150173668988055341509288841396648025706411041721), (3346619325391171461200134653070583075671924578813/118165397974537542718577637603184357540438954695517), (6978538473472686480023232/39198821546771549066532101), (6981954735562731188826112/39188682543327805579907621)], ![(160167027956248642545045006029605632448506426229/756197517555938599352812948961990819661822952533), (2087435984042939175033774642794358947215205249717/9830567728227201791586568336505880655603698382929), (2119864236786370008771192/3136382312405633185150297), (163172006222229097625344/241105019169658677271389)], ![(-149951890903504797875/83352569036756560188013584), (149951890903504797875/83352569036756560188013584), (-4686075734870255500/5209535564797285011750849), (4686075734870255500/5209535564797285011750849)], ![(5318342740364809636119327010729024225168610581/5322100325366026483587268977831799517356754061), (72978492230574740970629/72926968607108637939009), (-11996353881267854080/72926968607108637939009), (11996353881267854080/72926968607108637939009)]]

example : b65b_enclosure 0 0 < b65b_enclosure 0 1 := by norm_num [b65b_enclosure]

/-- Dot product of disc-centre directions from the fixed base point.
Source: B65-BRAIDCERT checker C, coneok. -/
def b65b_dot (i j : Fin 12) : ℚ :=
  ((b65b_vertex0 i).1 + 11/2) * ((b65b_vertex0 j).1 + 11/2) +
    ((b65b_vertex0 i).2 - 10) * ((b65b_vertex0 j).2 - 10)

example : b65b_dot 10 10 = (11/2)^2 + 100 := by norm_num [b65b_dot, b65b_vertex0]

/-- Signed area of the two disc-centre directions from the base point.
Source: B65-BRAIDCERT checker C, coneok. -/
def b65b_cross (i j : Fin 12) : ℚ :=
  ((b65b_vertex0 i).1 + 11/2) * ((b65b_vertex0 j).2 - 10) -
    ((b65b_vertex0 i).2 - 10) * ((b65b_vertex0 j).1 + 11/2)

example (i : Fin 12) : b65b_cross i i = 0 := by unfold b65b_cross; ring

/-- Root-to-centre motion inside each disc followed by the recorded straight segment.
Source: B65-BRAIDCERT REPORT §1.2, braid-trivial disc isotopy and path.vertices. -/
def b65b_configuration (p : Fin 12 → ℂ) (t : ℝ) (i : Fin 12) : ℂ :=
  if t ≤ 1/2 then
    (1 - 2 * (t : ℂ)) * b65s_normalize (p 10) (p 11) (p i) +
      (2 * (t : ℂ)) * b65b_track 0 i
  else b65b_track (2 * t - 1) i

example (p : Fin 12 → ℂ) (i : Fin 12) :
    b65b_configuration p 0 i = b65s_normalize (p 10) (p 11) (p i) := by
  norm_num [b65b_configuration]

/-- Inverse of the rational box-centre normalization in its finite chart.
Source: B65-BRAIDCERT checker D, Minv. -/
def b65b_inverseNormalization (w : ℂ) : ℂ :=
  let a : ℂ := (b65b_boxCentre 0).1
  let b : ℂ := (b65b_boxCentre 6).1
  a * b / (b - w * (b - a))

example : b65b_inverseNormalization 0 = ((b65b_boxCentre 0).1 : ℂ) := by
  norm_num [b65b_inverseNormalization, b65b_boxCentre]

/-- Peripheral traces at the certified rational disc centres, in column tuple order.
Source: B65-BRAIDCERT checker D, lasso_word and OW; REPORT §1.4. -/
def b65b_lasso (i : Fin 13) (s : ℝ) : ℂ :=
  if hi : i.val = 0 then mr_outer s
  else
    let j : Fin 12 := ⟨13 - i.val - 1, by omega⟩
    let c := b65b_track 0 j
    let r : ℂ := b65b_radius j
    if s ≤ 1/3 then mr_basePoint + (3 * s : ℂ) * (c + Complex.I * r - mr_basePoint)
    else if s ≤ 2/3 then
      c + Complex.I * r * Complex.exp (2 * Real.pi * Complex.I * (3 * s - 1 : ℂ))
    else mr_basePoint + (3 - 3 * s : ℂ) * (c + Complex.I * r - mr_basePoint)

example (s : ℝ) : b65b_lasso 0 s = mr_outer s := rfl

end HodgeLean.Foundations.Program

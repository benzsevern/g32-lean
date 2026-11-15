import HodgeLean.Foundations.Program.BraidCertificateDefs

/-! # Braid-certificate bridges: cut crossings and rational lasso pieces

Data for the first stage of the crossing-class and path-lasso bridges. The cut system
uses downward rays from 5, minus seven and zero. The rational pieces are the segment
and the two semicircles of checker D, and the crossing table transcribes its isolating
intervals. Column index `i` of `b65b_lasso` refers to final-label order; `b65x_slot`
converts the counterclockwise slot order of `b65b_initialWords` into that index.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Finite branch values in cut order: 5, minus seven, zero.
Source: B65-BRAIDCERT JSON, downstairs.cuts; checker D, cross_piece. -/
def b65x_cutPoint : Fin 3 → ℝ := ![5, -7, 0]

example : b65x_cutPoint 1 = -7 := rfl

/-- The three-punctured downstairs plane.
Source: B65-BRAIDCERT REPORT §1.4; the domain of `b65r_four_point_monodromy`. -/
abbrev b65x_Down : Type := {z : ℂ // z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7}

example : ((⟨2, by norm_num⟩ : b65x_Down) : ℂ) = 2 := rfl

/-- A point lies on the open downward ray from the `k`-th cut point.
Source: B65-BRAIDCERT JSON, downstairs.cuts, rays `{a - i r : r > 0}`. -/
def b65x_OnCut (k : Fin 3) (z : ℂ) : Prop :=
  z.re = b65x_cutPoint k ∧ z.im < 0

example : b65x_OnCut 0 (5 - Complex.I) := by
  norm_num [b65x_OnCut, b65x_cutPoint]

example : ¬ b65x_OnCut 0 Complex.I := by
  simp [b65x_OnCut]

/-- A based downstairs loop meets the cuts exactly at the strictly increasing interior times
`u m`, and nowhere else. At time `u m` it crosses cut `w[m].1`, from left to right when
`w[m].2 = 1` and from right to left when `w[m].2 = -1`. The list `w` is the chronological
crossing word.
Source: Hatcher, Algebraic Topology, §1.2, van Kampen for the cut plane; Völklein, Groups as
Galois Groups, Ch. 9; B65-BRAIDCERT checker D, cross_piece. -/
def b65x_CrossesAs {y : b65x_Down} (d : Path y y) (w : List (Fin 3 × ℤ)) : Prop :=
  ∃ u : Fin w.length → unitInterval, StrictMono u ∧
    (∀ m : Fin w.length, 0 < (u m : ℝ) ∧ (u m : ℝ) < 1) ∧
    (∀ m : Fin w.length, w[m].2 = 1 ∨ w[m].2 = -1) ∧
    (∀ (k : Fin 3) (s : unitInterval),
      b65x_OnCut k (d s).val ↔ ∃ m : Fin w.length, w[m].1 = k ∧ s = u m) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ (m : Fin w.length) (s : unitInterval), |(s : ℝ) - u m| < ε →
      ((s : ℝ) < u m → (w[m].2 : ℝ) * ((d s).val.re - b65x_cutPoint w[m].1) < 0) ∧
      ((u m : ℝ) < s → 0 < (w[m].2 : ℝ) * ((d s).val.re - b65x_cutPoint w[m].1))

/-- The point `i` of the downstairs plane, above every cut.
Source: elementary plane geometry. -/
def b65x_upper : b65x_Down :=
  ⟨Complex.I, Complex.I_ne_zero,
    fun h ↦ by have := congrArg Complex.im h; norm_num at this,
    fun h ↦ by have := congrArg Complex.im h; norm_num at this⟩

example : b65x_CrossesAs (Path.refl b65x_upper) [] := by
  refine ⟨fun m ↦ m.elim0, fun m ↦ m.elim0, fun m ↦ m.elim0, fun m ↦ m.elim0, ?_,
    1, one_pos, fun m ↦ m.elim0⟩
  intro k s
  have hs : (b65x_upper : ℂ) = Complex.I := rfl
  simp [b65x_OnCut, hs]

/-- The predicate is not trivially true: the constant loop crosses no cut.
Source: `b65x_CrossesAs`. -/
example : ¬ b65x_CrossesAs (Path.refl b65x_upper) [(0, 1)] := by
  rintro ⟨u, -, -, -, hcut, -⟩
  have h := (hcut 0 (u 0)).2 ⟨0, rfl, rfl⟩
  have hs : (b65x_upper : ℂ) = Complex.I := rfl
  simp [b65x_OnCut, hs] at h
  exact absurd h.2 (by norm_num)

/-- Centres of three circles through `i`, one around each cut point: the circle about `5 + i`
of radius 5, the circle about `-7 + i` of radius 7 and the unit circle about 0.
Source: elementary plane geometry; the cut points `b65x_cutPoint`. -/
def b65x_loopCentre : Fin 3 → ℂ := ![5 + Complex.I, -7 + Complex.I, 0]

example : b65x_loopCentre 2 = 0 := rfl

/-- The counterclockwise circle through `i` about `b65x_loopCentre j`, starting at `i`.
Source: elementary plane geometry. -/
def b65x_loopFun (j : Fin 3) (s : ℝ) : ℂ :=
  b65x_loopCentre j + (Complex.I - b65x_loopCentre j) *
    ((Real.cos (2 * Real.pi * s) : ℂ) + (Real.sin (2 * Real.pi * s) : ℂ) * Complex.I)

example (s : ℝ) : (b65x_loopFun 0 s).re = 5 - 5 * Real.cos (2 * Real.pi * s) ∧
    (b65x_loopFun 0 s).im = 1 - 5 * Real.sin (2 * Real.pi * s) := by
  unfold b65x_loopFun
  generalize Real.cos (2 * Real.pi * s) = c
  generalize Real.sin (2 * Real.pi * s) = d
  simp [b65x_loopCentre]
  constructor <;> ring

/-- The three circles as based downstairs loops at `i`; each avoids 0, 5 and minus seven.
Source: elementary plane geometry; `b65x_loopFun`. -/
def b65x_cutLoop (j : Fin 3) : Path b65x_upper b65x_upper where
  toFun s := ⟨b65x_loopFun j s, by
    have hsc := Real.sin_sq_add_cos_sq (2 * Real.pi * s)
    have hc := Real.cos_le_one (2 * Real.pi * s)
    have hs := Real.neg_one_le_sin (2 * Real.pi * s)
    have hs' := Real.sin_le_one (2 * Real.pi * s)
    unfold b65x_loopFun
    generalize Real.cos (2 * Real.pi * s) = c at *
    generalize Real.sin (2 * Real.pi * s) = d at *
    refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩ <;>
    · have hr := congrArg Complex.re h
      have hi := congrArg Complex.im h
      fin_cases j <;> simp [b65x_loopCentre] at hr hi <;> nlinarith⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    unfold b65x_loopFun
    fun_prop
  source' := by
    apply Subtype.ext
    simp [b65x_loopFun, b65x_upper]
  target' := by
    apply Subtype.ext
    simp [b65x_loopFun, b65x_upper]

example (j : Fin 3) : b65x_cutLoop j 0 = b65x_upper := (b65x_cutLoop j).source

/-- Rational parametrization of the unit circle, `e(t) = ((1 - t²) + 2 i t) / (1 + t²)`.
Source: B65-BRAIDCERT checker D, et; JSON pieces_note. -/
def b65x_et (t : ℝ) : ℂ :=
  (((1 - t ^ 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) / ((1 + t ^ 2 : ℝ) : ℂ)

example : b65x_et 0 = 1 := by simp [b65x_et]

/-- Centre of the circle of the `i`-th column trace: the outer centre for `i = 0`, else the
rational disc centre at final label `12 - i`, as in `b65b_lasso`.
Source: B65-BRAIDCERT JSON, lasso_discs and base_point; `b65b_lasso`. -/
def b65x_centre (i : Fin 13) : ℂ :=
  if hi : i.val = 0 then mr_centre else b65b_track 0 ⟨13 - i.val - 1, by omega⟩

example : b65x_centre 0 = -11 / 2 := by simp [b65x_centre, mr_centre]

/-- Radius of the circle of the `i`-th column trace: 10 for the outer loop, else the
rational lasso radius.
Source: B65-BRAIDCERT JSON, lasso_discs; `b65b_lasso`. -/
def b65x_radius (i : Fin 13) : ℝ :=
  if hi : i.val = 0 then 10 else (b65b_radius ⟨13 - i.val - 1, by omega⟩ : ℝ)

example : b65x_radius 0 = 10 := by simp [b65x_radius]

/-- Every radius is positive, so no circle is degenerate.
Source: `b65b_radius`. -/
example : ∀ i, 0 < b65x_radius i := by
  intro i
  fin_cases i <;> norm_num [b65x_radius, b65b_radius]

/-- The three rational pieces of the `i`-th trace, in checker D's forward parameter:
`k = 0` the segment from the base point to the top of the circle (`t ∈ [0, 1]`), `k = 1` the
arc `c - r e(t)` from the top by the left to the bottom, `k = 2` the arc `c + r e(t)` from the
bottom by the right to the top (`t ∈ [-1, 1]`). For `i = 0` the segment piece is constant.
Source: B65-BRAIDCERT checker D, lasso_word, word_piece and OW; JSON pieces_note. -/
def b65x_piece (i : Fin 13) (k : Fin 3) (t : ℝ) : ℂ :=
  ![mr_basePoint + (t : ℂ) *
      (b65x_centre i + Complex.I * (b65x_radius i : ℂ) - mr_basePoint),
    b65x_centre i - (b65x_radius i : ℂ) * b65x_et t,
    b65x_centre i + (b65x_radius i : ℂ) * b65x_et t] k

example (i : Fin 13) : b65x_piece i 0 0 = mr_basePoint := by simp [b65x_piece]

example (i : Fin 13) : b65x_piece i 2 0 = b65x_centre i + (b65x_radius i : ℂ) := by
  simp [b65x_piece, b65x_et]

/-- Parameter domain of a rational piece.
Source: B65-BRAIDCERT checker D, lasso_word. -/
def b65x_dom (k : Fin 3) : Set ℝ :=
  if k = 0 then Set.Icc 0 1 else Set.Icc (-1) 1

example : (-1 : ℝ) ∈ b65x_dom 1 := by norm_num [b65x_dom]
example : (-1 : ℝ) ∉ b65x_dom 0 := by norm_num [b65x_dom]

/-- The downstairs curve `z(t) = φ(M⁻¹(γ(t)))` of a rational piece.
Source: B65-BRAIDCERT checker D, zof. -/
def b65x_down (i : Fin 13) (k : Fin 3) (t : ℝ) : ℂ :=
  b65r_phi (b65b_inverseNormalization (b65x_piece i k t))

example (i : Fin 13) :
    b65x_down i 0 0 = b65r_phi (b65b_inverseNormalization mr_basePoint) := by
  simp [b65x_down, b65x_piece]

/-- One certified crossing of a rational piece: the cut, a rational isolating interval
and the direction (`1` left to right, `-1` right to left).
Source: B65-BRAIDCERT JSON, lasso_words.*.pieces.crossings. -/
structure b65x_Crossing where
  cut : Fin 3
  lo : ℚ
  hi : ℚ
  dir : ℤ

example : (⟨2, 3/4, 7/8, -1⟩ : b65x_Crossing).dir = -1 := rfl

/-- Crossing table by column index `i` (final label `12 - i`, outer loop at `0`) and forward
piece `k`. For the outer loop, piece 1 is the JSON arc `-11/2 - 10 e(t)` and piece 2 the
arc `-11/2 + 10 e(t)`.
Source: B65-BRAIDCERT JSON, lasso_words and outer_loop; intervals checked exactly by
Sturm counts (docs/specs/BraidBridges.md, falsification checks). -/
def b65x_crossings : Fin 13 → Fin 3 → List b65x_Crossing :=
  ![![[], [⟨2, (-3/4), (-1/2), -1⟩], [⟨2, (-1/4), (-1/8), -1⟩]],
    ![[], [⟨1, (127/128), (255/256), 1⟩], []],
    ![[⟨2, (34/35), (35/36), -1⟩], [], [⟨0, (-255/256), (-127/128), 1⟩]],
    ![[], [⟨0, (0), (1/2), 1⟩], []],
    ![[⟨2, (63/64), (127/128), -1⟩], [], [⟨1, (3/4), (7/8), 1⟩]],
    ![[⟨2, (23/24), (24/25), -1⟩, ⟨2, (81/82), (163/164), -1⟩,
        ⟨1, (24575/24576), (49151/49152), -1⟩], [⟨1, (-15/16), (-7/8), 1⟩], []],
    ![[⟨2, (11/12), (12/13), -1⟩, ⟨2, (16/17), (17/18), -1⟩], [],
      [⟨0, (-1/2), (0), 1⟩]],
    ![[], [⟨0, (-3/4), (-1/2), 1⟩], []],
    ![[⟨0, (24/25), (25/26), 1⟩], [], [⟨1, (-7/8), (-3/4), 1⟩]],
    ![[⟨0, (18/19), (19/20), 1⟩, ⟨1, (115/116), (921/928), 1⟩, ⟨2, (779/784), (195/196), 1⟩,
        ⟨0, (332/333), (333/334), 1⟩, ⟨0, (684031/684032), (1368063/1368064), -1⟩],
      [⟨0, (-127/128), (-63/64), 1⟩], []],
    ![[⟨0, (15/16), (16/17), 1⟩, ⟨1, (6497/6612), (57/58), 1⟩,
        ⟨2, (6727/6844), (26909/27376), 1⟩, ⟨0, (13455/13688), (58/59), 1⟩],
      [⟨1, (3/4), (7/8), 1⟩], []],
    ![[⟨2, (16/17), (577/612), -1⟩, ⟨1, (17/18), (647/684), -1⟩], [],
      [⟨0, (1/2), (3/4), 1⟩]],
    ![[⟨2, (3/4), (7/8), -1⟩], [], [⟨1, (127/128), (255/256), 1⟩]]]

example : (b65x_crossings 9 0).length = 5 := rfl

/-- Chronological letters of a crossing list.
Source: B65-BRAIDCERT checker D, cross_piece output. -/
def b65x_letters (L : List b65x_Crossing) : List (Fin 3 × ℤ) :=
  L.map (fun c ↦ (c.cut, c.dir))

example : b65x_letters [⟨1, 0, 1, 1⟩] = [(1, 1)] := rfl

/-- Letters of a piece traversed backwards: reversed order, inverted directions.
Source: B65-BRAIDCERT checker D, word_piece with rev. -/
def b65x_back (w : List (Fin 3 × ℤ)) : List (Fin 3 × ℤ) :=
  w.reverse.map (fun a ↦ (a.1, -a.2))

example : b65x_back [(0, 1), (2, -1)] = [(2, 1), (0, -1)] := rfl

/-- Unreduced chronological crossing word of the `i`-th column trace: segment, both arcs and
the segment back; for the outer loop, the two arcs backwards.
Source: B65-BRAIDCERT checker D, lasso_word and OW before freered. -/
def b65x_rawWord (i : Fin 13) : List (Fin 3 × ℤ) :=
  if i = 0 then
    b65x_back (b65x_letters (b65x_crossings 0 2)) ++
      b65x_back (b65x_letters (b65x_crossings 0 1))
  else
    b65x_letters (b65x_crossings i 0) ++ b65x_letters (b65x_crossings i 1) ++
      b65x_letters (b65x_crossings i 2) ++ b65x_back (b65x_letters (b65x_crossings i 0))

example : b65x_rawWord 0 = [(2, 1), (2, 1)] := by decide
example : b65x_rawWord 2 = [(2, -1), (0, 1), (2, 1)] := by decide

/-- Column index of `b65b_lasso` for each counterclockwise slot of `b65b_initialWords`.
Slots 2, 3, 4 hold labels 4, 10, p10, which sit at column indices 3, 4, 2.
Source: B65-BRAIDCERT JSON, ccw_order_initial and path.vertices label order. -/
def b65x_slot : Fin 13 → Fin 13 := ![0, 1, 3, 4, 2, 5, 6, 7, 8, 9, 10, 11, 12]

example : Function.Bijective b65x_slot := by decide
example : b65x_slot 4 = 2 := rfl

/-- Dot product of final-mark directions from the base point.
Source: B65-BRAIDCERT checker C, coneok on MARKS. -/
def b65x_markDot (i j : Fin 12) : ℚ :=
  ((b65b_vertex1 i).1 + 11/2) * ((b65b_vertex1 j).1 + 11/2) +
    ((b65b_vertex1 i).2 - 10) * ((b65b_vertex1 j).2 - 10)

example : b65x_markDot 0 0 = (13/2)^2 + 100 := by norm_num [b65x_markDot, b65b_vertex1]

/-- Signed area of two final-mark directions from the base point.
Source: B65-BRAIDCERT checker C, coneok on MARKS. -/
def b65x_markCross (i j : Fin 12) : ℚ :=
  ((b65b_vertex1 i).1 + 11/2) * ((b65b_vertex1 j).2 - 10) -
    ((b65b_vertex1 i).2 - 10) * ((b65b_vertex1 j).1 + 11/2)

example : b65x_markCross 0 1 = 10 := by norm_num [b65x_markCross, b65b_vertex1]

end HodgeLean.Foundations.Program

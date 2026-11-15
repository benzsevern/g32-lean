import HodgeLean.Foundations.Program.BraidBridgesProofs

/-! # Braid-certificate bridges, stage one

Six statements toward the crossing-class and path-lasso bridges of
docs/specs/BraidCertificate.md:

* the rational semicircles and segments of checker D reparametrize `b65b_lasso`;
* every rational piece stays in `b65s_regular` and avoids source infinity;
* the exact crossing intervals of every rational piece with the three cuts;
* the cut-system lemma: a loop with a given signed crossing sequence represents the
  corresponding word in any once-crossing generators;
* the raw crossing words reduce to `b65b_initialWords` after the slot permutation;
* the final marks with radius 1/4 are cone-separated inside the outer circle.

Implication from explicit rational data and plane topology to based-class identities.
Not claimed: the assembled crossing words of the column traces, the downstairs
marking, the extension over apparent points, the moving-lasso family and the two
positive moves. These later stages are listed in docs/specs/BraidBridges.md.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- The segment and semicircle pieces of checker D trace `b65b_lasso` after an explicit
monotone change of parameter: `e(t) = exp(2 i arctan t)`.
Source: B65-BRAIDCERT checker D, lasso_word, et and OW; `b65b_lasso`, `mr_outer`. -/
theorem b65x_lasso_pieces :
    (∀ i : Fin 13, i ≠ 0 → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      b65b_lasso i (t / 3) = b65x_piece i 0 t ∧
        b65b_lasso i (1 - t / 3) = b65x_piece i 0 t) ∧
    (∀ i : Fin 13, i ≠ 0 → ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      b65b_lasso i ((5/4 + Real.arctan t / Real.pi) / 3) = b65x_piece i 1 t ∧
        b65b_lasso i ((7/4 + Real.arctan t / Real.pi) / 3) = b65x_piece i 2 t) ∧
    (∀ t ∈ Set.Icc (-1 : ℝ) 1,
      b65b_lasso 0 (1/4 - Real.arctan t / Real.pi) = b65x_piece 0 2 t ∧
        b65b_lasso 0 (3/4 - Real.arctan t / Real.pi) = b65x_piece 0 1 t) :=
  b65x_lasso_pieces_aux

example (i : Fin 13) (hi : i ≠ 0) :
    b65b_lasso i ((5/4 + Real.arctan 0 / Real.pi) / 3) = b65x_piece i 1 0 :=
  (b65x_lasso_pieces.2.1 i hi 0 (by norm_num)).1

/-- Every rational piece avoids the pole of the inverse normalization, the apparent poles
and the preimages of the branch values.
Source: B65-BRAIDCERT checker D, cross_piece pole and branch-value tests; G32 v0.16, §5.4. -/
theorem b65x_piece_regular :
    ∀ (i : Fin 13) (k : Fin 3), ∀ t ∈ b65x_dom k,
      ((b65b_boxCentre 6).1 : ℂ) - b65x_piece i k t *
          (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
        b65b_inverseNormalization (b65x_piece i k t) ∈ b65s_regular :=
  b65x_piece_regular_aux

example : b65b_inverseNormalization mr_basePoint ∈ b65s_regular := by
  simpa [b65x_piece] using (b65x_piece_regular 1 0 0 (by norm_num [b65x_dom])).2

/-- Certified crossings of each rational piece with the downward cuts: ordered disjoint
rational intervals, each with negative imaginary part, exactly one root of the real-part
equation and the recorded endpoint signs, and no cut point outside them.
Source: B65-BRAIDCERT checker D, cross_piece and isol (Sturm isolation of
`Re(U conj V) - a |V|²`); JSON lasso_words and outer_loop. -/
theorem b65x_piece_crossings (i : Fin 13) (k : Fin 3) :
    (∀ m m' : Fin (b65x_crossings i k).length, m < m' →
      (b65x_crossings i k)[m].hi < (b65x_crossings i k)[m'].lo) ∧
    (∀ c ∈ b65x_crossings i k,
      (c.lo : ℝ) ∈ b65x_dom k ∧ (c.hi : ℝ) ∈ b65x_dom k ∧ c.lo < c.hi ∧
      (c.dir = 1 ∨ c.dir = -1) ∧
      (∀ t ∈ Set.Icc (c.lo : ℝ) c.hi, (b65x_down i k t).im < 0) ∧
      (∃! t, t ∈ Set.Icc (c.lo : ℝ) c.hi ∧
        (b65x_down i k t).re = b65x_cutPoint c.cut) ∧
      (c.dir : ℝ) * ((b65x_down i k c.lo).re - b65x_cutPoint c.cut) < 0 ∧
      0 < (c.dir : ℝ) * ((b65x_down i k c.hi).re - b65x_cutPoint c.cut)) ∧
    ∀ t ∈ b65x_dom k, ∀ j : Fin 3, b65x_OnCut j (b65x_down i k t) →
      ∃ c ∈ b65x_crossings i k, c.cut = j ∧ t ∈ Set.Icc (c.lo : ℝ) c.hi :=
  b65x_piece_crossings_aux i k

/-- The segment of the lasso around label 1 crosses the cut from 5 near its end. -/
example : ∃ t ∈ Set.Icc ((684031/684032 : ℚ) : ℝ) ((1368063/1368064 : ℚ) : ℝ),
    (b65x_down 9 0 t).re = 5 := by
  obtain ⟨-, h, -⟩ := b65x_piece_crossings 9 0
  obtain ⟨-, -, -, -, -, ⟨t, ⟨ht, hre⟩, -⟩, -, -⟩ :=
    h ⟨0, 684031/684032, 1368063/1368064, -1⟩ (by simp [b65x_crossings])
  exact ⟨t, ht, by simpa [b65x_cutPoint] using hre⟩

/-- Cut-system lemma: in the three-punctured plane, a based loop whose crossings with the
downward rays from 5, minus seven and zero form the chronological signed word `w`
represents the reversed product of the once-crossing generators. The reversal matches
`fromPath (p.trans q) = fromPath q * fromPath p`.
Source: Hatcher, Algebraic Topology, §1.2 (van Kampen; the plane slit along the three rays
is contractible); Völklein, Groups as Galois Groups, Ch. 9 (cut systems and standard
generators). -/
theorem b65x_cut_word {y : b65x_Down} (g : Fin 3 → Path y y)
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)])
    (d : Path y y) (w : List (Fin 3 × ℤ)) (hd : b65x_CrossesAs d w) :
    FundamentalGroup.fromPath ⟦d⟧ =
      (w.reverse.map (fun a ↦ FundamentalGroup.fromPath ⟦g a.1⟧ ^ a.2)).prod :=
  b65x_cut_word_aux g hg d w hd

example {y : b65x_Down} (g : Fin 3 → Path y y)
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)]) (d : Path y y)
    (hd : b65x_CrossesAs d []) :
    FundamentalGroup.fromPath ⟦d⟧ = 1 := by
  simpa using b65x_cut_word g hg d [] hd

/-- Non-vacuity of the hypothesis `hg` of `b65x_cut_word`: the circles `b65x_cutLoop j` through
`i` each cross exactly one cut, cut `j`, exactly once and from left to right, so the cut-word
statement applies to them.
Source: `b65x_cutLoop`; elementary trigonometry. -/
example (d : Path b65x_upper b65x_upper) (w : List (Fin 3 × ℤ)) (hd : b65x_CrossesAs d w) :
    FundamentalGroup.fromPath ⟦d⟧ =
      (w.reverse.map (fun a ↦ FundamentalGroup.fromPath ⟦b65x_cutLoop a.1⟧ ^ a.2)).prod := by
  have hg : ∀ j, b65x_CrossesAs (b65x_cutLoop j) [(j, 1)] := by
    have hre : ∀ j (s : unitInterval), ((b65x_cutLoop j s : b65x_Down) : ℂ).re =
        ![5 - 5 * Real.cos (2 * Real.pi * s), -7 + 7 * Real.cos (2 * Real.pi * s),
          -Real.sin (2 * Real.pi * s)] j ∧
        ((b65x_cutLoop j s : b65x_Down) : ℂ).im =
        ![1 - 5 * Real.sin (2 * Real.pi * s), 1 + 7 * Real.sin (2 * Real.pi * s),
          Real.cos (2 * Real.pi * s)] j := by
      intro j s
      change (b65x_loopFun j s).re = _ ∧ (b65x_loopFun j s).im = _
      unfold b65x_loopFun
      generalize Real.cos (2 * Real.pi * s) = c
      generalize Real.sin (2 * Real.pi * s) = d
      fin_cases j <;> constructor <;> simp [b65x_loopCentre] <;> ring
    have hcos0 : ∀ x, 0 ≤ x → x ≤ 2 * Real.pi → Real.cos x = 0 →
        x = Real.pi / 2 ∨ x = 3 * Real.pi / 2 := by
      intro x h0 h1 hx
      obtain ⟨n, rfl⟩ := Real.cos_eq_zero_iff.1 hx
      have hpi := Real.pi_pos
      have hn0 : (-1 : ℝ) < n := by nlinarith
      have hn1 : (n : ℝ) < 2 := by nlinarith
      have : n = 0 ∨ n = 1 := by
        have : (-1 : ℤ) < n := by exact_mod_cast hn0
        have : n < (2 : ℤ) := by exact_mod_cast hn1
        omega
      rcases this with rfl | rfl
      · left; push_cast; ring
      · right; push_cast; ring
    have hsin0 : ∀ x, 0 ≤ x → x ≤ 2 * Real.pi → Real.sin x = 0 →
        x = 0 ∨ x = Real.pi ∨ x = 2 * Real.pi := by
      intro x h0 h1 hx
      obtain ⟨n, rfl⟩ := Real.sin_eq_zero_iff.1 hx
      have hpi := Real.pi_pos
      have hn0 : (-1 : ℝ) < n := by nlinarith
      have hn1 : (n : ℝ) < 3 := by nlinarith
      have : n = 0 ∨ n = 1 ∨ n = 2 := by
        have : (-1 : ℤ) < n := by exact_mod_cast hn0
        have : n < (3 : ℤ) := by exact_mod_cast hn1
        omega
      rcases this with rfl | rfl | rfl
      · left; simp
      · right; left; simp
      · right; right; push_cast; ring
    have hpi := Real.pi_pos
    have hθ : ∀ s : unitInterval, 0 ≤ 2 * Real.pi * s ∧ 2 * Real.pi * s ≤ 2 * Real.pi := by
      intro s
      have := s.2.1
      have := s.2.2
      constructor <;> nlinarith
    have hsc : ∀ s : unitInterval,
        Real.sin (2 * Real.pi * s) ^ 2 + Real.cos (2 * Real.pi * s) ^ 2 = 1 :=
      fun s ↦ Real.sin_sq_add_cos_sq _
    have h0 : b65x_CrossesAs (b65x_cutLoop 0) [(0, 1)] := by
      refine ⟨fun _ ↦ ⟨1/4, by norm_num, by norm_num⟩, fun a b h ↦ ?_, fun _ ↦ ?_,
        fun _ ↦ Or.inl (by simp), ?_, 1/4, by norm_num, ?_⟩
      · exact absurd h (by simp [Fin.lt_def])
      · norm_num
      · intro k s
        obtain ⟨hr, hi⟩ := hre 0 s
        obtain ⟨h0, h1⟩ := hθ s
        have := hsc s
        have hcl := Real.cos_le_one (2 * Real.pi * s)
        simp only [Fin.isValue, Matrix.cons_val_zero] at hr hi
        fin_cases k <;> simp [b65x_OnCut, b65x_cutPoint, hr, hi, Subtype.ext_iff]
        · constructor
          · rintro ⟨hc, hs⟩
            have hc : Real.cos (2 * Real.pi * s) = 0 := by linarith
            rcases hcos0 _ h0 h1 hc with h | h
            · nlinarith
            · have : Real.sin (2 * Real.pi * s) = -1 := by
                rw [h, show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
                  Real.sin_pi_div_two]
              linarith
          · intro h
            rw [h, show 2 * Real.pi * 4⁻¹ = Real.pi / 2 by ring, Real.cos_pi_div_two,
              Real.sin_pi_div_two]
            norm_num
        · intro h; linarith
        · intro h
          have hc : Real.cos (2 * Real.pi * s) = 1 := by linarith
          nlinarith
      · intro m s hs
        simp only [Fin.getElem_fin, List.getElem_singleton]
        obtain ⟨hr, -⟩ := hre 0 s
        simp only [Fin.isValue, Matrix.cons_val_zero] at hr
        change |(s : ℝ) - 1/4| < 1/4 at hs
        have hs' := abs_lt.1 hs
        obtain ⟨h0, h1⟩ := hθ s
        simp only [b65x_cutPoint, Fin.isValue, Matrix.cons_val_zero, Int.cast_one, one_mul, hr]
        constructor
        · intro hlt
          have := Real.cos_pos_of_mem_Ioo (x := 2 * Real.pi * s) ⟨by nlinarith, by nlinarith⟩
          linarith
        · intro hlt
          have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 2 * Real.pi * s) (by nlinarith)
            (by nlinarith)
          linarith
    have h1 : b65x_CrossesAs (b65x_cutLoop 1) [(1, 1)] := by
      refine ⟨fun _ ↦ ⟨3/4, by norm_num, by norm_num⟩, fun a b h ↦ ?_, fun _ ↦ ?_,
        fun _ ↦ Or.inl (by simp), ?_, 1/4, by norm_num, ?_⟩
      · exact absurd h (by simp [Fin.lt_def])
      · norm_num
      · intro k s
        obtain ⟨hr, hi⟩ := hre 1 s
        obtain ⟨h0, h1⟩ := hθ s
        have := hsc s
        have hcl := Real.cos_le_one (2 * Real.pi * s)
        simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at hr hi
        fin_cases k <;> simp [b65x_OnCut, b65x_cutPoint, hr, hi, Subtype.ext_iff]
        · intro h; linarith
        · constructor
          · rintro ⟨hc, hs⟩
            have hc : Real.cos (2 * Real.pi * s) = 0 := by linarith
            rcases hcos0 _ h0 h1 hc with h | h
            · rw [h, Real.sin_pi_div_two] at hs
              linarith
            · nlinarith
          · intro h
            rw [h, show 2 * Real.pi * (3 / 4) = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
              Real.sin_add_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
            norm_num
        · intro h
          have hc : Real.cos (2 * Real.pi * s) = 1 := by linarith
          nlinarith
      · intro m s hs
        simp only [Fin.getElem_fin, List.getElem_singleton]
        obtain ⟨hr, -⟩ := hre 1 s
        simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at hr
        change |(s : ℝ) - 3/4| < 1/4 at hs
        have hs' := abs_lt.1 hs
        obtain ⟨h0, h1⟩ := hθ s
        simp only [b65x_cutPoint, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
          Int.cast_one, one_mul, hr]
        constructor
        · intro hlt
          have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 2 * Real.pi * s) (by nlinarith)
            (by nlinarith)
          linarith
        · intro hlt
          have := Real.cos_pos_of_mem_Ioo (x := 2 * Real.pi * s - 2 * Real.pi)
            ⟨by nlinarith, by nlinarith⟩
          rw [Real.cos_sub_two_pi] at this
          linarith
    have h2 : b65x_CrossesAs (b65x_cutLoop 2) [(2, 1)] := by
      refine ⟨fun _ ↦ ⟨1/2, by norm_num, by norm_num⟩, fun a b h ↦ ?_, fun _ ↦ ?_,
        fun _ ↦ Or.inl (by simp), ?_, 1/4, by norm_num, ?_⟩
      · exact absurd h (by simp [Fin.lt_def])
      · norm_num
      · intro k s
        obtain ⟨hr, hi⟩ := hre 2 s
        obtain ⟨h0, h1⟩ := hθ s
        have := hsc s
        have hsl := Real.sin_le_one (2 * Real.pi * s)
        have hsl' := Real.neg_one_le_sin (2 * Real.pi * s)
        simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hr hi
        fin_cases k <;> simp [b65x_OnCut, b65x_cutPoint, hr, hi, Subtype.ext_iff]
        · intro h; linarith
        · intro h; linarith
        · constructor
          · rintro ⟨hs, hc⟩
            rcases hsin0 _ h0 h1 hs with h | h | h
            · rw [h, Real.cos_zero] at hc; norm_num at hc
            · nlinarith
            · rw [h, Real.cos_two_pi] at hc; norm_num at hc
          · intro h
            rw [h, show 2 * Real.pi * 2⁻¹ = Real.pi by ring, Real.sin_pi, Real.cos_pi]
            norm_num
      · intro m s hs
        simp only [Fin.getElem_fin, List.getElem_singleton]
        obtain ⟨hr, -⟩ := hre 2 s
        simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hr
        change |(s : ℝ) - 1/2| < 1/4 at hs
        have hs' := abs_lt.1 hs
        simp only [b65x_cutPoint, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons, Int.cast_one, one_mul, sub_zero, hr]
        constructor
        · intro hlt
          have := Real.sin_pos_of_pos_of_lt_pi (x := 2 * Real.pi * s) (by nlinarith)
            (by nlinarith)
          linarith
        · intro hlt
          have := Real.sin_pos_of_pos_of_lt_pi (x := 2 * Real.pi * s - Real.pi) (by nlinarith)
            (by nlinarith)
          rw [Real.sin_sub_pi] at this
          linarith
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  exact b65x_cut_word b65x_cutLoop hg d w hd

/-- The unreduced crossing word of column trace `b65x_slot i` and the literal initial word
of slot `i` have equal products in every group.
Source: B65-BRAIDCERT checker D, freered; JSON ccw_order_initial and lasso_words. -/
theorem b65x_raw_reduction {G : Type*} [Group G] (D : Fin 3 → G) (i : Fin 13) :
    ((b65x_rawWord (b65x_slot i)).reverse.map (fun a ↦ D a.1 ^ a.2)).prod =
      ((b65b_initialWords i).reverse.map (fun a ↦ D a.1 ^ a.2)).prod :=
  b65x_raw_reduction_aux D i

example (D : Fin 3 → Multiplicative ℤ) :
    ((b65x_rawWord (b65x_slot 4)).reverse.map (fun a ↦ D a.1 ^ a.2)).prod =
      ((b65b_initialWords 4).reverse.map (fun a ↦ D a.1 ^ a.2)).prod :=
  b65x_raw_reduction D 4

/-- The raw-word check detects conjugation errors: in the free group on the three cut
letters, the unpermuted raw word of column index 2 (the lasso around p10, class `D₂ D₀ D₂⁻¹`)
differs from `b65b_initialWords 2` (class `D₀`). The `Multiplicative ℤ` example cannot see
this.
Source: defect 1 of docs/specs/BraidBridges.md; B65-BRAIDCERT JSON, ccw_order_initial. -/
example :
    ((b65x_rawWord 2).reverse.map (fun a ↦ (FreeGroup.of a.1 : FreeGroup (Fin 3)) ^ a.2)).prod ≠
      ((b65b_initialWords 2).reverse.map
        (fun a ↦ (FreeGroup.of a.1 : FreeGroup (Fin 3)) ^ a.2)).prod := by
  decide

/-- The raw-word check detects product-order errors: in the free group, the reversed product of
the raw word of column index 2 differs from its chronological product.
Source: `fromPath (p.trans q) = fromPath q * fromPath p`; `b65b_eval`. -/
example :
    ((b65x_rawWord 2).reverse.map (fun a ↦ (FreeGroup.of a.1 : FreeGroup (Fin 3)) ^ a.2)).prod ≠
      ((b65x_rawWord 2).map (fun a ↦ (FreeGroup.of a.1 : FreeGroup (Fin 3)) ^ a.2)).prod := by
  decide

/-- With the slot permutation, slot 4 carries column index 2 and the reduction holds in the
free group, where only free cancellation is available.
Source: `b65x_raw_reduction`. -/
example :
    ((b65x_rawWord (b65x_slot 4)).reverse.map
        (fun a ↦ (FreeGroup.of a.1 : FreeGroup (Fin 3)) ^ a.2)).prod =
      ((b65b_initialWords 4).reverse.map
        (fun a ↦ (FreeGroup.of a.1 : FreeGroup (Fin 3)) ^ a.2)).prod :=
  b65x_raw_reduction FreeGroup.of 4

/-- The final marks are the rational path endpoints, lie well inside the outer circle,
and their discs of radius 1/4 have disjoint cones from the base point.
Source: B65-BRAIDCERT checker C, MARKS and coneok; `mr_marks`, `mr_lasso`. -/
theorem b65x_final_marks :
    (∀ j : Fin 12, mr_marks j =
      ((b65b_vertex1 j).1 : ℂ) + ((b65b_vertex1 j).2 : ℂ) * Complex.I) ∧
    (∀ j : Fin 12, ((b65b_vertex1 j).1 + 11/2) ^ 2 + (b65b_vertex1 j).2 ^ 2 <
      (10 - 1/4 : ℚ) ^ 2) ∧
    ∀ i j : Fin 12, i < j →
      0 < b65x_markDot i j ∧
      (b65x_markCross i j) ^ 2 > (1/4 : ℚ) ^ 2 * b65x_markDot j j +
        (1/4 : ℚ) ^ 2 * b65x_markDot i i +
        (1/4 : ℚ) * (1/4) * (b65x_markDot i i + b65x_markDot j j) :=
  b65x_final_marks_aux

example : 0 < b65x_markDot 0 11 := (b65x_final_marks.2.2 0 11 (by decide)).1

/-- Chain check toward the crossing-class field: once the column trace in slot `i` has its
raw crossing word, any marking sending the generators to `b65b_cut` sends its class to
`b65b_initial i`, the value used to derive `b65b_transported_identification`.
Source: `b65x_cut_word`, `b65x_raw_reduction`; the archived derivation in
docs/specs/BraidCertificate.md. -/
example {y : b65x_Down} (g : Fin 3 → Path y y)
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)])
    (κ : FundamentalGroup b65x_Down y →* b4b_Group)
    (hκ : ∀ j, κ (FundamentalGroup.fromPath ⟦g j⟧) = b65b_cut j)
    (i : Fin 13) (d : Path y y) (hd : b65x_CrossesAs d (b65x_rawWord (b65x_slot i))) :
    κ (FundamentalGroup.fromPath ⟦d⟧) = b65b_initial i := by
  rw [b65x_cut_word g hg d _ hd, map_list_prod, List.map_map]
  have hfun : (⇑κ ∘ fun a : Fin 3 × ℤ ↦ FundamentalGroup.fromPath ⟦g a.1⟧ ^ a.2) =
      fun a ↦ b65b_cut a.1 ^ a.2 := by
    funext a
    change κ (FundamentalGroup.fromPath ⟦g a.1⟧ ^ a.2) = _
    rw [map_zpow, hκ]
  rw [hfun, b65x_raw_reduction b65b_cut i]
  rfl

/-- Chain check toward the trace field `δ` of the crossing-class bridge: the segment part of
every column trace lies in the regular plane.
Source: `b65x_lasso_pieces`, `b65x_piece_regular`. -/
example (i : Fin 13) (hi : i ≠ 0) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    b65b_inverseNormalization (b65b_lasso i (t / 3)) ∈ b65s_regular := by
  rw [(b65x_lasso_pieces.1 i hi t ht).1]
  exact (b65x_piece_regular i 0 t (by simpa [b65x_dom] using ht)).2

end HodgeLean.Foundations.Program

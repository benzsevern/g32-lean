import HodgeLean.Foundations.Program.BraidBridgesCutProofs
import HodgeLean.Foundations.Program.BraidBridgesLassoProofs
import HodgeLean.Foundations.Program.BraidBridgesCrossingConstant

/-! # Braid-certificate bridges, first stage: proofs. -/

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65x_lasso_pieces_aux :
    (∀ i : Fin 13, i ≠ 0 → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      b65b_lasso i (t / 3) = b65x_piece i 0 t ∧
        b65b_lasso i (1 - t / 3) = b65x_piece i 0 t) ∧
    (∀ i : Fin 13, i ≠ 0 → ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      b65b_lasso i ((5/4 + Real.arctan t / Real.pi) / 3) = b65x_piece i 1 t ∧
        b65b_lasso i ((7/4 + Real.arctan t / Real.pi) / 3) = b65x_piece i 2 t) ∧
    (∀ t ∈ Set.Icc (-1 : ℝ) 1,
      b65b_lasso 0 (1/4 - Real.arctan t / Real.pi) = b65x_piece 0 2 t ∧
        b65b_lasso 0 (3/4 - Real.arctan t / Real.pi) = b65x_piece 0 1 t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi t ht
    exact b65x_lasso_segments i hi t ht
  · intro i hi t ht
    obtain ⟨hl, hr⟩ := b65x_arctan_ratio_bounds t ht
    have hm0 : 1/3 ≤ (5/4 + Real.arctan t / Real.pi) / 3 := by linarith
    have hm1 : (5/4 + Real.arctan t / Real.pi) / 3 ≤ 2/3 := by linarith
    have hp0 : 1/3 ≤ (7/4 + Real.arctan t / Real.pi) / 3 := by linarith
    have hp1 : (7/4 + Real.arctan t / Real.pi) / 3 ≤ 2/3 := by linarith
    rw [b65x_lasso_circle i hi _ hm0 hm1, b65x_lasso_circle i hi _ hp0 hp1]
    have hm : (3 * (((5/4 + Real.arctan t / Real.pi) / 3 : ℝ) : ℂ) - 1) =
        ((1/4 + Real.arctan t / Real.pi : ℝ) : ℂ) := by push_cast; ring
    have hp : (3 * (((7/4 + Real.arctan t / Real.pi) / 3 : ℝ) : ℂ) - 1) =
        ((3/4 + Real.arctan t / Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [hm, hp, (b65x_exp_quarters t).1, (b65x_exp_quarters t).2.1]
    constructor
    · change _ = b65x_centre i - (b65x_radius i : ℂ) * b65x_et t
      calc
        _ = b65x_centre i + (Complex.I * Complex.I) *
            (b65x_radius i : ℂ) * b65x_et t := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    · change _ = b65x_centre i + (b65x_radius i : ℂ) * b65x_et t
      calc
        _ = b65x_centre i - (Complex.I * Complex.I) *
            (b65x_radius i : ℂ) * b65x_et t := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
  · intro t ht
    change mr_outer (1/4 - Real.arctan t / Real.pi) =
        b65x_centre 0 + (b65x_radius 0 : ℂ) * b65x_et t ∧
      mr_outer (3/4 - Real.arctan t / Real.pi) =
        b65x_centre 0 - (b65x_radius 0 : ℂ) * b65x_et t
    simp only [mr_outer, b65x_centre, b65x_radius, Fin.val_zero, dite_true,
      Complex.ofReal_ofNat]
    rw [(b65x_exp_quarters t).2.2.1, (b65x_exp_quarters t).2.2.2]
    constructor
    · calc
        _ = mr_centre - 10 * (Complex.I * Complex.I) * b65x_et t := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    · calc
        _ = mr_centre + 10 * (Complex.I * Complex.I) * b65x_et t := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring

theorem b65x_piece_regular_aux :
    ∀ (i : Fin 13) (k : Fin 3), ∀ t ∈ b65x_dom k,
      ((b65b_boxCentre 6).1 : ℂ) - b65x_piece i k t *
          (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 ∧
        b65b_inverseNormalization (b65x_piece i k t) ∈ b65s_regular := by
  intro i k t ht
  fin_cases i <;> fin_cases k
  · exact b65x_piece_regular_0_0 t
  · exact b65x_piece_regular_0_1 t ht
  · exact b65x_piece_regular_0_2 t ht
  · exact b65x_piece_regular_1_0 t ht
  · exact b65x_piece_regular_1_1 t ht
  · exact b65x_piece_regular_1_2 t ht
  · exact b65x_piece_regular_2_0 t ht
  · exact b65x_piece_regular_2_1 t ht
  · exact b65x_piece_regular_2_2 t ht
  · exact b65x_piece_regular_3_0 t ht
  · exact b65x_piece_regular_3_1 t ht
  · exact b65x_piece_regular_3_2 t ht
  · exact b65x_piece_regular_4_0 t ht
  · exact b65x_piece_regular_4_1 t ht
  · exact b65x_piece_regular_4_2 t ht
  · exact b65x_piece_regular_5_0 t ht
  · exact b65x_piece_regular_5_1 t ht
  · exact b65x_piece_regular_5_2 t ht
  · exact b65x_piece_regular_6_0 t ht
  · exact b65x_piece_regular_6_1 t ht
  · exact b65x_piece_regular_6_2 t ht
  · exact b65x_piece_regular_7_0 t ht
  · exact b65x_piece_regular_7_1 t ht
  · exact b65x_piece_regular_7_2 t ht
  · exact b65x_piece_regular_8_0 t ht
  · exact b65x_piece_regular_8_1 t ht
  · exact b65x_piece_regular_8_2 t ht
  · exact b65x_piece_regular_9_0 t ht
  · exact b65x_piece_regular_9_1 t ht
  · exact b65x_piece_regular_9_2 t ht
  · exact b65x_piece_regular_10_0 t ht
  · exact b65x_piece_regular_10_1 t ht
  · exact b65x_piece_regular_10_2 t ht
  · exact b65x_piece_regular_11_0 t ht
  · exact b65x_piece_regular_11_1 t ht
  · exact b65x_piece_regular_11_2 t ht
  · exact b65x_piece_regular_12_0 t ht
  · exact b65x_piece_regular_12_1 t ht
  · exact b65x_piece_regular_12_2 t ht

theorem b65x_piece_crossings_aux (i : Fin 13) (k : Fin 3) :
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
      ∃ c ∈ b65x_crossings i k, c.cut = j ∧ t ∈ Set.Icc (c.lo : ℝ) c.hi := by
  fin_cases i <;> fin_cases k
  · exact b65x_piece_crossings_0_0
  · exact b65x_piece_crossings_0_1
  · exact b65x_piece_crossings_0_2
  · exact b65x_piece_crossings_1_0
  · exact b65x_piece_crossings_1_1
  · exact b65x_piece_crossings_1_2
  · exact b65x_piece_crossings_2_0
  · exact b65x_piece_crossings_2_1
  · exact b65x_piece_crossings_2_2
  · exact b65x_piece_crossings_3_0
  · exact b65x_piece_crossings_3_1
  · exact b65x_piece_crossings_3_2
  · exact b65x_piece_crossings_4_0
  · exact b65x_piece_crossings_4_1
  · exact b65x_piece_crossings_4_2
  · exact b65x_piece_crossings_5_0
  · exact b65x_piece_crossings_5_1
  · exact b65x_piece_crossings_5_2
  · exact b65x_piece_crossings_6_0
  · exact b65x_piece_crossings_6_1
  · exact b65x_piece_crossings_6_2
  · exact b65x_piece_crossings_7_0
  · exact b65x_piece_crossings_7_1
  · exact b65x_piece_crossings_7_2
  · exact b65x_piece_crossings_8_0
  · exact b65x_piece_crossings_8_1
  · exact b65x_piece_crossings_8_2
  · exact b65x_piece_crossings_9_0
  · exact b65x_piece_crossings_9_1
  · exact b65x_piece_crossings_9_2
  · exact b65x_piece_crossings_10_0
  · exact b65x_piece_crossings_10_1
  · exact b65x_piece_crossings_10_2
  · exact b65x_piece_crossings_11_0
  · exact b65x_piece_crossings_11_1
  · exact b65x_piece_crossings_11_2
  · exact b65x_piece_crossings_12_0
  · exact b65x_piece_crossings_12_1
  · exact b65x_piece_crossings_12_2

theorem b65x_cut_word_aux {y : b65x_Down} (g : Fin 3 → Path y y)
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)])
    (d : Path y y) (w : List (Fin 3 × ℤ)) (hd : b65x_CrossesAs d w) :
    FundamentalGroup.fromPath ⟦d⟧ =
      (w.reverse.map (fun a ↦ FundamentalGroup.fromPath ⟦g a.1⟧ ^ a.2)).prod := by
  by_cases hn : 0 < w.length
  · obtain ⟨u, hu, hint, he, hc, ε, hε, hs⟩ := hd
    obtain ⟨t, ht0, ht1, hbound⟩ := b65x_crossing_samples hn u hu hint
    have ht (i : Fin (w.length + 1)) (k : Fin 3) :
        ¬ b65x_OnCut k (d (t i)).val := by
      intro h
      obtain ⟨m, _, hm⟩ := (hc k (t i)).mp h
      have hm' := congrArg Subtype.val hm
      by_cases hi : m.val < i.val
      · have := (hbound i m).1 hi
        linarith
      · have := (hbound i m).2 (by omega)
        linarith
    obtain ⟨a, ha, hfactor⟩ := b65x_finite_based_subpaths d t ht0 ht1 ht
    have hsingle (m : Fin w.length) :
        b65x_CrossesAs ((a m.castSucc).trans
          ((d.subpath (t m.castSucc) (t m.succ)).trans (a m.succ).symm)) [w[m]] := by
      apply b65x_subpath_stemmed_single d w u he hc ε hε hs m
        (t m.castSucc) (t m.succ)
        ((hbound m.castSucc m).2 (by change m.val ≤ m.val; exact le_rfl))
        ((hbound m.succ m).1 (by change m.val < m.val + 1; omega))
        ?_ (a m.castSucc) (a m.succ).symm (ha m.castSucc)
        (fun s k ↦ ha m.succ (unitInterval.symm s) k)
      intro n hl hr
      apply Fin.ext
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := (hbound m.castSucc n).1 hlt
        linarith
      · have := (hbound m.succ n).2 (by change m.val + 1 ≤ n.val; omega)
        linarith
    rw [hfactor]
    have hlist : List.ofFn (fun m : Fin w.length ↦ FundamentalGroup.fromPath
        ⟦(a m.castSucc).trans
          ((d.subpath (t m.castSucc) (t m.succ)).trans (a m.succ).symm)⟧) =
        w.map (fun c ↦ FundamentalGroup.fromPath ⟦g c.1⟧ ^ c.2) := by
      rw [← List.ofFn_getElem_eq_map]
      apply congrArg List.ofFn
      funext m
      exact b65x_single_word_class _ (g w[m].1) w[m].1 w[m].2 (hsingle m) (hg w[m].1)
    rw [hlist, List.map_reverse]
  · have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst w
    simpa using b65x_empty_word d hd

theorem b65x_raw_reduction_aux {G : Type*} [Group G] (D : Fin 3 → G) (i : Fin 13) :
    ((b65x_rawWord (b65x_slot i)).reverse.map (fun a ↦ D a.1 ^ a.2)).prod =
      ((b65b_initialWords i).reverse.map (fun a ↦ D a.1 ^ a.2)).prod := by
  fin_cases i <;>
    norm_num [b65x_rawWord, b65x_slot, b65x_letters, b65x_back, b65x_crossings,
      b65b_initialWords]

theorem b65x_final_marks_aux :
    (∀ j : Fin 12, mr_marks j =
      ((b65b_vertex1 j).1 : ℂ) + ((b65b_vertex1 j).2 : ℂ) * Complex.I) ∧
    (∀ j : Fin 12, ((b65b_vertex1 j).1 + 11/2) ^ 2 + (b65b_vertex1 j).2 ^ 2 <
      (10 - 1/4 : ℚ) ^ 2) ∧
    ∀ i j : Fin 12, i < j →
      0 < b65x_markDot i j ∧
      (b65x_markCross i j) ^ 2 > (1/4 : ℚ) ^ 2 * b65x_markDot j j +
        (1/4 : ℚ) ^ 2 * b65x_markDot i i +
        (1/4 : ℚ) * (1/4) * (b65x_markDot i i + b65x_markDot j j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num [mr_marks, mr_base, b65b_vertex1, Fin.append, Fin.addCases]
  · intro j
    fin_cases j <;> norm_num [b65b_vertex1]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [b65x_markDot, b65x_markCross, b65b_vertex1]

end HodgeLean.Foundations.Program

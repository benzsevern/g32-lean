import HodgeLean.Foundations.Program.PrymParabolicSimplicesDefs

/-! # Plane geometry of the base cells of stage H3b

Coordinates of the edges `e_i`, `f_i`, `h_i` and of the triangles `A_i`, `B_i` at `mr_base`, used
for the step A statements in `PrymParabolicSimplicesProofs.lean`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Complex Convexity

namespace HodgeLean.Foundations.Program

/-! ## Points of the standard simplex -/

theorem hg5_sum3 (a : StdSimplex ℝ (Fin 3)) : a.weights 0 + a.weights 1 + a.weights 2 = 1 := by
  rw [← a.total_of_fintype, Fin.sum_univ_three]

theorem hg5_simplex_ext {a b : StdSimplex ℝ (Fin 3)} (h0 : a.weights 0 = b.weights 0)
    (h1 : a.weights 1 = b.weights 1) (h2 : a.weights 2 = b.weights 2) : a = b := by
  apply StdSimplex.ext
  ext k
  fin_cases k <;> assumption

/-- The point of the standard `2`-simplex with weights `(x, y, z)`. -/
def hg5_pt (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 1) :
    StdSimplex ℝ (Fin 3) where
  weights := Finsupp.equivFunOnFinite.symm ![x, y, z]
  nonneg k := by fin_cases k <;> simpa
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa [Fin.sum_univ_three] using h

@[simp] theorem hg5_pt_w0 (x y z : ℝ) (hx hy hz h) : (hg5_pt x y z hx hy hz h).weights 0 = x := by
  simp [hg5_pt]
@[simp] theorem hg5_pt_w1 (x y z : ℝ) (hx hy hz h) : (hg5_pt x y z hx hy hz h).weights 1 = y := by
  simp [hg5_pt]
@[simp] theorem hg5_pt_w2 (x y z : ℝ) (hx hy hz h) : (hg5_pt x y z hx hy hz h).weights 2 = z := by
  simp [hg5_pt]

theorem hg5_single_w (i k : Fin 3) :
    (StdSimplex.single i : StdSimplex ℝ (Fin 3)).weights k = if i = k then 1 else 0 := by
  simp [StdSimplex.single, Finsupp.single_apply]

theorem hg5_eq_single1 (a : StdSimplex ℝ (Fin 3)) : a = StdSimplex.single 1 ↔ a.weights 1 = 1 := by
  constructor
  · rintro rfl; simp
  · intro h
    have hs := hg5_sum3 a
    have h0 := a.weights_nonneg 0
    have h2 := a.weights_nonneg 2
    apply hg5_simplex_ext <;> simp <;> linarith

/-- Face weights at parameter `t`. -/
theorem hg5_face_w (k : Fin 3) (t : unitInterval) (j : Fin 3) :
    (StdSimplex.map k.succAbove (StdSimplex.homeomorphI.symm t)).weights j =
      if j = k then 0 else if (k = 0 ∧ j = 1) ∨ (k ≠ 0 ∧ j = 0) then 1 - (t : ℝ) else (t : ℝ) := by
  have h := b3Rest2_face_weights t
  fin_cases k <;> fin_cases j <;> simp_all

theorem hg5_face_apply {T : Type} [TopologicalSpace T] (σ : C(StdSimplex ℝ (Fin 3), T))
    (k : Fin 3) (t : unitInterval) :
    hg5_face σ k t = σ (StdSimplex.map k.succAbove (StdSimplex.homeomorphI.symm t)) := rfl

/-! ## The marks -/

theorem hg5_fin13_cases (i : Fin 13) : i.val < 12 ∨ i = 12 := by
  rcases Nat.lt_or_ge i.val 12 with h | h
  · exact Or.inl h
  · exact Or.inr (Fin.ext (by have := i.isLt; simp; omega))

theorem hg5_branch_lt (i : Fin 13) (h : i.val < 12) :
    b6_branch mr_base i = ((hg5_markRe ⟨i.val, h⟩ : ℂ) : OnePoint ℂ) := by
  obtain ⟨i, hi⟩ := i
  simp only at h
  interval_cases i <;>
    simp [b6_branch, mr_base, Fin.append, Fin.addCases, hg5_markRe] <;> norm_num

theorem hg5_branch_12 : b6_branch mr_base 12 = OnePoint.infty := rfl

theorem hg5_mark_iff (z : OnePoint ℂ) :
    z ∈ Set.range (b6_branch mr_base) ↔
      z = OnePoint.infty ∨ ∃ j : Fin 12, z = ((hg5_markRe j : ℂ) : OnePoint ℂ) := by
  constructor
  · rintro ⟨i, rfl⟩
    rcases hg5_fin13_cases i with h | rfl
    · exact Or.inr ⟨_, hg5_branch_lt i h⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨12, rfl⟩
    · refine ⟨⟨j.val, by omega⟩, ?_⟩
      rw [hg5_branch_lt _ (by simp)]

theorem hg5_coe_mark_iff (w : ℂ) :
    ((w : ℂ) : OnePoint ℂ) ∈ Set.range (b6_branch mr_base) ↔
      w.im = 0 ∧ ∃ j : Fin 12, w.re = hg5_markRe j := by
  rw [hg5_mark_iff]
  constructor
  · rintro (h | ⟨j, h⟩)
    · exact absurd h (OnePoint.coe_ne_infty _)
    · have := OnePoint.coe_injective h
      subst this
      simp
  · rintro ⟨h1, j, h2⟩
    refine Or.inr ⟨j, ?_⟩
    congr 1
    apply Complex.ext <;> simp [h1, h2]

/-! ## Order of waists and marks -/

theorem hg5_waist_lt_mark (i : Fin 13) (j : Fin 12) (h : i.val ≤ j.val) :
    hg3_waist i < hg5_markRe j := by
  revert h
  fin_cases i <;> fin_cases j <;> norm_num [hg3_waist, hg5_markRe]

theorem hg5_mark_lt_waist (i : Fin 13) (j : Fin 12) (h : j.val < i.val) :
    hg5_markRe j < hg3_waist i := by
  revert h
  fin_cases i <;> fin_cases j <;> norm_num [hg3_waist, hg5_markRe]

theorem hg5_markRe_strictMono : StrictMono hg5_markRe := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [hg5_markRe, Fin.lt_def]

theorem hg5_waist_strictMono : StrictMono hg3_waist := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [hg3_waist, Fin.lt_def]

theorem hg5_markRe_injective : Function.Injective hg5_markRe := hg5_markRe_strictMono.injective

theorem hg5_waist_injective : Function.Injective hg3_waist := hg5_waist_strictMono.injective

theorem hg5_waist_ne_mark (i : Fin 13) (j : Fin 12) : hg3_waist i ≠ hg5_markRe j := by
  rcases Nat.lt_or_ge j.val i.val with h | h
  · exact (hg5_mark_lt_waist i j h).ne'
  · exact (hg5_waist_lt_mark i j h).ne

theorem hg5_waist_bounds (i : Fin 13) : -25 / 2 ≤ hg3_waist i ∧ hg3_waist i ≤ 3 / 2 := by
  fin_cases i <;> norm_num [hg3_waist]

theorem hg5_markRe_bounds (j : Fin 12) : -12 ≤ hg5_markRe j ∧ hg5_markRe j ≤ 1 := by
  fin_cases j <;> norm_num [hg5_markRe]

theorem hg5_waist_0 : hg3_waist 0 = -25 / 2 := rfl
theorem hg5_waist_12 : hg3_waist 12 = 3 / 2 := rfl

/-! ## Coordinates of the edges -/

theorem hg5_edgeE_lt (i : Fin 13) (h : i.val < 12) (s : unitInterval) :
    hg5_edgeE i s = (((-11 / 2 + (s : ℝ) * (hg5_markRe ⟨i.val, h⟩ + 11 / 2) : ℝ) : ℂ) +
      ((10 * (1 - (s : ℝ)) : ℝ) : ℂ) * I : ℂ) := by
  simp only [hg5_edgeE, dif_pos h, ContinuousMap.coe_mk]
  congr 1
  apply Complex.ext <;> (simp [mr_basePoint, mr_centre]; try ring_nf; try simp)

theorem hg5_edgeH_lt (i : Fin 13) (h : i.val < 12) (s : unitInterval) :
    hg5_edgeH i s = (((-11 / 2 + (1 - (s : ℝ)) * (hg5_markRe ⟨i.val, h⟩ + 11 / 2) : ℝ) : ℂ) +
      ((-10 * (s : ℝ)) : ℝ) * I : ℂ) := by
  simp only [hg5_edgeH, dif_pos h, ContinuousMap.coe_mk]
  congr 1
  apply Complex.ext <;> (simp [hg3_bottom, mr_centre]; try ring_nf; try simp)

theorem hg5_edgeF_eq (i : Fin 13) (s : unitInterval) :
    hg5_edgeF i s = (((-11 / 2 + (hg3_waist i + 11 / 2) * (1 - |1 - 2 * (s : ℝ)|) : ℝ) : ℂ) +
      ((10 * (1 - 2 * (s : ℝ))) : ℝ) * I : ℂ) := by
  simp only [hg5_edgeF, ContinuousMap.coe_mk]
  congr 1
  apply Complex.ext
  · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero]
    rw [hg3_arc_re, hg3_profile]
    have : |10 - 20 * (s : ℝ)| / 10 = |1 - 2 * (s : ℝ)| := by
      rw [show (10 : ℝ) - 20 * s = 10 * (1 - 2 * s) by ring, abs_mul]; norm_num
    rw [this]; ring
  · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add]
    rw [hg3_arc_im]; ring

theorem hg5_edgeE_12 (s : unitInterval) :
    hg5_edgeE 12 s = hg5_chartInv (-I * (((1 - (s : ℝ)) / 10 : ℝ) : ℂ)) := by
  simp [hg5_edgeE]

theorem hg5_edgeH_12 (s : unitInterval) :
    hg5_edgeH 12 s = hg5_chartInv (I * ((((s : ℝ)) / 10 : ℝ) : ℂ)) := by
  simp [hg5_edgeH]

/-! ## Statement 1: the endpoints -/

theorem hg5_edgeE_zero (i : Fin 13) : hg5_edgeE i 0 = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
  unfold hg5_edgeE
  split_ifs
  · simp
  · simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Set.Icc.coe_zero, sub_zero]
    have h0 : -I * ((((1 : ℝ) / 10 : ℝ)) : ℂ) ≠ 0 := by
      simp [Complex.ext_iff]
    rw [hg5_chartInv_ne h0, mr_basePoint]
    congr 1
    have : (-I * ((((1 : ℝ) / 10 : ℝ)) : ℂ))⁻¹ = 10 * I := by
      rw [mul_inv, inv_neg, Complex.inv_I]; push_cast; ring
    rw [this]

theorem hg5_edgeE_one (i : Fin 13) : hg5_edgeE i 1 = b6_branch mr_base i := by
  rcases hg5_fin13_cases i with h | rfl
  · rw [hg5_edgeE_lt i h, hg5_branch_lt i h]
    congr 1
    apply Complex.ext <;> simp; ring
  · rw [hg5_edgeE_12]; simp [hg5_chartInv_zero, hg5_branch_12]

theorem hg5_edgeH_zero (i : Fin 13) : hg5_edgeH i 0 = b6_branch mr_base i := by
  rcases hg5_fin13_cases i with h | rfl
  · rw [hg5_edgeH_lt i h, hg5_branch_lt i h]
    congr 1
    apply Complex.ext <;> simp; ring
  · rw [hg5_edgeH_12]; simp [hg5_chartInv_zero, hg5_branch_12]

theorem hg5_edgeH_one (i : Fin 13) : hg5_edgeH i 1 = ((hg3_bottom : ℂ) : OnePoint ℂ) := by
  rcases hg5_fin13_cases i with h | rfl
  · rw [hg5_edgeH_lt i h]
    congr 1
    apply Complex.ext <;> simp [hg3_bottom, mr_centre]
  · rw [hg5_edgeH_12]
    have h0 : I * ((((1 : ℝ)) / 10 : ℝ) : ℂ) ≠ 0 := by simp [Complex.ext_iff]
    simp only [Set.Icc.coe_one]
    rw [hg5_chartInv_ne h0, hg3_bottom]
    congr 1
    have : (I * ((((1 : ℝ)) / 10 : ℝ) : ℂ))⁻¹ = -10 * I := by
      rw [mul_inv, Complex.inv_I]; push_cast; ring
    rw [this]; ring

theorem hg5_edgeF_zero (i : Fin 13) : hg5_edgeF i 0 = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
  simp [hg5_edgeF, hg3_arc]

theorem hg5_edgeF_one (i : Fin 13) : hg5_edgeF i 1 = ((hg3_bottom : ℂ) : OnePoint ℂ) := by
  have h1 : min (1 : ℝ) (1 / 2) = 1 / 2 := by norm_num
  have h2 : max (1 : ℝ) (1 / 2) = 1 := by norm_num
  simp only [hg5_edgeF, ContinuousMap.coe_mk, Set.Icc.coe_one, hg3_arc, h1, h2]
  congr 1
  push_cast
  ring

theorem hg5_edge_ends_proof (ε : hg2_Edge Unit 13) :
    hg5_edge ε 0 = hg5_vert (hg2_src hg5_one ε) ∧ hg5_edge ε 1 = hg5_vert (hg2_tgt hg5_one ε) := by
  rcases ε with ⟨i, _⟩ | ⟨i, _⟩ | ⟨i, _⟩
  · exact ⟨hg5_edgeE_zero i, hg5_edgeE_one i⟩
  · exact ⟨hg5_edgeF_zero i, hg5_edgeF_one i⟩
  · exact ⟨hg5_edgeH_zero i, hg5_edgeH_one i⟩


/-! ## Statement 2: the faces -/

theorem hg5_wedge_apply (u v : ℝ) (a : StdSimplex ℝ (Fin 3)) :
    hg5_wedge u v a = ((-11 / 2 + (u + 11 / 2) * (1 - |a.weights 0 - a.weights 2|) +
      (v - u) * a.weights 1 : ℝ) : ℂ) + ((10 * (a.weights 0 - a.weights 2) : ℝ) : ℂ) * I := rfl

theorem hg5_triA_lt (i : Fin 13) (h : i.val < 12) (a : StdSimplex ℝ (Fin 3)) :
    hg5_triA i a = ((hg5_wedge (hg3_waist i) (hg5_markRe ⟨i.val, h⟩) a : ℂ) : OnePoint ℂ) := by
  simp [hg5_triA, h]

theorem hg5_triB_lt (i : Fin 13) (h : i.val < 12) (a : StdSimplex ℝ (Fin 3)) :
    hg5_triB i a =
      ((hg5_wedge (hg3_waist (finRotate 13 i)) (hg5_markRe ⟨i.val, h⟩) a : ℂ) : OnePoint ℂ) := by
  simp [hg5_triB, h]

theorem hg5_triA_12 : hg5_triA 12 = hg5_cone 12 hg5_waist12_ne := by
  simp [hg5_triA]

theorem hg5_triB_12 : hg5_triB 12 = hg5_cone 0 hg5_waist0_ne := by
  simp [hg5_triB]

theorem hg5_cone_apply (i : Fin 13) (hi : hg3_waist i + 11 / 2 ≠ 0) (a : StdSimplex ℝ (Fin 3)) :
    hg5_cone i hi a = hg5_chartInv (hg5_coneFun (2 * (hg3_waist i + 11 / 2)) a) := rfl

theorem hg5_face_w0 (k : Fin 3) (t : unitInterval) :
    (StdSimplex.map k.succAbove (StdSimplex.homeomorphI.symm t)).weights 0 =
      if k = 0 then 0 else 1 - (t : ℝ) := by
  rw [hg5_face_w]; fin_cases k <;> simp

theorem hg5_face_w1 (k : Fin 3) (t : unitInterval) :
    (StdSimplex.map k.succAbove (StdSimplex.homeomorphI.symm t)).weights 1 =
      if k = 0 then 1 - (t : ℝ) else if k = 1 then 0 else (t : ℝ) := by
  rw [hg5_face_w]; fin_cases k <;> simp

theorem hg5_face_w2 (k : Fin 3) (t : unitInterval) :
    (StdSimplex.map k.succAbove (StdSimplex.homeomorphI.symm t)).weights 2 =
      if k = 2 then 0 else (t : ℝ) := by
  rw [hg5_face_w]; fin_cases k <;> simp

theorem hg5_wedge_face0 (u v : ℝ) (t : unitInterval) :
    hg5_wedge u v (StdSimplex.map (0 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)) =
      (((-11 / 2 + (1 - (t : ℝ)) * (v + 11 / 2) : ℝ) : ℂ) + ((-10 * (t : ℝ)) : ℝ) * I : ℂ) := by
  have ht0 := t.2.1
  rw [hg5_wedge_apply, hg5_face_w0, hg5_face_w1, hg5_face_w2]
  simp only [↓reduceIte, Fin.reduceEq]
  rw [show (0 : ℝ) - t = -t by ring, abs_neg, abs_of_nonneg ht0]
  congr 2 <;> push_cast <;> ring

theorem hg5_wedge_face1 (u v : ℝ) (t : unitInterval) :
    hg5_wedge u v (StdSimplex.map (1 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)) =
      (((-11 / 2 + (u + 11 / 2) * (1 - |1 - 2 * (t : ℝ)|) : ℝ) : ℂ) +
        ((10 * (1 - 2 * (t : ℝ))) : ℝ) * I : ℂ) := by
  rw [hg5_wedge_apply, hg5_face_w0, hg5_face_w1, hg5_face_w2]
  simp only [↓reduceIte, Fin.reduceEq]
  rw [show (1 : ℝ) - t - t = 1 - 2 * t by ring]
  congr 2; ring

theorem hg5_wedge_face2 (u v : ℝ) (t : unitInterval) :
    hg5_wedge u v (StdSimplex.map (2 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)) =
      (((-11 / 2 + (t : ℝ) * (v + 11 / 2) : ℝ) : ℂ) + ((10 * (1 - (t : ℝ))) : ℝ) * I : ℂ) := by
  have ht1 := t.2.2
  rw [hg5_wedge_apply, hg5_face_w0, hg5_face_w1, hg5_face_w2]
  simp only [↓reduceIte, Fin.reduceEq]
  rw [sub_zero, abs_of_nonneg (by linarith)]
  congr 2; ring

theorem hg5_coneFun_face0 (k : ℝ) (t : unitInterval) :
    hg5_coneFun k (StdSimplex.map (0 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)) =
      I * ((((t : ℝ)) / 10 : ℝ) : ℂ) := by
  have ht0 := t.2.1
  rw [hg5_coneFun, hg5_face_w0, hg5_face_w2]
  simp only [↓reduceIte, Fin.reduceEq, zero_add, min_eq_left ht0,
    mul_zero, Complex.ofReal_zero]
  by_cases h : (t : ℝ) = 0
  · simp [h]
  · have hI : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
    rw [div_eq_iff]
    · push_cast
      ring_nf
      rw [Complex.I_sq]; ring
    · simpa [Complex.ext_iff] using h

theorem hg5_coneFun_face2 (k : ℝ) (t : unitInterval) :
    hg5_coneFun k (StdSimplex.map (2 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)) =
      -I * (((1 - (t : ℝ)) / 10 : ℝ) : ℂ) := by
  have ht1 := t.2.2
  rw [hg5_coneFun, hg5_face_w0, hg5_face_w2]
  simp only [↓reduceIte, Fin.reduceEq, add_zero,
    min_eq_right (show (0 : ℝ) ≤ 1 - t by linarith), mul_zero, Complex.ofReal_zero, sub_zero,
    zero_add]
  by_cases h : (1 - t : ℝ) = 0
  · simp [h]
  · have hI : ((1 - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
    rw [div_eq_iff]
    · push_cast
      ring_nf
      rw [Complex.I_sq]; ring
    · simpa [Complex.ext_iff] using h

theorem hg5_two_min (t : ℝ) : 2 * min (1 - t) t = 1 - |1 - 2 * t| := by
  rcases le_total (1 - t) t with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

theorem hg5_cone_face1 (i : Fin 13) (hi : hg3_waist i + 11 / 2 ≠ 0) (t : unitInterval) :
    hg5_cone i hi (StdSimplex.map (1 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)) =
      hg5_edgeF i t := by
  rw [hg5_cone_apply, hg5_coneFun, hg5_face_w0, hg5_face_w2, hg5_edgeF_eq]
  simp only [↓reduceIte, Fin.reduceEq]
  rw [show (1 : ℝ) - t + t = 1 by ring, one_pow, Complex.ofReal_one]
  set D : ℂ := ((2 * (hg3_waist i + 11 / 2) * min (1 - (t : ℝ)) t : ℝ) : ℂ) +
    ((10 * (1 - (t : ℝ) - t) : ℝ) : ℂ) * I with hD
  have hD0 : D ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    have hre := congrArg Complex.re h0
    simp [hD] at him hre
    have ht : (t : ℝ) = 1 / 2 := by linarith
    rw [ht] at hre
    norm_num at hre
    exact hi hre
  rw [one_div, hg5_chartInv_ne (inv_ne_zero hD0), inv_inv]
  congr 1
  apply Complex.ext
  · simp only [hD, mr_centre, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      div_ofNat_re]
    norm_num
    linear_combination (hg3_waist i + 11 / 2) * hg5_two_min (t : ℝ)
  · simp [hD, mr_centre]; ring

theorem hg5_faces_proof (τ : hg2_Tri Unit 13) :
    hg5_face (hg5_tri τ) 0 = hg5_edge (hg2_face0 hg5_one τ) ∧
      hg5_face (hg5_tri τ) 1 = hg5_edge (hg2_face1 τ) ∧
      hg5_face (hg5_tri τ) 2 = hg5_edge (hg2_face2 τ) := by
  rcases τ with ⟨i, _⟩ | ⟨i, _⟩
  · rcases hg5_fin13_cases i with h | rfl
    · refine ⟨?_, ?_, ?_⟩ <;> ext1 t <;>
        simp only [hg5_face_apply, hg5_tri, hg2_face0, hg2_face1, hg2_face2, hg5_edge,
          hg5_triA_lt i h]
      · rw [hg5_wedge_face0, hg5_edgeH_lt i h]
      · rw [hg5_wedge_face1, hg5_edgeF_eq]
      · rw [hg5_wedge_face2, hg5_edgeE_lt i h]
    · refine ⟨?_, ?_, ?_⟩ <;> ext1 t <;>
        simp only [hg5_face_apply, hg5_tri, hg2_face0, hg2_face1, hg2_face2, hg5_edge,
          hg5_triA_12]
      · rw [hg5_cone_apply, hg5_coneFun_face0, hg5_edgeH_12]
      · rw [hg5_cone_face1]
      · rw [hg5_cone_apply, hg5_coneFun_face2, hg5_edgeE_12]
  · rcases hg5_fin13_cases i with h | rfl
    · refine ⟨?_, ?_, ?_⟩ <;> ext1 t <;>
        simp only [hg5_face_apply, hg5_tri, hg2_face0, hg2_face1, hg2_face2, hg5_edge,
          hg5_triB_lt i h]
      · rw [hg5_wedge_face0, hg5_edgeH_lt i h]
      · rw [hg5_wedge_face1, hg5_edgeF_eq]
      · rw [hg5_wedge_face2, hg5_edgeE_lt i h]
    · refine ⟨?_, ?_, ?_⟩ <;> ext1 t <;>
        simp only [hg5_face_apply, hg5_tri, hg2_face0, hg2_face1, hg2_face2, hg5_edge,
          hg5_triB_12]
      · rw [hg5_cone_apply, hg5_coneFun_face0, hg5_edgeH_12]
      · rw [hg5_cone_face1]; rfl
      · rw [hg5_cone_apply, hg5_coneFun_face2, hg5_edgeE_12]


/-! ## Statement 3: the edges and the marks -/

theorem hg5_inv_negI (r : ℝ) (hr : r ≠ 0) : (-I * (r : ℂ))⁻¹ = I * ((r⁻¹ : ℝ) : ℂ) := by
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [mul_inv, inv_neg, Complex.inv_I]; push_cast; ring

theorem hg5_inv_I (r : ℝ) (hr : r ≠ 0) : (I * (r : ℂ))⁻¹ = -I * ((r⁻¹ : ℝ) : ℂ) := by
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [mul_inv, Complex.inv_I]; push_cast; ring

theorem hg5_edgeE_12_lt (s : unitInterval) (hs : (s : ℝ) ≠ 1) :
    hg5_edgeE 12 s = ((mr_centre + I * (((10 / (1 - (s : ℝ))) : ℝ) : ℂ) : ℂ) : OnePoint ℂ) := by
  have hr : (1 - (s : ℝ)) / 10 ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hs)) (by norm_num)
  have h0 : -I * ((((1 - (s : ℝ)) / 10 : ℝ)) : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (by exact_mod_cast hr)
  rw [hg5_edgeE_12, hg5_chartInv_ne h0, hg5_inv_negI _ hr, inv_div]

theorem hg5_edgeH_12_pos (s : unitInterval) (hs : (s : ℝ) ≠ 0) :
    hg5_edgeH 12 s = ((mr_centre - I * (((10 / (s : ℝ)) : ℝ) : ℂ) : ℂ) : OnePoint ℂ) := by
  have hr : (s : ℝ) / 10 ≠ 0 := div_ne_zero hs (by norm_num)
  have h0 : I * ((((s : ℝ)) / 10 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (by exact_mod_cast hr)
  rw [hg5_edgeH_12, hg5_chartInv_ne h0, hg5_inv_I _ hr, inv_div]
  ring_nf

theorem hg5_unit_eq_one (s : unitInterval) : s = 1 ↔ (s : ℝ) = 1 := by
  rw [Subtype.ext_iff, Set.Icc.coe_one]

theorem hg5_unit_eq_zero (s : unitInterval) : s = 0 ↔ (s : ℝ) = 0 := by
  rw [Subtype.ext_iff, Set.Icc.coe_zero]

theorem hg5_edgeE_marks (i : Fin 13) (s : unitInterval) :
    hg5_edgeE i s ∈ Set.range (b6_branch mr_base) ↔ s = 1 := by
  rw [hg5_unit_eq_one]
  rcases hg5_fin13_cases i with h | rfl
  · rw [hg5_edgeE_lt i h, hg5_coe_mark_iff]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
      add_re, mul_re, sub_zero]
    constructor
    · rintro ⟨h1, -⟩; linarith
    · intro h1
      refine ⟨by rw [h1]; ring, ⟨i.val, h⟩, ?_⟩
      rw [h1]; ring
  · by_cases hs : (s : ℝ) = 1
    · simp only [hs, iff_true]
      have : s = 1 := (hg5_unit_eq_one s).mpr hs
      rw [this, hg5_edgeE_one]
      exact ⟨12, rfl⟩
    · simp only [hs, iff_false]
      rw [hg5_edgeE_12_lt s hs, hg5_coe_mark_iff]
      rintro ⟨h1, -⟩
      rw [show (mr_centre + I * (((10 / (1 - (s : ℝ))) : ℝ) : ℂ)).im = 10 / (1 - (s : ℝ)) by
        rw [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im]; simp [mr_centre]] at h1
      have : 1 - (s : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
      rcases div_eq_zero_iff.mp h1 with h1 | h1
      · norm_num at h1
      · exact this h1

theorem hg5_edgeH_marks (i : Fin 13) (s : unitInterval) :
    hg5_edgeH i s ∈ Set.range (b6_branch mr_base) ↔ s = 0 := by
  rw [hg5_unit_eq_zero]
  rcases hg5_fin13_cases i with h | rfl
  · rw [hg5_edgeH_lt i h, hg5_coe_mark_iff]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
      add_re, mul_re, sub_zero]
    constructor
    · rintro ⟨h1, -⟩; linarith
    · intro h1
      refine ⟨by rw [h1]; ring, ⟨i.val, h⟩, ?_⟩
      rw [h1]; ring
  · by_cases hs : (s : ℝ) = 0
    · simp only [hs, iff_true]
      have : s = 0 := (hg5_unit_eq_zero s).mpr hs
      rw [this, hg5_edgeH_zero]
      exact ⟨12, rfl⟩
    · simp only [hs, iff_false]
      rw [hg5_edgeH_12_pos s hs, hg5_coe_mark_iff]
      rintro ⟨h1, -⟩
      rw [show (mr_centre - I * (((10 / (s : ℝ)) : ℝ) : ℂ)).im = -(10 / (s : ℝ)) by
        rw [sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im]; simp [mr_centre]] at h1
      rcases div_eq_zero_iff.mp (neg_eq_zero.mp h1) with h1 | h1
      · norm_num at h1
      · exact hs h1

theorem hg5_edgeF_marks (i : Fin 13) (s : unitInterval) :
    hg5_edgeF i s ∉ Set.range (b6_branch mr_base) :=
  hg3_arc_mem_base i s

theorem hg5_edge_marks_proof (ε : hg2_Edge Unit 13) (s : unitInterval) :
    hg5_edge ε s ∈ Set.range (b6_branch mr_base) ↔
      (∃ i : Fin 13, ε = Sum.inl (i, ()) ∧ s = 1) ∨
        (∃ i : Fin 13, ε = Sum.inr (Sum.inr (i, ())) ∧ s = 0) := by
  rcases ε with ⟨i, _⟩ | ⟨i, _⟩ | ⟨i, _⟩
  · simp only [hg5_edge, hg5_edgeE_marks]
    simp
  · simp only [hg5_edge]
    simp only [hg5_edgeF_marks i s, false_iff]
    simp
  · simp only [hg5_edge, hg5_edgeH_marks]
    simp


/-! ## Statement 4: injectivity -/

theorem hg5_simplex_ext' {a b : StdSimplex ℝ (Fin 3)} (h1 : a.weights 1 = b.weights 1)
    (hd : a.weights 0 - a.weights 2 = b.weights 0 - b.weights 2) : a = b := by
  have ha := hg5_sum3 a
  have hb := hg5_sum3 b
  apply hg5_simplex_ext <;> linarith

theorem hg5_wedge_injective (u v : ℝ) (huv : u ≠ v) : Function.Injective (hg5_wedge u v) := by
  intro a b h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [hg5_wedge_apply, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
    mul_one, zero_add, add_re, mul_re, sub_zero] at him hre
  have hd : a.weights 0 - a.weights 2 = b.weights 0 - b.weights 2 := by linarith
  rw [hd] at hre
  have h1 : (v - u) * a.weights 1 = (v - u) * b.weights 1 := by linarith
  exact hg5_simplex_ext' (mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm huv)) h1) hd

theorem hg5_chartInv_injective : Function.Injective hg5_chartInv := by
  intro w w' h
  by_cases hw : w = 0
  · by_cases hw' : w' = 0
    · rw [hw, hw']
    · rw [hw, hg5_chartInv_zero, hg5_chartInv_ne hw'] at h
      exact absurd h.symm (OnePoint.coe_ne_infty _)
  · by_cases hw' : w' = 0
    · rw [hw', hg5_chartInv_zero, hg5_chartInv_ne hw] at h
      exact absurd h (OnePoint.coe_ne_infty _)
    · rw [hg5_chartInv_ne hw, hg5_chartInv_ne hw'] at h
      have := OnePoint.coe_injective h
      exact inv_injective (add_left_cancel this)

theorem hg5_split (a : StdSimplex ℝ (Fin 3)) :
    a.weights 0 + a.weights 2 =
      2 * min (a.weights 0) (a.weights 2) + |a.weights 0 - a.weights 2| := by
  rcases le_total (a.weights 0) (a.weights 2) with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- The cone denominator `k · min a₀ a₂ + 10 (a₀ − a₂) i`. -/
def hg5_coneDen (k : ℝ) (a : StdSimplex ℝ (Fin 3)) : ℂ :=
  ((k * min (a.weights 0) (a.weights 2) : ℝ) : ℂ) +
    ((10 * (a.weights 0 - a.weights 2) : ℝ) : ℂ) * I

theorem hg5_coneDen_ne (k : ℝ) (hk : k ≠ 0) (a : StdSimplex ℝ (Fin 3))
    (hS : 0 < a.weights 0 + a.weights 2) : hg5_coneDen k a ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [hg5_coneDen] at him hre
  have e : a.weights 0 = a.weights 2 := by linarith
  rcases hre with hre | hre
  · exact hk hre
  · rw [e, min_self] at hre
    linarith

theorem hg5_coneFun_eq (k : ℝ) (a : StdSimplex ℝ (Fin 3)) :
    hg5_coneFun k a = (((a.weights 0 + a.weights 2) ^ 2 : ℝ) : ℂ) / hg5_coneDen k a := rfl

theorem hg5_coneFun_zero_iff (k : ℝ) (hk : k ≠ 0) (a : StdSimplex ℝ (Fin 3)) :
    hg5_coneFun k a = 0 ↔ a.weights 0 + a.weights 2 = 0 := by
  have h0 := a.weights_nonneg 0
  have h2 := a.weights_nonneg 2
  constructor
  · intro h
    by_contra hS
    have hS' : 0 < a.weights 0 + a.weights 2 := lt_of_le_of_ne (by linarith) (Ne.symm hS)
    rw [hg5_coneFun_eq, div_eq_zero_iff] at h
    rcases h with h | h
    · have : (a.weights 0 + a.weights 2) ^ 2 = 0 := by exact_mod_cast h
      exact hS (pow_eq_zero_iff (by norm_num) |>.mp this)
    · exact hg5_coneDen_ne k hk a hS' h
  · intro h
    rw [hg5_coneFun_eq, h]; simp

theorem hg5_coneFun_inv (k : ℝ) (a : StdSimplex ℝ (Fin 3)) :
    (hg5_coneFun k a)⁻¹ =
      ((k * min (a.weights 0) (a.weights 2) / (a.weights 0 + a.weights 2) ^ 2 : ℝ) : ℂ) +
        ((10 * (a.weights 0 - a.weights 2) / (a.weights 0 + a.weights 2) ^ 2 : ℝ) : ℂ) * I := by
  rw [hg5_coneFun_eq, inv_div, hg5_coneDen, Complex.ofReal_div, Complex.ofReal_div,
    div_mul_eq_mul_div, add_div]

theorem hg5_coneFun_injective (k : ℝ) (hk : k ≠ 0) : Function.Injective (hg5_coneFun k) := by
  intro a b h
  have ha0 := a.weights_nonneg 0
  have ha2 := a.weights_nonneg 2
  have hb0 := b.weights_nonneg 0
  have hb2 := b.weights_nonneg 2
  have hz := hg5_coneFun_zero_iff k hk a
  have hz' := hg5_coneFun_zero_iff k hk b
  rw [h] at hz
  by_cases hS : a.weights 0 + a.weights 2 = 0
  · have hS' : b.weights 0 + b.weights 2 = 0 := hz'.mp (hz.mpr hS)
    apply hg5_simplex_ext' <;> [skip; linarith]
    have := hg5_sum3 a
    have := hg5_sum3 b
    linarith
  · have hSa : 0 < a.weights 0 + a.weights 2 := lt_of_le_of_ne (by linarith) (Ne.symm hS)
    have hSb : 0 < b.weights 0 + b.weights 2 := by
      rcases (lt_or_eq_of_le (show 0 ≤ b.weights 0 + b.weights 2 by linarith)) with h' | h'
      · exact h'
      · exact absurd (hz.mp (hz'.mpr h'.symm)) hS
    have hinv : (hg5_coneFun k a)⁻¹ = (hg5_coneFun k b)⁻¹ := by rw [h]
    rw [hg5_coneFun_inv k a, hg5_coneFun_inv k b] at hinv
    have hre := congrArg Complex.re hinv
    have him := congrArg Complex.im hinv
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero, add_im,
      mul_im, mul_one, zero_add, add_zero] at hre him
    have hsa := hg5_split a
    have hsb := hg5_split b
    set Sa := a.weights 0 + a.weights 2
    set Sb := b.weights 0 + b.weights 2
    have hm : min (a.weights 0) (a.weights 2) / Sa ^ 2 = min (b.weights 0) (b.weights 2) / Sb ^ 2 := by
      have := hre
      rw [mul_div_assoc, mul_div_assoc] at this
      exact mul_left_cancel₀ hk this
    have hd : (a.weights 0 - a.weights 2) / Sa ^ 2 = (b.weights 0 - b.weights 2) / Sb ^ 2 := by
      have := him
      rw [mul_div_assoc, mul_div_assoc] at this
      linarith
    have hda : |a.weights 0 - a.weights 2| / Sa ^ 2 = |b.weights 0 - b.weights 2| / Sb ^ 2 := by
      rw [← abs_of_pos (pow_pos hSa 2), ← abs_of_pos (pow_pos hSb 2), ← abs_div, ← abs_div, hd]
    have hinvS : 1 / Sa = 1 / Sb := by
      have e1 : 1 / Sa = (2 * min (a.weights 0) (a.weights 2) + |a.weights 0 - a.weights 2|) /
          Sa ^ 2 := by rw [← hsa]; field_simp
      have e2 : 1 / Sb = (2 * min (b.weights 0) (b.weights 2) + |b.weights 0 - b.weights 2|) /
          Sb ^ 2 := by rw [← hsb]; field_simp
      rw [e1, e2, add_div, add_div, mul_div_assoc, mul_div_assoc, hm, hda]
    have hSS : Sa = Sb := by
      have := hinvS
      rw [one_div, one_div] at this
      exact inv_injective this
    rw [hSS] at hd
    have hd' : a.weights 0 - a.weights 2 = b.weights 0 - b.weights 2 := by
      have hp : Sb ^ 2 ≠ 0 := (pow_pos hSb 2).ne'
      rwa [div_left_inj' hp] at hd
    apply hg5_simplex_ext' _ hd'
    have := hg5_sum3 a
    have := hg5_sum3 b
    linarith

theorem hg5_cone_injective (i : Fin 13) (hi : hg3_waist i + 11 / 2 ≠ 0) :
    Function.Injective (hg5_cone i hi) := by
  intro a b h
  rw [hg5_cone_apply, hg5_cone_apply] at h
  exact hg5_coneFun_injective _ (mul_ne_zero two_ne_zero hi) (hg5_chartInv_injective h)

theorem hg5_tri_injective_proof (τ : hg2_Tri Unit 13) : Function.Injective (hg5_tri τ) := by
  rcases τ with ⟨i, _⟩ | ⟨i, _⟩
  · rcases hg5_fin13_cases i with h | rfl
    · intro a b hab
      simp only [hg5_tri, hg5_triA_lt i h] at hab
      exact hg5_wedge_injective _ _ (hg5_waist_ne_mark _ _) (OnePoint.coe_injective hab)
    · simp only [hg5_tri, hg5_triA_12]
      exact hg5_cone_injective _ _
  · rcases hg5_fin13_cases i with h | rfl
    · intro a b hab
      simp only [hg5_tri, hg5_triB_lt i h] at hab
      exact hg5_wedge_injective _ _ (hg5_waist_ne_mark _ _) (OnePoint.coe_injective hab)
    · simp only [hg5_tri, hg5_triB_12]
      exact hg5_cone_injective _ _


/-! ## Plane invariants: the fan norm and the profile parameter -/

/-- The fan norm `|x + 11/2| / 7 + |y| / 10`; the fan `hg3_fan` is where it is at most `1`. -/
def hg5_N (w : ℂ) : ℝ := |w.re + 11 / 2| / 7 + |w.im| / 10

/-- The profile parameter: the real crossing point `u` of the profile `prof_u` through `w`
(meaningful for `|Im w| < 10`). -/
def hg5_rho (w : ℂ) : ℝ := -11 / 2 + (w.re + 11 / 2) / (1 - |w.im| / 10)

theorem hg5_waist_succ (i : Fin 13) (h : i.val < 12) :
    hg3_waist (finRotate 13 i) = hg3_waist ⟨i.val + 1, by omega⟩ := by
  have := finRotate_of_lt (n := 12) (k := i.val) h
  congr 1

theorem hg5_waist_lt_mark_self (i : Fin 13) (h : i.val < 12) :
    hg3_waist i < hg5_markRe ⟨i.val, h⟩ := hg5_waist_lt_mark i _ le_rfl

theorem hg5_mark_lt_waist_succ (i : Fin 13) (h : i.val < 12) :
    hg5_markRe ⟨i.val, h⟩ < hg3_waist ⟨i.val + 1, by omega⟩ :=
  hg5_mark_lt_waist _ _ (by simp)

theorem hg5_wedge_int (u v : ℝ) (a : StdSimplex ℝ (Fin 3)) (ha : ∀ k, 0 < a.weights k) :
    |(hg5_wedge u v a).im| < 10 ∧
      ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ hg5_rho (hg5_wedge u v a) = u + (v - u) * θ := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have hs := hg5_sum3 a
  have hd : |a.weights 0 - a.weights 2| < a.weights 0 + a.weights 2 := by
    rw [abs_lt]; constructor <;> linarith
  have him : (hg5_wedge u v a).im = 10 * (a.weights 0 - a.weights 2) := by
    simp [hg5_wedge_apply]
  have hre : (hg5_wedge u v a).re = -11 / 2 + (u + 11 / 2) * (1 - |a.weights 0 - a.weights 2|) +
      (v - u) * a.weights 1 := by simp [hg5_wedge_apply]
  have habs : |(hg5_wedge u v a).im| = 10 * |a.weights 0 - a.weights 2| := by
    rw [him, abs_mul]; norm_num
  refine ⟨by rw [habs]; linarith, ?_⟩
  set l := 1 - |a.weights 0 - a.weights 2| with hl
  have hlpos : a.weights 1 < l := by rw [hl]; linarith
  have hl0 : 0 < l := lt_trans h1 hlpos
  refine ⟨a.weights 1 / l, div_pos h1 hl0, (div_lt_one hl0).mpr hlpos, ?_⟩
  rw [hg5_rho, habs, hre]
  have : 1 - 10 * |a.weights 0 - a.weights 2| / 10 = l := by rw [hl]; ring
  rw [this]
  field_simp
  ring

theorem hg5_cone_pt (i : Fin 13) (hi : hg3_waist i + 11 / 2 ≠ 0) (a : StdSimplex ℝ (Fin 3))
    (hS : 0 < a.weights 0 + a.weights 2) :
    ∃ w : ℂ, hg5_cone i hi a = ((w : ℂ) : OnePoint ℂ) ∧
      w.re + 11 / 2 = 2 * (hg3_waist i + 11 / 2) * min (a.weights 0) (a.weights 2) /
        (a.weights 0 + a.weights 2) ^ 2 ∧
      w.im = 10 * (a.weights 0 - a.weights 2) / (a.weights 0 + a.weights 2) ^ 2 := by
  have hk : 2 * (hg3_waist i + 11 / 2) ≠ 0 := mul_ne_zero two_ne_zero hi
  have hne : hg5_coneFun (2 * (hg3_waist i + 11 / 2)) a ≠ 0 := by
    rw [Ne, hg5_coneFun_zero_iff _ hk]; exact hS.ne'
  refine ⟨_, by rw [hg5_cone_apply, hg5_chartInv_ne hne], ?_, ?_⟩
  · rw [add_re, hg5_coneFun_inv, add_re, ofReal_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    simp [mr_centre]; ring
  · rw [add_im, hg5_coneFun_inv, add_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    simp [mr_centre]

theorem hg5_waist_abs7 (i : Fin 13) (hi : i = 0 ∨ i = 12) : |hg3_waist i + 11 / 2| = 7 := by
  rcases hi with rfl | rfl <;> norm_num [hg3_waist]

/-- A finite point of a cone has fan norm `1 / (a₀ + a₂) ≥ 1`. -/
theorem hg5_cone_N (i : Fin 13) (h7 : |hg3_waist i + 11 / 2| = 7)
    (a : StdSimplex ℝ (Fin 3)) (hS : 0 < a.weights 0 + a.weights 2) (w : ℂ)
    (hw : w.re + 11 / 2 = 2 * (hg3_waist i + 11 / 2) * min (a.weights 0) (a.weights 2) /
        (a.weights 0 + a.weights 2) ^ 2)
    (hw' : w.im = 10 * (a.weights 0 - a.weights 2) / (a.weights 0 + a.weights 2) ^ 2) :
    hg5_N w = 1 / (a.weights 0 + a.weights 2) := by
  have hm : 0 ≤ min (a.weights 0) (a.weights 2) := le_min (a.weights_nonneg 0) (a.weights_nonneg 2)
  have hS2 : 0 < (a.weights 0 + a.weights 2) ^ 2 := pow_pos hS 2
  have e1 : |2 * (hg3_waist i + 11 / 2) * min (a.weights 0) (a.weights 2)| =
      14 * min (a.weights 0) (a.weights 2) := by
    rw [abs_mul, abs_mul, h7, abs_of_nonneg hm]; norm_num
  have e2 : |10 * (a.weights 0 - a.weights 2)| = 10 * |a.weights 0 - a.weights 2| := by
    rw [abs_mul]; norm_num
  rw [hg5_N, hw, hw', abs_div, abs_div, abs_of_pos hS2, e1, e2]
  have := hg5_split a
  have hS0 : a.weights 0 + a.weights 2 ≠ 0 := hS.ne'
  field_simp
  linarith

theorem hg5_N_lt_rho (w : ℂ) (hy : |w.im| < 10) (hN : 1 < hg5_N w) :
    hg5_rho w < -25 / 2 ∨ 3 / 2 < hg5_rho w := by
  have hl : 0 < 1 - |w.im| / 10 := by linarith
  have hX : 7 * (1 - |w.im| / 10) < |w.re + 11 / 2| := by
    unfold hg5_N at hN; linarith
  rw [hg5_rho]
  rcases le_or_gt 0 (w.re + 11 / 2) with h | h
  · rw [abs_of_nonneg h] at hX
    right
    have : 7 < (w.re + 11 / 2) / (1 - |w.im| / 10) := by rw [lt_div_iff₀ hl]; linarith
    linarith
  · rw [abs_of_neg h] at hX
    left
    have : (w.re + 11 / 2) / (1 - |w.im| / 10) < -7 := by rw [div_lt_iff₀ hl]; linarith
    linarith


/-! ## Statement 5: the open triangles -/

theorem hg5_intAA (i j : Fin 13) (hi : i.val < 12) (hj : j.val < 12) (x : ℝ)
    (h1 : hg3_waist i < x) (h2 : x < hg5_markRe ⟨i.val, hi⟩)
    (h3 : hg3_waist j < x) (h4 : x < hg5_markRe ⟨j.val, hj⟩) : i = j := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · have := hg5_mark_lt_waist j ⟨i.val, hi⟩ h; linarith
  · exact Fin.ext h
  · have := hg5_mark_lt_waist i ⟨j.val, hj⟩ h; linarith

theorem hg5_intBB (i j : Fin 13) (hi : i.val < 12) (hj : j.val < 12) (x : ℝ)
    (h1 : hg5_markRe ⟨i.val, hi⟩ < x) (h2 : x < hg3_waist ⟨i.val + 1, by omega⟩)
    (h3 : hg5_markRe ⟨j.val, hj⟩ < x) (h4 : x < hg3_waist ⟨j.val + 1, by omega⟩) : i = j := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · have := hg5_waist_lt_mark ⟨i.val + 1, by omega⟩ ⟨j.val, hj⟩ (by simp; omega); linarith
  · exact Fin.ext h
  · have := hg5_waist_lt_mark ⟨j.val + 1, by omega⟩ ⟨i.val, hi⟩ (by simp; omega); linarith

theorem hg5_intAB (i j : Fin 13) (hi : i.val < 12) (hj : j.val < 12) (x : ℝ)
    (h1 : hg3_waist i < x) (h2 : x < hg5_markRe ⟨i.val, hi⟩)
    (h3 : hg5_markRe ⟨j.val, hj⟩ < x) (h4 : x < hg3_waist ⟨j.val + 1, by omega⟩) : False := by
  rcases Nat.lt_or_ge j.val i.val with h | h
  · have : hg3_waist ⟨j.val + 1, by omega⟩ ≤ hg3_waist i :=
      hg5_waist_strictMono.monotone (show (⟨j.val + 1, by omega⟩ : Fin 13) ≤ i from by
        rw [Fin.le_def]; simp; omega)
    linarith
  · have : hg5_markRe ⟨i.val, hi⟩ ≤ hg5_markRe ⟨j.val, hj⟩ :=
      hg5_markRe_strictMono.monotone (by rw [Fin.le_def]; simpa using h)
    linarith

theorem hg5_waist_le_12 (i : Fin 13) : hg3_waist i ≤ 3 / 2 := (hg5_waist_bounds i).2
theorem hg5_waist_ge_0 (i : Fin 13) : -25 / 2 ≤ hg3_waist i := (hg5_waist_bounds i).1
theorem hg5_mark_bounds' (j : Fin 12) : -25 / 2 < hg5_markRe j ∧ hg5_markRe j < 3 / 2 := by
  have := hg5_markRe_bounds j; constructor <;> linarith

/-- The open region of a base triangle, in the plane coordinates. -/
def hg5_triReg : hg2_Tri Unit 13 → ℂ → Prop
  | Sum.inl (i, _), w => if h : i.val < 12 then
      |w.im| < 10 ∧ (-25 / 2 < hg5_rho w ∧ hg5_rho w < 3 / 2) ∧
        hg3_waist i < hg5_rho w ∧ hg5_rho w < hg5_markRe ⟨i.val, h⟩
    else 0 < w.re + 11 / 2 ∧ (|w.im| < 10 → 3 / 2 < hg5_rho w)
  | Sum.inr (i, _), w => if h : i.val < 12 then
      |w.im| < 10 ∧ (-25 / 2 < hg5_rho w ∧ hg5_rho w < 3 / 2) ∧
        hg5_markRe ⟨i.val, h⟩ < hg5_rho w ∧ hg5_rho w < hg3_waist ⟨i.val + 1, by omega⟩
    else w.re + 11 / 2 < 0 ∧ (|w.im| < 10 → hg5_rho w < -25 / 2)

theorem hg5_triReg_unique (τ τ' : hg2_Tri Unit 13) (w : ℂ) (h : hg5_triReg τ w)
    (h' : hg5_triReg τ' w) : τ = τ' := by
  rcases τ with ⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩ <;> rcases τ' with ⟨j, ⟨⟩⟩ | ⟨j, ⟨⟩⟩ <;>
    simp only [hg5_triReg] at h h' <;> split_ifs at h h' with hi hj
  all_goals first
    | (rw [hg5_intAA i j hi hj _ h.2.2.1 h.2.2.2 h'.2.2.1 h'.2.2.2])
    | (rw [hg5_intBB i j hi hj _ h.2.2.1 h.2.2.2 h'.2.2.1 h'.2.2.2])
    | (exact (hg5_intAB i j hi hj _ h.2.2.1 h.2.2.2 h'.2.2.1 h'.2.2.2).elim)
    | (exact (hg5_intAB j i hj hi _ h'.2.2.1 h'.2.2.2 h.2.2.1 h.2.2.2).elim)
    | (exfalso; linarith [h.1, h'.1])
    | (have := i.isLt; have := j.isLt
       have hij : i = j := Fin.ext (by omega)
       rw [hij])
    | (exfalso; have := h'.2 h.1; linarith [h.2.1.1, h.2.1.2])
    | (exfalso; have := h.2 h'.1; linarith [h'.2.1.1, h'.2.1.2])


theorem hg5_wedge_reg (u v : ℝ) (a : StdSimplex ℝ (Fin 3)) (ha : ∀ k, 0 < a.weights k)
    (lo hi : ℝ) (hlo : -25 / 2 ≤ lo) (hhi : hi ≤ 3 / 2)
    (huv : (lo = u ∧ hi = v) ∨ (lo = v ∧ hi = u)) (hlt : lo < hi) :
    |(hg5_wedge u v a).im| < 10 ∧
      (-25 / 2 < hg5_rho (hg5_wedge u v a) ∧ hg5_rho (hg5_wedge u v a) < 3 / 2) ∧
      lo < hg5_rho (hg5_wedge u v a) ∧ hg5_rho (hg5_wedge u v a) < hi := by
  obtain ⟨hy, θ, h0, h1, hr⟩ := hg5_wedge_int u v a ha
  have key : lo < hg5_rho (hg5_wedge u v a) ∧ hg5_rho (hg5_wedge u v a) < hi := by
    rw [hr]
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  exact ⟨hy, ⟨by linarith [key.1], by linarith [key.2]⟩, key⟩

theorem hg5_cone_int (i : Fin 13) (hi : hg3_waist i + 11 / 2 ≠ 0)
    (h7 : |hg3_waist i + 11 / 2| = 7) (a : StdSimplex ℝ (Fin 3)) (ha : ∀ k, 0 < a.weights k) :
    ∃ w : ℂ, hg5_cone i hi a = ((w : ℂ) : OnePoint ℂ) ∧ 1 < hg5_N w ∧
      0 < (w.re + 11 / 2) * (hg3_waist i + 11 / 2) := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have hs := hg5_sum3 a
  have hS : 0 < a.weights 0 + a.weights 2 := by linarith
  obtain ⟨w, hw, hre, him⟩ := hg5_cone_pt i hi a hS
  refine ⟨w, hw, ?_, ?_⟩
  · rw [hg5_cone_N i h7 a hS w hre him, lt_div_iff₀ hS]; linarith
  · rw [hre]
    have hm : 0 < min (a.weights 0) (a.weights 2) := lt_min h0 h2
    have : 0 < (hg3_waist i + 11 / 2) * (hg3_waist i + 11 / 2) := mul_self_pos.mpr hi
    have hS2 : 0 < (a.weights 0 + a.weights 2) ^ 2 := pow_pos hS 2
    rw [div_mul_eq_mul_div]
    apply div_pos _ hS2
    nlinarith

theorem hg5_rho_sign (w : ℂ) (hy : |w.im| < 10) (hX : 0 < w.re + 11 / 2) : -11 / 2 < hg5_rho w := by
  have hl : 0 < 1 - |w.im| / 10 := by linarith
  have := div_pos hX hl
  unfold hg5_rho; linarith

theorem hg5_rho_sign' (w : ℂ) (hy : |w.im| < 10) (hX : w.re + 11 / 2 < 0) : hg5_rho w < -11 / 2 := by
  have hl : 0 < 1 - |w.im| / 10 := by linarith
  have := div_neg_of_neg_of_pos hX hl
  unfold hg5_rho; linarith

theorem hg5_tri_int (τ : hg2_Tri Unit 13) (a : StdSimplex ℝ (Fin 3)) (ha : ∀ k, 0 < a.weights k) :
    ∃ w : ℂ, hg5_tri τ a = ((w : ℂ) : OnePoint ℂ) ∧ hg5_triReg τ w := by
  rcases τ with ⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩
  · rcases hg5_fin13_cases i with h | rfl
    · refine ⟨_, hg5_triA_lt i h a, ?_⟩
      simp only [hg5_triReg, dif_pos h]
      exact hg5_wedge_reg _ _ a ha _ _ (hg5_waist_ge_0 i) (hg5_mark_bounds' _).2.le
        (Or.inl ⟨rfl, rfl⟩) (hg5_waist_lt_mark_self i h)
    · obtain ⟨w, hw, hN, hX⟩ := hg5_cone_int 12 hg5_waist12_ne (hg5_waist_abs7 12 (Or.inr rfl)) a ha
      refine ⟨w, by rw [← hw]; rfl, ?_⟩
      simp only [hg5_triReg, show ¬ (12 : Fin 13).val < 12 by decide, dite_false]
      rw [hg5_waist_12] at hX
      have hX' : 0 < w.re + 11 / 2 := by nlinarith
      refine ⟨hX', fun hy ↦ ?_⟩
      rcases hg5_N_lt_rho w hy hN with h | h
      · have := hg5_rho_sign w hy hX'; linarith
      · exact h
  · rcases hg5_fin13_cases i with h | rfl
    · refine ⟨_, hg5_triB_lt i h a, ?_⟩
      simp only [hg5_triReg, dif_pos h]
      rw [hg5_waist_succ i h]
      exact hg5_wedge_reg _ _ a ha _ _ (hg5_mark_bounds' _).1.le (hg5_waist_le_12 _)
        (Or.inr ⟨rfl, rfl⟩) (hg5_mark_lt_waist_succ i h)
    · obtain ⟨w, hw, hN, hX⟩ := hg5_cone_int 0 hg5_waist0_ne (hg5_waist_abs7 0 (Or.inl rfl)) a ha
      refine ⟨w, by rw [← hw]; rfl, ?_⟩
      simp only [hg5_triReg, show ¬ (12 : Fin 13).val < 12 by decide, dite_false]
      rw [hg5_waist_0] at hX
      have hX' : w.re + 11 / 2 < 0 := by nlinarith
      refine ⟨hX', fun hy ↦ ?_⟩
      rcases hg5_N_lt_rho w hy hN with h | h
      · exact h
      · have := hg5_rho_sign' w hy hX'; linarith

theorem hg5_noMarkA (i : Fin 13) (hi : i.val < 12) (x : ℝ) (h1 : hg3_waist i < x)
    (h2 : x < hg5_markRe ⟨i.val, hi⟩) (j : Fin 12) : x ≠ hg5_markRe j := by
  rintro rfl
  rcases Nat.lt_or_ge j.val i.val with h | h
  · have := hg5_mark_lt_waist i j h; linarith
  · have := hg5_markRe_strictMono.monotone (show (⟨i.val, hi⟩ : Fin 12) ≤ j from h); linarith

theorem hg5_noWaistA (i : Fin 13) (hi : i.val < 12) (x : ℝ) (h1 : hg3_waist i < x)
    (h2 : x < hg5_markRe ⟨i.val, hi⟩) (j : Fin 13) : x ≠ hg3_waist j := by
  rintro rfl
  rcases Nat.lt_or_ge i.val j.val with h | h
  · have := hg5_mark_lt_waist j ⟨i.val, hi⟩ h; linarith
  · have := hg5_waist_strictMono.monotone (show j ≤ i from h); linarith

theorem hg5_noMarkB (i : Fin 13) (hi : i.val < 12) (x : ℝ) (h1 : hg5_markRe ⟨i.val, hi⟩ < x)
    (h2 : x < hg3_waist ⟨i.val + 1, by omega⟩) (j : Fin 12) : x ≠ hg5_markRe j := by
  rintro rfl
  rcases Nat.lt_or_ge i.val j.val with h | h
  · have := hg5_waist_lt_mark ⟨i.val + 1, by omega⟩ j (by simp; omega); linarith
  · have := hg5_markRe_strictMono.monotone (show j ≤ (⟨i.val, hi⟩ : Fin 12) from h); linarith

theorem hg5_noWaistB (i : Fin 13) (hi : i.val < 12) (x : ℝ) (h1 : hg5_markRe ⟨i.val, hi⟩ < x)
    (h2 : x < hg3_waist ⟨i.val + 1, by omega⟩) (j : Fin 13) : x ≠ hg3_waist j := by
  rintro rfl
  rcases Nat.lt_or_ge i.val j.val with h | h
  · have := hg5_waist_strictMono.monotone
      (show (⟨i.val + 1, by omega⟩ : Fin 13) ≤ j from by rw [Fin.le_def]; simp; omega)
    linarith
  · have := hg5_waist_lt_mark j ⟨i.val, hi⟩ h; linarith

/-- Points of open triangles avoid the lines of the edges. -/
theorem hg5_triReg_avoid (τ : hg2_Tri Unit 13) (w : ℂ) (h : hg5_triReg τ w) :
    (w.re + 11 / 2 ≠ 0 ∨ |w.im| < 10) ∧
      (|w.im| < 10 → (∀ j, hg5_rho w ≠ hg5_markRe j) ∧ ∀ j, hg5_rho w ≠ hg3_waist j) := by
  rcases τ with ⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩ <;> simp only [hg5_triReg] at h <;> split_ifs at h with hi
  · exact ⟨Or.inr h.1, fun _ ↦ ⟨hg5_noMarkA i hi _ h.2.2.1 h.2.2.2,
      hg5_noWaistA i hi _ h.2.2.1 h.2.2.2⟩⟩
  · refine ⟨Or.inl h.1.ne', fun hy ↦ ⟨fun j ↦ ?_, fun j ↦ ?_⟩⟩
    · have := (hg5_mark_bounds' j).2; have := h.2 hy; exact ne_of_gt (by linarith)
    · have := hg5_waist_le_12 j; have := h.2 hy; exact ne_of_gt (by linarith)
  · exact ⟨Or.inr h.1, fun _ ↦ ⟨hg5_noMarkB i hi _ h.2.2.1 h.2.2.2,
      hg5_noWaistB i hi _ h.2.2.1 h.2.2.2⟩⟩
  · refine ⟨Or.inl h.1.ne, fun hy ↦ ⟨fun j ↦ ?_, fun j ↦ ?_⟩⟩
    · have := (hg5_mark_bounds' j).1; have := h.2 hy; exact ne_of_lt (by linarith)
    · have := hg5_waist_ge_0 j; have := h.2 hy; exact ne_of_lt (by linarith)


/-! ## Statement 5: the open edges -/

/-- The open region of a base edge at parameter `s`, in the plane coordinates. -/
def hg5_edgeReg : hg2_Edge Unit 13 → ℝ → ℂ → Prop
  | Sum.inl (i, _), s, w => if h : i.val < 12 then
      0 < w.im ∧ w.im < 10 ∧ w.im = 10 * (1 - s) ∧ hg5_rho w = hg5_markRe ⟨i.val, h⟩
    else w.re + 11 / 2 = 0 ∧ 10 < w.im ∧ w.im = 10 / (1 - s)
  | Sum.inr (Sum.inl (i, _)), s, w =>
      -10 < w.im ∧ w.im < 10 ∧ w.im = 10 * (1 - 2 * s) ∧ hg5_rho w = hg3_waist i
  | Sum.inr (Sum.inr (i, _)), s, w => if h : i.val < 12 then
      -10 < w.im ∧ w.im < 0 ∧ w.im = -10 * s ∧ hg5_rho w = hg5_markRe ⟨i.val, h⟩
    else w.re + 11 / 2 = 0 ∧ w.im < -10 ∧ w.im = -10 / s

theorem hg5_edge_open (ε : hg2_Edge Unit 13) (s : unitInterval) (hs : s ∈ Set.Ioo 0 1) :
    ∃ w : ℂ, hg5_edge ε s = ((w : ℂ) : OnePoint ℂ) ∧ hg5_edgeReg ε s w := by
  have hs0 : 0 < (s : ℝ) := hs.1
  have hs1 : (s : ℝ) < 1 := hs.2
  rcases ε with ⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩
  · rcases hg5_fin13_cases i with h | rfl
    · refine ⟨_, hg5_edgeE_lt i h s, ?_⟩
      simp only [hg5_edgeReg, dif_pos h]
      simp only [hg5_rho, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
        zero_add, add_re, mul_re, sub_zero, add_zero]
      refine ⟨by nlinarith, by nlinarith, trivial, ?_⟩
      rw [abs_of_pos (by nlinarith)]
      have : 1 - 10 * (1 - (s : ℝ)) / 10 = s := by ring
      rw [this]
      field_simp
      ring
    · refine ⟨_, hg5_edgeE_12_lt s hs1.ne, ?_⟩
      simp only [hg5_edgeReg, show ¬ (12 : Fin 13).val < 12 by decide, dite_false]
      simp only [add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, mr_centre]
      refine ⟨by norm_num, ?_, by simp⟩
      have : 0 < 1 - (s : ℝ) := by linarith
      norm_num
      rw [lt_div_iff₀ this]; linarith
  · refine ⟨_, hg5_edgeF_eq i s, ?_⟩
    simp only [hg5_edgeReg]
    simp only [hg5_rho, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
      zero_add, add_re, mul_re, sub_zero, add_zero]
    have hab : |1 - 2 * (s : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
    refine ⟨by nlinarith [abs_lt.mp hab], by nlinarith [abs_lt.mp hab], trivial, ?_⟩
    rw [abs_mul, show |(10 : ℝ)| = 10 by norm_num]
    have : 1 - 10 * |1 - 2 * (s : ℝ)| / 10 = 1 - |1 - 2 * (s : ℝ)| := by ring
    rw [this]
    have hl : 1 - |1 - 2 * (s : ℝ)| ≠ 0 := by linarith
    field_simp
    ring
  · rcases hg5_fin13_cases i with h | rfl
    · refine ⟨_, hg5_edgeH_lt i h s, ?_⟩
      simp only [hg5_edgeReg, dif_pos h]
      simp only [hg5_rho, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
        zero_add, add_re, mul_re, sub_zero, add_zero]
      refine ⟨by nlinarith, by nlinarith, trivial, ?_⟩
      rw [abs_of_neg (by nlinarith)]
      have : 1 - -(-10 * (s : ℝ)) / 10 = 1 - s := by ring
      rw [this]
      have hl : 1 - (s : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    · refine ⟨_, hg5_edgeH_12_pos s hs0.ne', ?_⟩
      simp only [hg5_edgeReg, show ¬ (12 : Fin 13).val < 12 by decide, dite_false]
      simp only [sub_re, sub_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, mr_centre]
      refine ⟨by norm_num, ?_, by simp [neg_div]⟩
      norm_num
      rw [lt_div_iff₀ hs0]; linarith

theorem hg5_edgeReg_unique (ε ε' : hg2_Edge Unit 13) (s s' : ℝ) (hs : s ∈ Set.Ioo 0 1)
    (hs' : s' ∈ Set.Ioo 0 1) (w : ℂ) (h : hg5_edgeReg ε s w) (h' : hg5_edgeReg ε' s' w) :
    ε = ε' ∧ s = s' := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hs0', hs1'⟩ := hs'
  have e1 : 10 < 10 / (1 - s') := by rw [lt_div_iff₀ (by linarith)]; linarith
  have e2 : 10 < 10 / s' := by rw [lt_div_iff₀ hs0']; linarith
  have e3 : 10 < 10 / (1 - s) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have e4 : 10 < 10 / s := by rw [lt_div_iff₀ hs0]; linarith
  rcases ε with ⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩ <;> rcases ε' with ⟨j, ⟨⟩⟩ | ⟨j, ⟨⟩⟩ | ⟨j, ⟨⟩⟩ <;>
    simp only [hg5_edgeReg] at h h' <;> (try split_ifs at h with hi) <;>
    (try split_ifs at h' with hj) <;> casesm* _ ∧ _
  all_goals first
    | (exfalso; linarith)
    | (exfalso; exact hg5_waist_ne_mark _ _
        ((‹hg5_rho w = hg3_waist _›).symm.trans ‹hg5_rho w = hg5_markRe _›))
    | (refine ⟨?_, by linarith⟩
       have := hg5_markRe_injective
         ((‹hg5_rho w = hg5_markRe ⟨i.val, _⟩›).symm.trans ‹hg5_rho w = hg5_markRe ⟨j.val, _⟩›)
       have hij : i = j := Fin.ext (by simpa using this)
       rw [hij])
    | (refine ⟨?_, by linarith⟩
       have hij := hg5_waist_injective
         ((‹hg5_rho w = hg3_waist i›).symm.trans ‹hg5_rho w = hg3_waist j›)
       rw [hij])
    | (have := i.isLt; have := j.isLt
       have hij : i = j := Fin.ext (by omega)
       refine ⟨by rw [hij], ?_⟩
       have hw : 10 / (1 - s) = 10 / (1 - s') := by linarith
       have h1 : 1 - s ≠ 0 := by linarith
       have h2 : 1 - s' ≠ 0 := by linarith
       field_simp at hw
       linarith)
    | (have := i.isLt; have := j.isLt
       have hij : i = j := Fin.ext (by omega)
       refine ⟨by rw [hij], ?_⟩
       have hw : -10 / s = -10 / s' := by linarith
       field_simp at hw
       linarith)


/-- The points of the edge lines: the vertical line `Re = -11/2` outside the strip, or a point of
the strip on a profile through a mark or a waist. -/
def hg5_onLines (z : OnePoint ℂ) : Prop :=
  z = OnePoint.infty ∨ ∃ w : ℂ, z = ((w : ℂ) : OnePoint ℂ) ∧
    ((w.re + 11 / 2 = 0 ∧ 10 ≤ |w.im|) ∨
      (|w.im| < 10 ∧ ((∃ j, hg5_rho w = hg5_markRe j) ∨ ∃ j, hg5_rho w = hg3_waist j)))

theorem hg5_vert_onLines (v : hg2_Vert hg5_one) : hg5_onLines (hg5_vert v) := by
  rcases v with _ | _ | ⟨i, _⟩
  · refine Or.inr ⟨mr_basePoint, rfl, Or.inl ⟨by simp [mr_basePoint, mr_centre]; norm_num, ?_⟩⟩
    simp [mr_basePoint, mr_centre]
  · refine Or.inr ⟨hg3_bottom, rfl, Or.inl ⟨by simp [hg3_bottom, mr_centre]; norm_num, ?_⟩⟩
    simp [hg3_bottom, mr_centre]
  · rcases hg5_fin13_cases i with h | rfl
    · refine Or.inr ⟨(hg5_markRe ⟨i.val, h⟩ : ℂ), hg5_branch_lt i h, Or.inr ⟨by simp,
        Or.inl ⟨⟨i.val, h⟩, ?_⟩⟩⟩
      simp [hg5_rho]; ring
    · exact Or.inl rfl

theorem hg5_unit_ends (s : unitInterval) (hs : s ∉ Set.Ioo 0 1) : s = 0 ∨ s = 1 := by
  rw [hg5_unit_eq_zero, hg5_unit_eq_one]
  rcases eq_or_lt_of_le s.2.1 with h | h
  · exact Or.inl h.symm
  · rcases eq_or_lt_of_le s.2.2 with h' | h'
    · exact Or.inr h'
    · exact absurd ⟨h, h'⟩ hs

theorem hg5_edge_onLines (ε : hg2_Edge Unit 13) (s : unitInterval) :
    hg5_onLines (hg5_edge ε s) := by
  by_cases hs : s ∈ Set.Ioo 0 1
  · obtain ⟨w, hw, hr⟩ := hg5_edge_open ε s hs
    rw [hw]
    refine Or.inr ⟨w, rfl, ?_⟩
    rcases ε with ⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩ <;> simp only [hg5_edgeReg] at hr <;>
      (try split_ifs at hr with hi) <;> casesm* _ ∧ _
    · exact Or.inr ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, Or.inl ⟨_, ‹_›⟩⟩
    · exact Or.inl ⟨‹_›, by rw [abs_of_pos (by linarith)]; linarith⟩
    · exact Or.inr ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, Or.inr ⟨_, ‹_›⟩⟩
    · exact Or.inr ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, Or.inl ⟨_, ‹_›⟩⟩
    · exact Or.inl ⟨‹_›, by rw [abs_of_neg (by linarith)]; linarith⟩
  · rcases hg5_unit_ends s hs with rfl | rfl
    · rw [(hg5_edge_ends_proof ε).1]; exact hg5_vert_onLines _
    · rw [(hg5_edge_ends_proof ε).2]; exact hg5_vert_onLines _

theorem hg5_edgeReg_im (ε : hg2_Edge Unit 13) (s : ℝ) (w : ℂ) (h : hg5_edgeReg ε s w) :
    w.im ≠ 10 ∧ w.im ≠ -10 := by
  rcases ε with ⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩ <;> simp only [hg5_edgeReg] at h <;>
    (try split_ifs at h with hi) <;> casesm* _ ∧ _ <;> constructor <;> intro <;> linarith

theorem hg5_branch_injective : Function.Injective (b6_branch mr_base) := by
  intro i j h
  rcases hg5_fin13_cases i with hi | rfl <;> rcases hg5_fin13_cases j with hj | rfl
  · rw [hg5_branch_lt i hi, hg5_branch_lt j hj] at h
    have := hg5_markRe_injective (Complex.ofReal_injective (OnePoint.coe_injective h))
    exact Fin.ext (by simpa using this)
  · rw [hg5_branch_lt i hi, hg5_branch_12] at h; exact absurd h (OnePoint.coe_ne_infty _)
  · rw [hg5_branch_lt j hj, hg5_branch_12] at h; exact absurd h.symm (OnePoint.coe_ne_infty _)
  · rfl

theorem hg5_vert_injective : Function.Injective hg5_vert := by
  have hb0 : ((mr_basePoint : ℂ) : OnePoint ℂ) ∉ Set.range (b6_branch mr_base) := by
    rw [hg5_coe_mark_iff]; simp [mr_basePoint, mr_centre]
  have hb1 : ((hg3_bottom : ℂ) : OnePoint ℂ) ∉ Set.range (b6_branch mr_base) := by
    rw [hg5_coe_mark_iff]; simp [hg3_bottom, mr_centre]
  have h01 : ((mr_basePoint : ℂ) : OnePoint ℂ) ≠ ((hg3_bottom : ℂ) : OnePoint ℂ) := by
    intro h
    have := congrArg Complex.im (OnePoint.coe_injective h)
    simp [mr_basePoint, hg3_bottom, mr_centre] at this
    norm_num at this
  intro v v' h
  rcases v with ⟨⟩ | ⟨⟩ | ⟨i, c⟩ <;> rcases v' with ⟨⟩ | ⟨⟩ | ⟨j, c'⟩ <;>
    simp only [hg5_vert] at h
  · rfl
  · exact absurd h h01
  · exact absurd ⟨j, h.symm⟩ hb0
  · exact absurd h.symm h01
  · rfl
  · exact absurd ⟨j, h.symm⟩ hb1
  · exact absurd ⟨i, h⟩ hb0
  · exact absurd ⟨i, h⟩ hb1
  · have hij := hg5_branch_injective h
    subst hij
    have : c = c' := Subsingleton.elim _ _
    rw [this]

theorem hg5_open_cells_proof :
    (∀ (τ τ' : hg2_Tri Unit 13) (a a' : StdSimplex ℝ (Fin 3)),
        (∀ k, 0 < a.weights k) → (∀ k, 0 < a'.weights k) →
          hg5_tri τ a = hg5_tri τ' a' → τ = τ') ∧
      (∀ (τ : hg2_Tri Unit 13) (a : StdSimplex ℝ (Fin 3)), (∀ k, 0 < a.weights k) →
        ∀ (ε : hg2_Edge Unit 13) (s : unitInterval), hg5_tri τ a ≠ hg5_edge ε s) ∧
      (∀ (ε ε' : hg2_Edge Unit 13) (s s' : unitInterval), s ∈ Set.Ioo 0 1 →
        s' ∈ Set.Ioo 0 1 → hg5_edge ε s = hg5_edge ε' s' → ε = ε' ∧ s = s') ∧
      (∀ (ε : hg2_Edge Unit 13) (s : unitInterval), s ∈ Set.Ioo 0 1 →
        ∀ v, hg5_edge ε s ≠ hg5_vert v) ∧
      Function.Injective hg5_vert := by
  refine ⟨?_, ?_, ?_, ?_, hg5_vert_injective⟩
  · intro τ τ' a a' ha ha' h
    obtain ⟨w, hw, hr⟩ := hg5_tri_int τ a ha
    obtain ⟨w', hw', hr'⟩ := hg5_tri_int τ' a' ha'
    rw [hw, hw'] at h
    rw [OnePoint.coe_injective h] at hr
    exact hg5_triReg_unique τ τ' w' hr hr'
  · intro τ a ha ε s h
    obtain ⟨w, hw, hr⟩ := hg5_tri_int τ a ha
    have hav := hg5_triReg_avoid τ w hr
    rcases hg5_edge_onLines ε s with h' | ⟨w', hw', h'⟩
    · rw [← h, hw] at h'; exact OnePoint.coe_ne_infty _ h'
    · rw [← h, hw] at hw'
      rw [← OnePoint.coe_injective hw'] at h'
      rcases h' with ⟨h1, h2⟩ | ⟨h1, ⟨j, hj⟩ | ⟨j, hj⟩⟩
      · rcases hav.1 with h3 | h3
        · exact h3 h1
        · linarith
      · exact (hav.2 h1).1 j hj
      · exact (hav.2 h1).2 j hj
  · intro ε ε' s s' hs hs' h
    obtain ⟨w, hw, hr⟩ := hg5_edge_open ε s hs
    obtain ⟨w', hw', hr'⟩ := hg5_edge_open ε' s' hs'
    rw [hw, hw'] at h
    rw [OnePoint.coe_injective h] at hr
    obtain ⟨he, hs⟩ := hg5_edgeReg_unique ε ε' s s' hs hs' w' hr hr'
    exact ⟨he, Subtype.ext hs⟩
  · intro ε s hs v h
    have hnm : hg5_edge ε s ∉ Set.range (b6_branch mr_base) := by
      rw [hg5_edge_marks_proof]
      rintro (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩)
      · exact lt_irrefl _ hs.2
      · exact lt_irrefl _ hs.1
    obtain ⟨w, hw, hr⟩ := hg5_edge_open ε s hs
    have him := hg5_edgeReg_im ε s w hr
    rcases v with _ | _ | ⟨i, _⟩
    · rw [hw] at h
      have := congrArg Complex.im (OnePoint.coe_injective h)
      simp [mr_basePoint, mr_centre] at this
      exact him.1 this
    · rw [hw] at h
      have := congrArg Complex.im (OnePoint.coe_injective h)
      simp [hg3_bottom, mr_centre] at this
      exact him.2 this
    · exact hnm ⟨i, h.symm⟩


/-! ## Statement 6: the cover -/

theorem hg5_wedge_hits (u v : ℝ) (huv : u ≠ v) (w : ℂ) (hy : |w.im| < 10)
    (hθ0 : 0 ≤ (hg5_rho w - u) / (v - u)) (hθ1 : (hg5_rho w - u) / (v - u) ≤ 1) :
    ∃ a : StdSimplex ℝ (Fin 3), hg5_wedge u v a = w := by
  set l := 1 - |w.im| / 10 with hl
  have hl0 : 0 < l := by rw [hl]; linarith
  set θ := (hg5_rho w - u) / (v - u) with hθ
  have hd : |w.im / 10| = 1 - l := by rw [hl, abs_div]; norm_num
  have hy' := abs_le.mp (le_of_eq hd)
  have hθl : 0 ≤ θ * l := mul_nonneg hθ0 hl0.le
  have hθl' : θ * l ≤ l := by nlinarith
  refine ⟨hg5_pt ((1 - θ * l + w.im / 10) / 2) (θ * l) ((1 - θ * l - w.im / 10) / 2)
    (by linarith) hθl (by linarith) (by ring), ?_⟩
  rw [hg5_wedge_apply]
  simp only [hg5_pt_w0, hg5_pt_w1, hg5_pt_w2]
  have e1 : (1 - θ * l + w.im / 10) / 2 - (1 - θ * l - w.im / 10) / 2 = w.im / 10 := by ring
  rw [e1, hd]
  have huv' : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have hρ : hg5_rho w = -11 / 2 + (w.re + 11 / 2) / l := by rw [hg5_rho]
  apply Complex.ext
  · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero]
    rw [hθ, hρ]
    field_simp
    ring
  · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_one, zero_add, mul_zero]
    ring

theorem hg5_min_half (S d : ℝ) : min ((S + d) / 2) ((S - d) / 2) = (S - |d|) / 2 := by
  rcases le_total 0 d with h | h
  · rw [abs_of_nonneg h, min_eq_right (by linarith)]
  · rw [abs_of_nonpos h, min_eq_left (by linarith)]; ring

theorem hg5_cone_hits (i : Fin 13) (hi : hg3_waist i + 11 / 2 ≠ 0)
    (h7 : |hg3_waist i + 11 / 2| = 7) (w : ℂ) (hN : 1 ≤ hg5_N w)
    (hsg : 0 ≤ (w.re + 11 / 2) * (hg3_waist i + 11 / 2)) :
    ∃ a : StdSimplex ℝ (Fin 3), hg5_cone i hi a = ((w : ℂ) : OnePoint ℂ) := by
  set N := hg5_N w with hNdef
  have hN0 : 0 < N := by linarith
  set S := 1 / N with hS
  have hS0 : 0 < S := by rw [hS]; positivity
  have hS1 : S ≤ 1 := by rw [hS, div_le_one hN0]; exact hN
  have hSN : S * N = 1 := by rw [hS]; field_simp
  set d := w.im * S ^ 2 / 10 with hd
  have hNd : |w.im| / 10 ≤ N := by
    rw [hNdef, hg5_N]; have := abs_nonneg (w.re + 11 / 2); linarith
  have hdS : |d| ≤ S := by
    rw [hd, abs_div, abs_mul, abs_of_pos (pow_pos hS0 2), abs_of_pos (by norm_num : (0 : ℝ) < 10)]
    have : |w.im| / 10 * S ≤ 1 := by
      calc |w.im| / 10 * S ≤ N * S := by nlinarith
        _ = 1 := by rw [mul_comm]; exact hSN
    nlinarith
  have hdS' := abs_le.mp hdS
  set a := hg5_pt ((S + d) / 2) (1 - S) ((S - d) / 2) (by linarith) (by linarith) (by linarith)
    (by ring) with ha
  have haS : a.weights 0 + a.weights 2 = S := by simp [ha]; ring
  obtain ⟨w', hw', hre, him⟩ := hg5_cone_pt i hi a (by rw [haS]; exact hS0)
  refine ⟨a, ?_⟩
  rw [hw']
  congr 1
  rw [haS] at hre him
  have hm : min (a.weights 0) (a.weights 2) = (S - |d|) / 2 := by
    simp only [ha, hg5_pt_w0, hg5_pt_w2]; exact hg5_min_half S d
  rw [hm] at hre
  have hS2 : S ^ 2 ≠ 0 := (pow_pos hS0 2).ne'
  apply Complex.ext
  · -- `S - |d| = S² |X| / 7`
    have hX : S - |d| = S ^ 2 * |w.re + 11 / 2| / 7 := by
      have e : |d| = S ^ 2 * |w.im| / 10 := by
        rw [hd, abs_div, abs_mul, abs_of_pos (pow_pos hS0 2),
          abs_of_pos (by norm_num : (0 : ℝ) < 10)]; ring
      rw [e]
      have : S * (|w.re + 11 / 2| / 7 + |w.im| / 10) = 1 := by rw [← hg5_N, ← hNdef]; exact hSN
      nlinarith
    rw [hX] at hre
    have hre' : w'.re + 11 / 2 = (hg3_waist i + 11 / 2) * |w.re + 11 / 2| / 7 := by
      rw [hre]; field_simp
    have hsgn : (hg3_waist i + 11 / 2) * |w.re + 11 / 2| = 7 * (w.re + 11 / 2) := by
      rcases le_or_gt 0 (hg3_waist i + 11 / 2) with hk | hk
      · rw [abs_of_nonneg hk] at h7
        have hX0 : 0 ≤ w.re + 11 / 2 := by
          by_contra hc; push Not at hc; nlinarith
        rw [abs_of_nonneg hX0, h7]
      · rw [abs_of_neg hk] at h7
        have hX0 : w.re + 11 / 2 ≤ 0 := by
          by_contra hc; push Not at hc; nlinarith
        rw [abs_of_nonpos hX0]
        have : hg3_waist i + 11 / 2 = -7 := by linarith
        rw [this]; ring
    rw [hsgn] at hre'
    linarith
  · have e : a.weights 0 - a.weights 2 = d := by simp [ha]; ring
    rw [him, e, hd]; field_simp

theorem hg5_N_lt_one (w : ℂ) (hN : hg5_N w < 1) :
    |w.im| < 10 ∧ -25 / 2 < hg5_rho w ∧ hg5_rho w < 3 / 2 := by
  have hX := abs_nonneg (w.re + 11 / 2)
  have hY : |w.im| < 10 := by unfold hg5_N at hN; linarith
  refine ⟨hY, ?_⟩
  have hl : 0 < 1 - |w.im| / 10 := by linarith
  have hX7 : |w.re + 11 / 2| < 7 * (1 - |w.im| / 10) := by unfold hg5_N at hN; linarith
  have hb := abs_lt.mp hX7
  have h1 : -7 < (w.re + 11 / 2) / (1 - |w.im| / 10) := by rw [lt_div_iff₀ hl]; linarith
  have h2 : (w.re + 11 / 2) / (1 - |w.im| / 10) < 7 := by rw [div_lt_iff₀ hl]; linarith
  unfold hg5_rho
  constructor <;> linarith

theorem hg5_find_interval (x : ℝ) (h0 : -25 / 2 < x) (h1 : x < 3 / 2) :
    ∃ i : Fin 13, ∃ h : i.val < 12, hg3_waist i ≤ x ∧ x < hg3_waist ⟨i.val + 1, by omega⟩ := by
  classical
  set J := (Finset.univ : Finset (Fin 13)).filter (fun j ↦ hg3_waist j ≤ x) with hJ
  have hne : J.Nonempty := ⟨0, by simp [hJ, hg5_waist_0]; linarith⟩
  set j := J.max' hne with hjdef
  have hjJ : j ∈ J := J.max'_mem hne
  have hj : hg3_waist j ≤ x := by simpa [hJ] using hjJ
  have hj12 : j.val < 12 := by
    by_contra hc
    have : j = 12 := Fin.ext (by have := j.isLt; simp; omega)
    rw [this, hg5_waist_12] at hj
    linarith
  refine ⟨j, hj12, hj, ?_⟩
  by_contra hc
  push Not at hc
  have hmem : (⟨j.val + 1, by omega⟩ : Fin 13) ∈ J := by simp [hJ, hc]
  have := J.le_max' _ hmem
  rw [← hjdef, Fin.le_def] at this
  simp at this

theorem hg5_cover_proof (z : OnePoint ℂ) :
    ∃ (τ : hg2_Tri Unit 13) (a : StdSimplex ℝ (Fin 3)), hg5_tri τ a = z := by
  induction z using OnePoint.rec with
  | infty =>
    refine ⟨Sum.inl (12, ()), StdSimplex.single 1, ?_⟩
    simp [hg5_tri, hg5_triA_12, hg5_cone, hg5_coneFun, hg5_chartInv_zero]
  | coe w =>
    rcases le_or_gt 1 (hg5_N w) with hN | hN
    · rcases le_or_gt 0 (w.re + 11 / 2) with hX | hX
      · obtain ⟨a, ha⟩ := hg5_cone_hits 12 hg5_waist12_ne (hg5_waist_abs7 12 (Or.inr rfl)) w hN
          (by rw [hg5_waist_12]; nlinarith)
        exact ⟨Sum.inl (12, ()), a, by simp only [hg5_tri, hg5_triA_12]; exact ha⟩
      · obtain ⟨a, ha⟩ := hg5_cone_hits 0 hg5_waist0_ne (hg5_waist_abs7 0 (Or.inl rfl)) w hN
          (by rw [hg5_waist_0]; nlinarith)
        exact ⟨Sum.inr (12, ()), a, by simp only [hg5_tri, hg5_triB_12]; exact ha⟩
    · obtain ⟨hy, hr0, hr1⟩ := hg5_N_lt_one w hN
      obtain ⟨i, hi, hwi, hwi'⟩ := hg5_find_interval _ hr0 hr1
      have hp := hg5_waist_lt_mark_self i hi
      have hp' := hg5_mark_lt_waist_succ i hi
      rcases le_or_gt (hg5_rho w) (hg5_markRe ⟨i.val, hi⟩) with hm | hm
      · obtain ⟨a, ha⟩ := hg5_wedge_hits (hg3_waist i) (hg5_markRe ⟨i.val, hi⟩) hp.ne w hy
          (div_nonneg (by linarith) (by linarith))
          ((div_le_one (by linarith)).mpr (by linarith))
        exact ⟨Sum.inl (i, ()), a, by simp only [hg5_tri, hg5_triA_lt i hi, ha]⟩
      · obtain ⟨a, ha⟩ := hg5_wedge_hits (hg3_waist ⟨i.val + 1, by omega⟩)
          (hg5_markRe ⟨i.val, hi⟩) hp'.ne' w hy
          (div_nonneg_of_nonpos (by linarith) (by linarith))
          ((div_le_one_of_neg (by linarith)).mpr (by linarith))
        refine ⟨Sum.inr (i, ()), a, ?_⟩
        simp only [hg5_tri, hg5_triB_lt i hi, hg5_waist_succ i hi, ha]


/-! ## The triangles and the marks -/

theorem hg5_face_vertex {T : Type} [TopologicalSpace T] (σ : C(StdSimplex ℝ (Fin 3), T)) :
    hg5_face σ 2 0 = σ (StdSimplex.single 0) ∧ hg5_face σ 2 1 = σ (StdSimplex.single 1) ∧
      hg5_face σ 1 0 = σ (StdSimplex.single 0) ∧ hg5_face σ 1 1 = σ (StdSimplex.single 2) ∧
      hg5_face σ 0 0 = σ (StdSimplex.single 1) ∧ hg5_face σ 0 1 = σ (StdSimplex.single 2) := by
  simp only [hg5_face_apply, StdSimplex.homeomorphI_symm_zero, StdSimplex.homeomorphI_symm_one,
    StdSimplex.map_single]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hg5_tri_single0 (τ : hg2_Tri Unit 13) :
    hg5_tri τ (StdSimplex.single 0) = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
  rw [← (hg5_face_vertex (hg5_tri τ)).1, (hg5_faces_proof τ).2.2,
    (hg5_edge_ends_proof _).1]
  rcases τ with ⟨i, _⟩ | ⟨i, _⟩ <;> rfl

theorem hg5_tri_single2 (τ : hg2_Tri Unit 13) :
    hg5_tri τ (StdSimplex.single 2) = ((hg3_bottom : ℂ) : OnePoint ℂ) := by
  rw [← (hg5_face_vertex (hg5_tri τ)).2.2.2.1, (hg5_faces_proof τ).2.1,
    (hg5_edge_ends_proof _).2]
  rcases τ with ⟨i, _⟩ | ⟨i, _⟩ <;> rfl

theorem hg5_tri_single1 (i : Fin 13) (u : Unit) :
    hg5_tri (Sum.inl (i, u)) (StdSimplex.single 1) = b6_branch mr_base i ∧
      hg5_tri (Sum.inr (i, u)) (StdSimplex.single 1) = b6_branch mr_base i := by
  constructor
  · rw [← (hg5_face_vertex _).2.1, (hg5_faces_proof _).2.2, (hg5_edge_ends_proof _).2]; rfl
  · rw [← (hg5_face_vertex _).2.1, (hg5_faces_proof _).2.2, (hg5_edge_ends_proof _).2]; rfl

theorem hg5_wedge_marks (u v : ℝ) (huv : u ≠ v) (i : Fin 13) (hi : i.val < 12)
    (hv : v = hg5_markRe ⟨i.val, hi⟩)
    (hint : ∀ x : ℝ, ((u ≤ x ∧ x < v) ∨ (v < x ∧ x ≤ u)) → ∀ j, x ≠ hg5_markRe j)
    (a : StdSimplex ℝ (Fin 3)) :
    ((hg5_wedge u v a : ℂ) : OnePoint ℂ) ∈ Set.range (b6_branch mr_base) ↔
      a = StdSimplex.single 1 := by
  rw [hg5_coe_mark_iff, hg5_eq_single1]
  have hs := hg5_sum3 a
  have h0 := a.weights_nonneg 0
  have h2 := a.weights_nonneg 2
  have h1 := a.weights_nonneg 1
  simp only [hg5_wedge_apply, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
    mul_one, zero_add, add_re, mul_re, sub_zero, add_zero]
  constructor
  · rintro ⟨him, j, hre⟩
    have hd : a.weights 0 - a.weights 2 = 0 := by linarith
    rw [hd, abs_zero] at hre
    by_contra hne
    have ha1 : a.weights 1 < 1 := lt_of_le_of_ne (by linarith) hne
    apply hint (u + (v - u) * a.weights 1) _ j (by linarith)
    rcases lt_or_gt_of_ne huv with h | h
    · left; constructor <;> nlinarith
    · right; constructor <;> nlinarith
  · intro ha1
    have ha0 : a.weights 0 = 0 := by linarith
    have ha2 : a.weights 2 = 0 := by linarith
    refine ⟨by rw [ha0, ha2]; ring, ⟨i.val, hi⟩, ?_⟩
    rw [ha0, ha2, ha1, ← hv]; ring

theorem hg5_S_zero_iff (a : StdSimplex ℝ (Fin 3)) :
    a.weights 0 + a.weights 2 = 0 ↔ a = StdSimplex.single 1 := by
  rw [hg5_eq_single1]
  have := hg5_sum3 a
  have := a.weights_nonneg 0
  have := a.weights_nonneg 2
  constructor <;> intro h <;> linarith

theorem hg5_cone_marks (i : Fin 13) (hi : hg3_waist i + 11 / 2 ≠ 0)
    (h7 : |hg3_waist i + 11 / 2| = 7) (a : StdSimplex ℝ (Fin 3)) :
    hg5_cone i hi a ∈ Set.range (b6_branch mr_base) ↔ a = StdSimplex.single 1 := by
  constructor
  · intro hm
    by_contra hne
    have hS : 0 < a.weights 0 + a.weights 2 := by
      rcases (eq_or_lt_of_le (add_nonneg (a.weights_nonneg 0) (a.weights_nonneg 2))) with h | h
      · exact absurd ((hg5_S_zero_iff a).mp h.symm) hne
      · exact h
    obtain ⟨w, hw, hre, him⟩ := hg5_cone_pt i hi a hS
    have hN := hg5_cone_N i h7 a hS w hre him
    have hS1 : a.weights 0 + a.weights 2 ≤ 1 := by
      have := hg5_sum3 a; have := a.weights_nonneg 1; linarith
    have hN1 : 1 ≤ hg5_N w := by rw [hN, le_div_iff₀ hS]; linarith
    rw [hw, hg5_coe_mark_iff] at hm
    obtain ⟨h0, j, hj⟩ := hm
    have hb := hg5_markRe_bounds j
    have : hg5_N w < 1 := by
      rw [hg5_N, h0, hj, abs_zero]
      have : |hg5_markRe j + 11 / 2| < 7 := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith
    linarith
  · rintro rfl
    have : hg5_cone i hi (StdSimplex.single 1) = OnePoint.infty := by
      simp [hg5_cone, hg5_coneFun, hg5_chartInv_zero]
    rw [this]; exact ⟨12, rfl⟩

theorem hg5_tri_marks (τ : hg2_Tri Unit 13) (a : StdSimplex ℝ (Fin 3)) :
    hg5_tri τ a ∈ Set.range (b6_branch mr_base) ↔ a = StdSimplex.single 1 := by
  rcases τ with ⟨i, _⟩ | ⟨i, _⟩
  · rcases hg5_fin13_cases i with h | rfl
    · simp only [hg5_tri, hg5_triA_lt i h]
      refine hg5_wedge_marks _ _ (hg5_waist_ne_mark _ _) i h rfl ?_ a
      rintro x (⟨h1, h2⟩ | ⟨h1, h2⟩) j
      · rcases eq_or_lt_of_le h1 with e | e
        · rw [← e]; exact hg5_waist_ne_mark _ _
        · exact hg5_noMarkA i h x e h2 j
      · have := hg5_waist_lt_mark_self i h; linarith
    · simp only [hg5_tri, hg5_triA_12]
      exact hg5_cone_marks _ _ (hg5_waist_abs7 12 (Or.inr rfl)) a
  · rcases hg5_fin13_cases i with h | rfl
    · simp only [hg5_tri, hg5_triB_lt i h, hg5_waist_succ i h]
      refine hg5_wedge_marks _ _ (hg5_waist_ne_mark _ _) i h rfl ?_ a
      rintro x (⟨h1, h2⟩ | ⟨h1, h2⟩) j
      · have := hg5_mark_lt_waist_succ i h; linarith
      · rcases eq_or_lt_of_le h2 with e | e
        · rw [e]; exact hg5_waist_ne_mark _ _
        · exact hg5_noMarkB i h x h1 e j
    · simp only [hg5_tri, hg5_triB_12]
      exact hg5_cone_marks _ _ (hg5_waist_abs7 0 (Or.inl rfl)) a

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLoopRepresentatives

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
open Convexity Set

theorem b6m_pathChain_convex_chart {T E : Type} [TopologicalSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph T E) {U : Set E} (hU : Convex ℝ U)
    (hUt : U ⊆ e.target) {u : E} (hu : u ∈ U)
    (g : C(unitInterval, T)) (hgs : ∀ t, g t ∈ e.source) (hgU : ∀ t, e (g t) ∈ U) :
    b6m_pathChain g = b6m_pathChain (b3Rest2_seg e hU hUt hu (hgU 1)) -
      b6m_pathChain (b3Rest2_seg e hU hUt hu (hgU 0)) := by
  set V : unitInterval → E := fun t ↦ e (g t) - u
  have hV : Continuous V :=
    (e.continuousOn.comp_continuous g.continuous hgs).sub continuous_const
  set w1 : StdSimplex ℝ (Fin 3) → ℝ := fun w ↦ w.weights 1
  set w2 : StdSimplex ℝ (Fin 3) → ℝ := fun w ↦ w.weights 2
  have hw1 : Continuous w1 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 1
  have hw2 : Continuous w2 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 2
  set Φ : StdSimplex ℝ (Fin 3) → E := fun w ↦
    (w1 w + w2 w) • V (Set.projIcc 0 1 zero_le_one (w2 w / (w1 w + w2 w)))
  have hΦ : Continuous Φ := b3Rest2_continuous_cone hw1 hw2
    (fun w ↦ w.weights_nonneg 1) (fun w ↦ w.weights_nonneg 2) hV
  have hmem : ∀ w : StdSimplex ℝ (Fin 3), u + Φ w ∈ U := by
    intro w
    have hs := w.total_of_fintype
    rw [Fin.sum_univ_three] at hs
    have h12 : w1 w + w2 w ∈ Icc (0 : ℝ) 1 :=
      ⟨add_nonneg (w.weights_nonneg 1) (w.weights_nonneg 2), by
        have := w.weights_nonneg 0
        simp only [w1, w2]
        linarith⟩
    exact hU.add_smul_sub_mem hu (hgU _) h12
  let f : C(StdSimplex ℝ (Fin 3), T) :=
    ⟨fun w ↦ e.symm (u + Φ w),
      e.continuousOn_symm.comp_continuous (continuous_const.add hΦ)
        fun w ↦ hUt (hmem w)⟩
  have h := b6m_pathChain_triangle f g (b3Rest2_seg e hU hUt hu (hgU 1))
    (b3Rest2_seg e hU hUt hu (hgU 0)) ?_ ?_ ?_
  · apply sub_eq_zero.mp
    calc
      _ = b6m_pathChain g - b6m_pathChain (b3Rest2_seg e hU hUt hu (hgU 1)) +
          b6m_pathChain (b3Rest2_seg e hU hUt hu (hgU 0)) := by abel
      _ = 0 := h
  all_goals
    intro t
    obtain ⟨⟨w00, w01, w02⟩, ⟨w10, w11, w12⟩, ⟨w20, w21, w22⟩⟩ := b3Rest2_face_weights t
    simp only [f, ContinuousMap.coe_mk, Φ, w1, w2, V, b3Rest2_seg_apply]
  · rw [w01, w02, sub_add_cancel, div_one, one_smul, Set.projIcc_of_mem _ t.2]
    rw [show (⟨(t : ℝ), t.2⟩ : Icc (0 : ℝ) 1) = t from rfl,
      add_sub_cancel, e.left_inv (hgs t)]
  · rw [w11, w12, zero_add]
    by_cases ht : (t : ℝ) = 0
    · rw [ht, zero_smul, zero_smul]
    · rw [div_self ht, Set.projIcc_right]
      rfl
  · rw [w21, w22, add_zero, zero_div, Set.projIcc_left]
    rfl

theorem b6m_pathChain_eq_in_convex_chart {T E : Type} [TopologicalSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph T E) {U : Set E} (hU : Convex ℝ U)
    (hUt : U ⊆ e.target) (g h : C(unitInterval, T))
    (hgs : ∀ t, g t ∈ e.source) (hgU : ∀ t, e (g t) ∈ U)
    (hhs : ∀ t, h t ∈ e.source) (hhU : ∀ t, e (h t) ∈ U)
    (h0 : g 0 = h 0) (h1 : g 1 = h 1) : b6m_pathChain g = b6m_pathChain h := by
  rw [b6m_pathChain_convex_chart e hU hUt (hgU 0) g hgs hgU,
    b6m_pathChain_convex_chart e hU hUt (hgU 0) h hhs hhU]
  congr 1 <;> congr 1 <;> ext t <;> simp only [b3Rest2_seg_apply, h0, h1]

theorem b6m_pathChain_eq_sum {T : Type} [TopologicalSpace T]
    (g : C(unitInterval, T)) {n : ℕ} (hn : 0 < n) :
    b6m_pathChain g = ∑ k ∈ Finset.range n,
      b6m_pathChain (b3Rest2_restr g (b3Rest2_frac n k) (b3Rest2_frac n (k + 1))) := by
  have key : ∀ m ≤ n, b6m_pathChain (b3Rest2_restr g 0 (b3Rest2_frac n m)) =
      ∑ k ∈ Finset.range m,
        b6m_pathChain (b3Rest2_restr g (b3Rest2_frac n k) (b3Rest2_frac n (k + 1))) := by
    intro m hm
    induction m with
    | zero =>
      have h0 : b3Rest2_frac n 0 = 0 := by simp [b3Rest2_frac]
      have he : b3Rest2_restr g 0 0 = ContinuousMap.const unitInterval (g 0) := by
        ext t
        simp [b3Rest2_restr_apply, b3Rest2_affI]
      rw [h0, he, b6m_pathChain_const, Finset.sum_range_zero]
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih (by omega), ← b6m_pathChain_subdiv]
  have h := key n le_rfl
  have h1 : b3Rest2_frac n n = 1 := by
    apply Subtype.ext
    rw [b3Rest2_frac_coe le_rfl hn, div_self (by exact_mod_cast hn.ne')]
    rfl
  rwa [h1, b3Rest2_restr_zero_one] at h

theorem b6m_pathChain_square_in_chart {T E : Type} [TopologicalSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph T E) {U : Set E} (hU : Convex ℝ U)
    (hUt : U ⊆ e.target) {a b c d : T}
    (g : Path a b) (h : Path c d) (p : Path a c) (q : Path b d)
    (hg : ∀ t, g t ∈ e.source ∧ e (g t) ∈ U)
    (hh : ∀ t, h t ∈ e.source ∧ e (h t) ∈ U)
    (hp : ∀ t, p t ∈ e.source ∧ e (p t) ∈ U)
    (hq : ∀ t, q t ∈ e.source ∧ e (q t) ∈ U) :
    b6m_pathChain g.toContinuousMap + b6m_pathChain q.toContinuousMap =
      b6m_pathChain p.toContinuousMap + b6m_pathChain h.toContinuousMap := by
  have mem_trans {x y z : T} (r : Path x y) (s : Path y z)
      (hr : ∀ t, r t ∈ e.source ∧ e (r t) ∈ U)
      (hs : ∀ t, s t ∈ e.source ∧ e (s t) ∈ U) (t : unitInterval) :
      (r.trans s) t ∈ e.source ∧ e ((r.trans s) t) ∈ U := by
    have ht : (r.trans s) t ∈ Set.range r ∪ Set.range s := by
      rw [← Path.trans_range]
      exact ⟨t, rfl⟩
    rcases ht with ⟨u, hu⟩ | ⟨u, hu⟩
    · rw [← hu]
      exact hr u
    · rw [← hu]
      exact hs u
  have he := b6m_pathChain_eq_in_convex_chart e hU hUt
    (g.trans q).toContinuousMap (p.trans h).toContinuousMap
    (fun t ↦ (mem_trans g q hg hq t).1) (fun t ↦ (mem_trans g q hg hq t).2)
    (fun t ↦ (mem_trans p h hp hh t).1) (fun t ↦ (mem_trans p h hp hh t).2)
    (by simp) (by simp)
  rwa [b6m_pathChain_trans, b6m_pathChain_trans] at he

theorem b6m_pathChain_chart_comparison {T E : Type} [TopologicalSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g h : C(unitInterval, T)) {n : ℕ} (hn : 0 < n)
    (e : ℕ → OpenPartialHomeomorph T E) (U : ℕ → Set E)
    (hU : ∀ i, Convex ℝ (U i)) (hUt : ∀ i, U i ⊆ (e i).target)
    (p : ∀ i, Path (g (b3Rest2_frac n i)) (h (b3Rest2_frac n i)))
    (hp : (p n).toContinuousMap = (p 0).toContinuousMap)
    (hg : ∀ i < n, ∀ t,
      b3Rest2_restr g (b3Rest2_frac n i) (b3Rest2_frac n (i + 1)) t ∈ (e i).source ∧
      e i (b3Rest2_restr g (b3Rest2_frac n i) (b3Rest2_frac n (i + 1)) t) ∈ U i)
    (hh : ∀ i < n, ∀ t,
      b3Rest2_restr h (b3Rest2_frac n i) (b3Rest2_frac n (i + 1)) t ∈ (e i).source ∧
      e i (b3Rest2_restr h (b3Rest2_frac n i) (b3Rest2_frac n (i + 1)) t) ∈ U i)
    (hp₀ : ∀ i < n, ∀ t, p i t ∈ (e i).source ∧ e i (p i t) ∈ U i)
    (hp₁ : ∀ i < n, ∀ t, p (i + 1) t ∈ (e i).source ∧ e i (p (i + 1) t) ∈ U i) :
    b6m_pathChain g = b6m_pathChain h := by
  let piece (f : C(unitInterval, T)) (i : ℕ) :
      Path (f (b3Rest2_frac n i)) (f (b3Rest2_frac n (i + 1))) :=
    { toContinuousMap := b3Rest2_restr f (b3Rest2_frac n i) (b3Rest2_frac n (i + 1))
      source' := by simp [b3Rest2_restr_apply, b3Rest2_affI]
      target' := by simp [b3Rest2_restr_apply, b3Rest2_affI] }
  have heq (i : ℕ) (hi : i < n) :
      b6m_pathChain (piece g i).toContinuousMap - b6m_pathChain (piece h i).toContinuousMap =
        b6m_pathChain (p i).toContinuousMap - b6m_pathChain (p (i + 1)).toContinuousMap := by
    have hs := b6m_pathChain_square_in_chart (e i) (hU i) (hUt i)
      (piece g i) (piece h i) (p i) (p (i + 1)) (hg i hi) (hh i hi)
      (hp₀ i hi) (hp₁ i hi)
    apply sub_eq_zero.mp
    calc
      _ = (b6m_pathChain (piece g i).toContinuousMap + b6m_pathChain (p (i + 1)).toContinuousMap) -
          (b6m_pathChain (p i).toContinuousMap + b6m_pathChain (piece h i).toContinuousMap) := by abel
      _ = 0 := sub_eq_zero.mpr hs
  apply sub_eq_zero.mp
  rw [b6m_pathChain_eq_sum g hn, b6m_pathChain_eq_sum h hn, ← Finset.sum_sub_distrib]
  change (∑ i ∈ Finset.range n,
    (b6m_pathChain (piece g i).toContinuousMap - b6m_pathChain (piece h i).toContinuousMap)) = 0
  rw [Finset.sum_congr rfl (fun i hi ↦ heq i (Finset.mem_range.mp hi))]
  have ht := Finset.sum_range_sub (fun i ↦ b6m_pathChain (p i).toContinuousMap) n
  have he : (∑ i ∈ Finset.range n,
      (b6m_pathChain (p i).toContinuousMap - b6m_pathChain (p (i + 1)).toContinuousMap)) =
      -(∑ i ∈ Finset.range n,
        (b6m_pathChain (p (i + 1)).toContinuousMap - b6m_pathChain (p i).toContinuousMap)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    abel
  rw [he, ht, hp, sub_self, neg_zero]

set_option backward.isDefEq.respectTransparency false in
theorem b6m_integral_loopClass_eq_iff_pathChain {T : Type} [TopologicalSpace T]
    (p q : C(UnitAddCircle, T)) :
    ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass (loopCycle ℤ p) =
      ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass (loopCycle ℤ q) ↔
    b6m_pathChain (simplexPath (loopSimplex p)) =
      b6m_pathChain (simplexPath (loopSimplex q)) := by
  obtain ⟨j, hj, hJ⟩ := b6m_homology_chain_embedding T
  constructor
  · intro h
    have hh := congrArg j h
    rw [hJ, hJ] at hh
    simpa only [b6m_pathChain, b3Rest2_pathSimplex_simplexPath (T := T), loopCycle] using hh
  · intro h
    apply hj
    rw [hJ, hJ]
    simpa only [b6m_pathChain, b3Rest2_pathSimplex_simplexPath (T := T), loopCycle] using h

end HodgeLean.Foundations.Program

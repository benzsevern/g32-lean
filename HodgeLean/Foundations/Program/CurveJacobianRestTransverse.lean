import HodgeLean.Foundations.Program.CurveJacobianRestPoly
import HodgeLean.Foundations.Program.CurveJacobianACrossings
import HodgeLean.Foundations.Program.CurveJacobianFormsPeriods

/-! # Track B3, lane Rest: transverse polygonal representatives of loops

A **chart polygon** is a `C¹` loop made of `N` chart segments, the `k`-th one in the chart at
`x k`, from the vertex `w k` to the vertex `w (k + 1)`, inside a convex chart ball; the segments
are reparametrized by a smooth step, so they join with zero velocity.

* If the arcs `δ [k/N, (k+1)/N]` of a `C¹` loop `δ` lie in the same chart balls, and each vertex
  `w k` is joined to `δ (k/N)` by a chart segment inside the balls of both arcs `k - 1` and `k`,
  then every smooth closed real `1`-form has the same integral along the polygon and along `δ`
  (`b3Rest_Poly.lineIntegral_loop`): on each ball the integrals are differences of a primitive, and
  the differences telescope. In particular the polygon has the periods of `δ`.
* A polygon whose vertices avoid a `C¹` loop `γ`, and whose segments meet `γ` only where the chart
  derivative of `γ` is independent of the segment, is transverse to `γ`
  (`b3Rest_Poly.transverse`); the smooth step has positive derivative on `(0, 1)`, so the polygon
  moves at every point that is not a vertex.
* Such vertices exist (`b3Rest_exists_generic`): by Sard's theorem in the plane (Mathlib's
  `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`), the points of `γ` in a chart and the bad
  endpoints `v` of segments from a fixed `c` (images of the critical set of
  `(s, μ) ↦ c + μ⁻¹ (φ (γ s) - c)`) are null sets.
* Refining a cover of `δ` by chart balls (two segments per arc, the middle vertex generic for both)
  gives **a `C¹` loop transverse to `γ` with the periods of `δ`** (`b3Rest_exists_transverse`).
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Manifold Filter Topology Set Metric
open scoped ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- **A chart polygon**: `N` chart segments, the `k`-th in the ball of radius `r k` of the chart at
`x k`, from `w k` to `w (k + 1)`; all data are `N`-periodic in `k`. -/
structure b3Rest_Poly (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (C : Type)
    [TopologicalSpace C] [ChartedSpace E C] where
  N : ℕ
  pos : 0 < N
  x : ℤ → C
  r : ℤ → ℝ
  w : ℤ → C
  x_add : ∀ k, x (k + N) = x k
  w_add : ∀ k, w (k + N) = w k
  ball_sub : ∀ k, ball (chartAt E (x k) (x k)) (r k) ⊆ (chartAt E (x k)).target
  mem_w : ∀ k, w k ∈ (chartAt E (x k)).source ∧
    chartAt E (x k) (w k) ∈ ball (chartAt E (x k) (x k)) (r k)
  mem_w' : ∀ k, w (k + 1) ∈ (chartAt E (x k)).source ∧
    chartAt E (x k) (w (k + 1)) ∈ ball (chartAt E (x k) (x k)) (r k)

namespace b3Rest_Poly

variable (K : b3Rest_Poly E C)

/-- The initial vertex of the `k`-th segment in its chart. -/
def A (k : ℤ) : E := chartAt E (K.x k) (K.w k)

/-- The final vertex of the `k`-th segment in its chart. -/
def B (k : ℤ) : E := chartAt E (K.x k) (K.w (k + 1))

/-- The `k`-th segment. -/
def seg (k : ℤ) (τ : ℝ) : C :=
  (chartAt E (K.x k)).symm (K.A k + Real.smoothTransition (3 * τ - 1) • (K.B k - K.A k))

theorem segPt_mem (k : ℤ) (τ : ℝ) :
    K.A k + Real.smoothTransition (3 * τ - 1) • (K.B k - K.A k) ∈
      ball (chartAt E (K.x k) (K.x k)) (K.r k) :=
  Convex.add_smul_sub_mem (convex_ball _ _) (K.mem_w k).2 (K.mem_w' k).2
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem seg_mem (k : ℤ) (τ : ℝ) : K.seg k τ ∈ (chartAt E (K.x k)).source ∧
    chartAt E (K.x k) (K.seg k τ) ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k) := by
  have h := K.ball_sub k (K.segPt_mem k τ)
  refine ⟨(chartAt E (K.x k)).map_target h, ?_⟩
  rw [seg, (chartAt E (K.x k)).right_inv h]
  exact K.segPt_mem k τ

theorem seg_isGoodPath (k : ℤ) : b3A_IsGoodPath (E := E) (K.seg k) (K.w k) (K.w (k + 1)) := by
  have h := b3A_isGoodPath_segment (K.x k) (K.A k) (K.B k)
    (((convex_ball _ _).segment_subset (K.mem_w k).2 (K.mem_w' k).2).trans (K.ball_sub k))
  rw [show (chartAt E (K.x k)).symm (K.A k) = K.w k from
      (chartAt E (K.x k)).left_inv (K.mem_w k).1,
    show (chartAt E (K.x k)).symm (K.B k) = K.w (k + 1) from
      (chartAt E (K.x k)).left_inv (K.mem_w' k).1] at h
  exact h

theorem seg_zero (k : ℤ) : K.seg k 0 = K.w k := (K.seg_isGoodPath k).apply_zero

theorem seg_add (k : ℤ) : K.seg (k + K.N) = K.seg k := by
  funext τ
  have h1 : K.w (k + K.N + 1) = K.w (k + 1) := by
    rw [show k + K.N + 1 = (k + 1) + K.N by ring, K.w_add]
  simp only [seg, A, B, K.x_add, K.w_add, h1]

/-- **The polygon** `t ↦ seg ⌊N t⌋ (fract (N t))`. -/
def loop (t : ℝ) : C := K.seg ⌊(K.N : ℝ) * t⌋ (Int.fract ((K.N : ℝ) * t))

theorem loop_periodic : Function.Periodic K.loop 1 := by
  intro t
  simp only [loop, mul_add, mul_one]
  rw [Int.floor_add_natCast, Int.fract_add_natCast, K.seg_add]

theorem loop_contMDiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 K.loop := by
  have h := b3Rest_floorPath_contMDiff K.seg K.w K.seg_isGoodPath
  exact h.comp ((contDiff_const.mul contDiff_id).contMDiff)

/-- The polygon as a `C¹` loop. -/
def smoothLoop : b3_SmoothLoop E C := ⟨K.loop, K.loop_periodic, K.loop_contMDiff⟩

theorem loop_mem (k : ℤ) {t : ℝ} (ht : t ∈ Icc ((k : ℝ) / K.N) ((k + 1) / K.N)) :
    K.loop t ∈ (chartAt E (K.x k)).source ∧
      chartAt E (K.x k) (K.loop t) ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k) := by
  have hN : (0 : ℝ) < K.N := Nat.cast_pos.2 K.pos
  have h1 : (k : ℝ) ≤ K.N * t := by
    have := ht.1; rw [div_le_iff₀ hN] at this; linarith
  have h2 : (K.N : ℝ) * t ≤ k + 1 := by
    have := ht.2; rw [le_div_iff₀ hN] at this; linarith
  rcases h2.lt_or_eq with hlt | heq
  · have hfl : ⌊(K.N : ℝ) * t⌋ = k := by rw [Int.floor_eq_iff]; exact ⟨h1, hlt⟩
    simp only [loop, hfl]
    exact K.seg_mem k _
  · have hfl : ⌊(K.N : ℝ) * t⌋ = k + 1 := by
      rw [heq]; exact_mod_cast Int.floor_intCast (k + 1)
    have hfr : Int.fract ((K.N : ℝ) * t) = 0 := by
      rw [heq]; exact_mod_cast Int.fract_intCast (k + 1)
    simp only [loop, hfl, hfr, seg_zero]
    exact K.mem_w' k

theorem loop_at (k : ℤ) : K.loop ((k : ℝ) / K.N) = K.w k := by
  have hN : (K.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 K.pos.ne'
  have : (K.N : ℝ) * (k / K.N) = k := by field_simp
  simp only [loop, this, Int.floor_intCast, Int.fract_intCast, seg_zero]

end b3Rest_Poly

/-! ## Periods of a polygon following a loop -/

section Follows

attribute [local instance] b3Forms_isManifold_real

namespace b3Rest_Poly

variable (K : b3Rest_Poly E C)

/-- **The polygon follows `P`**: the arcs `P [k/N, (k+1)/N]` lie in the chart balls of the
segments, and the chart segment from `P (k/N)` to the vertex `w k` lies in the balls of the
segments `k - 1` and `k`. -/
structure Follows (P : ℝ → C) : Prop where
  arc : ∀ k : ℤ, ∀ τ ∈ Icc (0 : ℝ) 1, P ((k + τ) / K.N) ∈ (chartAt E (K.x k)).source ∧
    chartAt E (K.x k) (P ((k + τ) / K.N)) ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k)
  conn : ∀ k : ℤ, ∀ τ ∈ Icc (0 : ℝ) 1,
    (chartAt E (K.x k)).symm (chartAt E (K.x k) (P (k / K.N)) +
        τ • (K.A k - chartAt E (K.x k) (P (k / K.N)))) ∈ (chartAt E (K.x (k - 1))).source ∧
      chartAt E (K.x (k - 1)) ((chartAt E (K.x k)).symm (chartAt E (K.x k) (P (k / K.N)) +
        τ • (K.A k - chartAt E (K.x k) (P (k / K.N))))) ∈
        ball (chartAt E (K.x (k - 1)) (K.x (k - 1))) (K.r (k - 1))

variable {K} {P : ℝ → C}

theorem Follows.u_mem (hF : K.Follows P) (k : ℤ) : P (k / K.N) ∈ (chartAt E (K.x k)).source ∧
    chartAt E (K.x k) (P (k / K.N)) ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k) := by
  have := hF.arc k 0 ⟨le_rfl, zero_le_one⟩
  rw [add_zero] at this
  exact this

theorem Follows.u_mem' (hF : K.Follows P) (k : ℤ) :
    P ((k + 1) / K.N) ∈ (chartAt E (K.x k)).source ∧
      chartAt E (K.x k) (P ((k + 1) / K.N)) ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k) :=
  hF.arc k 1 ⟨zero_le_one, le_rfl⟩

/-- The connecting segment from `P (k / N)` to `w k`. -/
def conn (K : b3Rest_Poly E C) (P : ℝ → C) (k : ℤ) : ℝ → C :=
  b3Forms_segPath (K.x k) (chartAt E (K.x k) (P (k / K.N))) (K.A k)

theorem conn_add (hper : Function.Periodic P 1) (k : ℤ) : conn K P (k + K.N) = conn K P k := by
  have hN : (K.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 K.pos.ne'
  have hP : P (((k + K.N : ℤ) : ℝ) / K.N) = P (k / K.N) := by
    have : (((k + K.N : ℤ) : ℝ)) / K.N = k / K.N + 1 := by push_cast; field_simp
    rw [this, hper]
  simp only [conn, A, K.x_add, K.w_add, hP]

/-- **A polygon following `P` has the integrals of `P`** for every smooth closed real `1`-form. -/
theorem lineIntegral_loop (hF : K.Follows P) (hP : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 P)
    (hper : Function.Periodic P 1) {α : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (hdα : b3Forms_d α = 0) :
    b3Forms_lineIntegral α K.loop 0 1 = b3Forms_lineIntegral α P 0 1 := by
  have hN : (0 : ℝ) < K.N := Nat.cast_pos.2 K.pos
  choose h hh using fun k ↦ b3Forms_exists_local_primitive hα hdα (K.x k) (convex_ball _ _)
    isOpen_ball (K.ball_sub k)
  let D : ℤ → ℝ := fun k ↦ b3Forms_lineIntegral α (conn K P k) 0 1
  have hD1 : ∀ k, D k = h k (K.A k) - h k (chartAt E (K.x k) (P (k / K.N))) := fun k ↦
    b3Forms_lineIntegral_segPath hα (K.x k) (convex_ball _ _) (K.ball_sub k) (hh k)
      (hF.u_mem k).2 (K.mem_w k).2
  have hD2 : ∀ k : ℤ, D (k + 1) = h k (K.B k) - h k (chartAt E (K.x k) (P ((k + 1) / K.N))) := by
    intro k
    have hc := (b3Forms_segPath_isTame (K.x (k + 1)) (convex_ball _ _) (K.ball_sub (k + 1))
      (hF.u_mem (k + 1)).2 (K.mem_w (k + 1)).2).1
    have hmem : ∀ t ∈ uIcc (0 : ℝ) 1, conn K P (k + 1) t ∈ (chartAt E (K.x k)).source ∧
        chartAt E (K.x k) (conn K P (k + 1) t) ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k) := by
      intro t _
      have := hF.conn (k + 1) (Real.smoothTransition (3 * t - 1))
        ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
      rw [add_sub_cancel_right] at this
      exact this
    have e := b3Forms_lineIntegral_eq_of_primitive hα (hh k) hc hmem
    have e1 : b3Forms_segPath (K.x (k + 1)) (chartAt E (K.x (k + 1)) (P (((k + 1 : ℤ) : ℝ) / K.N)))
        (chartAt E (K.x (k + 1)) (K.w (k + 1))) 1 = K.w (k + 1) := by
      rw [b3Forms_segPath_one]
      exact (chartAt E (K.x (k + 1))).left_inv (K.mem_w (k + 1)).1
    have e0 : b3Forms_segPath (K.x (k + 1)) (chartAt E (K.x (k + 1)) (P (((k + 1 : ℤ) : ℝ) / K.N)))
        (chartAt E (K.x (k + 1)) (K.w (k + 1))) 0 = P ((k + 1) / K.N) := by
      rw [b3Forms_segPath_zero]
      have := (chartAt E (K.x (k + 1))).left_inv (hF.u_mem (k + 1)).1
      push_cast at this ⊢
      exact this
    rw [e1, e0] at e
    exact e
  have hLi : ∀ k : ℤ, b3Forms_lineIntegral α K.loop ((k : ℝ) / K.N) ((k + 1) / K.N) =
      h k (K.B k) - h k (K.A k) := by
    intro k
    have hle : (k : ℝ) / K.N ≤ (k + 1) / K.N := by gcongr; linarith
    have e := b3Forms_lineIntegral_eq_of_primitive hα (hh k) K.loop_contMDiff
      (fun t ht ↦ K.loop_mem k (by rwa [uIcc_of_le hle] at ht))
    rw [e, K.loop_at k]
    have := K.loop_at (k + 1)
    push_cast at this
    rw [this]
    rfl
  have hPi : ∀ k : ℤ, b3Forms_lineIntegral α P ((k : ℝ) / K.N) ((k + 1) / K.N) =
      h k (chartAt E (K.x k) (P ((k + 1) / K.N))) - h k (chartAt E (K.x k) (P (k / K.N))) := by
    intro k
    have hle : (k : ℝ) / K.N ≤ (k + 1) / K.N := by gcongr; linarith
    refine b3Forms_lineIntegral_eq_of_primitive hα (hh k) hP fun t ht ↦ ?_
    rw [uIcc_of_le hle] at ht
    have hτ : (K.N : ℝ) * t - k ∈ Icc (0 : ℝ) 1 := by
      constructor
      · have := ht.1; rw [div_le_iff₀ hN] at this; linarith
      · have := ht.2; rw [le_div_iff₀ hN] at this; linarith
    have := hF.arc k _ hτ
    rwa [show ((k : ℝ) + (K.N * t - k)) / K.N = t by field_simp; ring] at this
  have hdiff : ∀ k : ℤ, b3Forms_lineIntegral α K.loop ((k : ℝ) / K.N) ((k + 1) / K.N) -
      b3Forms_lineIntegral α P ((k : ℝ) / K.N) ((k + 1) / K.N) = D (k + 1) - D k := by
    intro k
    rw [hLi, hPi, hD2, hD1]
    ring
  -- sum over the `N` arcs
  have hsum : ∀ γ : ℝ → C, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ →
      ∑ i ∈ Finset.range K.N, b3Forms_lineIntegral α γ ((i : ℝ) / K.N) ((i + 1) / K.N) =
        b3Forms_lineIntegral α γ 0 1 := by
    intro γ hγ
    have := intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ ↦ (i : ℝ) / K.N)
      (n := K.N) (f := fun t ↦ α (γ t) (fun _ ↦ b3Forms_velocity γ t)) (μ := MeasureTheory.volume)
      (fun i _ ↦ b3Forms_intervalIntegrable_lineIntegrand hα hγ _ _)
    simp only [Nat.cast_zero, zero_div, div_self hN.ne', Nat.cast_add, Nat.cast_one] at this
    exact this
  have hDN : D K.N = D 0 := by
    have := conn_add hper (K := K) 0
    simp only [zero_add] at this
    show b3Forms_lineIntegral α (conn K P K.N) 0 1 = b3Forms_lineIntegral α (conn K P 0) 0 1
    rw [this]
  have key : ∑ i ∈ Finset.range K.N, (b3Forms_lineIntegral α K.loop ((i : ℝ) / K.N) ((i + 1) / K.N) -
      b3Forms_lineIntegral α P ((i : ℝ) / K.N) ((i + 1) / K.N)) = 0 := by
    have : ∀ i : ℕ, b3Forms_lineIntegral α K.loop ((i : ℝ) / K.N) ((i + 1) / K.N) -
        b3Forms_lineIntegral α P ((i : ℝ) / K.N) ((i + 1) / K.N) =
          D ((i + 1 : ℕ) : ℤ) - D (i : ℤ) := by
      intro i
      have := hdiff (i : ℤ)
      push_cast at this ⊢
      exact this
    simp only [this]
    rw [Finset.sum_range_sub (fun i : ℕ ↦ D (i : ℤ))]
    simp only [Nat.cast_zero]
    rw [hDN, sub_self]
  rw [Finset.sum_sub_distrib, hsum _ K.loop_contMDiff, hsum _ hP, sub_eq_zero] at key
  exact key

end b3Rest_Poly

end Follows

/-! ## Transversality of a polygon -/

section Transverse

theorem b3Rest_expNegInvGlue_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt expNegInvGlue (Real.exp (-x⁻¹) * (x ^ 2)⁻¹) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ Real.exp (-y⁻¹)) (Real.exp (-x⁻¹) * (x ^ 2)⁻¹) x := by
    have := ((hasDerivAt_inv hx.ne').neg).exp
    simpa [neg_neg] using this
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp [expNegInvGlue, not_le.2 (show (0 : ℝ) < y from hy)]

/-- **The smooth step has positive derivative on `(0, 1)`.** -/
theorem b3Rest_smoothTransition_hasDerivAt_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∃ d > 0, HasDerivAt Real.smoothTransition d x := by
  obtain ⟨h0, h1⟩ := hx
  have h1' : 0 < 1 - x := by linarith
  set g := expNegInvGlue x
  set k := expNegInvGlue (1 - x)
  set g' := Real.exp (-x⁻¹) * (x ^ 2)⁻¹
  set k' := Real.exp (-(1 - x)⁻¹) * ((1 - x) ^ 2)⁻¹
  have hg := b3Rest_expNegInvGlue_hasDerivAt h0
  have hk : HasDerivAt (fun y ↦ expNegInvGlue (1 - y)) (-k') x := by
    have := (b3Rest_expNegInvGlue_hasDerivAt h1').comp x ((hasDerivAt_id x).const_sub 1)
    convert this using 1
    · rfl
    · simp only [k']; ring
  have hden : g + k ≠ 0 := (Real.smoothTransition.pos_denom x).ne'
  have hd := hg.div (hg.add hk) hden
  have hgp : 0 < g := expNegInvGlue.pos_of_pos h0
  have hkp : 0 < k := expNegInvGlue.pos_of_pos h1'
  have hg'p : 0 < g' := by positivity
  have hk'p : 0 < k' := by positivity
  refine ⟨(g' * (g + k) - g * (g' + -k')) / (g + k) ^ 2, ?_, ?_⟩
  · have : g' * (g + k) - g * (g' + -k') = g' * k + g * k' := by ring
    rw [this]
    positivity
  · convert hd using 1
    funext y
    rfl

variable [FiniteDimensional ℂ E]

/-- On a complex line, a vanishing orientation means `ℝ`-dependence. -/
theorem b3Rest_dep_of_orient_eq_zero (hE : Module.finrank ℂ E = 1) (v w : E)
    (h : b3_orient E v w = 0) : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a • v + b • w = 0 := by
  set e := Module.finBasis ℂ E
  have i₀ : Fin (Module.finrank ℂ E) := ⟨0, by omega⟩
  have hall : ∀ i : Fin (Module.finrank ℂ E), i = i₀ := fun i ↦ Fin.ext (by omega)
  have hv : v = e.equivFun v i₀ • e i₀ := by
    conv_lhs => rw [← e.sum_equivFun v]
    rw [Finset.sum_eq_single i₀ (fun i _ hi ↦ absurd (hall i) hi) (by simp)]
  have hw : w = e.equivFun w i₀ • e i₀ := by
    conv_lhs => rw [← e.sum_equivFun w]
    rw [Finset.sum_eq_single i₀ (fun i _ hi ↦ absurd (hall i) hi) (by simp)]
  have ho : (starRingEnd ℂ (e.equivFun v i₀) * e.equivFun w i₀).im = 0 := by
    have := h
    simp only [b3_orient] at this
    rwa [Finset.sum_eq_single i₀ (fun i _ hi ↦ absurd (hall i) hi) (by simp)] at this
  set a := e.equivFun v i₀
  set c := e.equivFun w i₀
  by_cases ha : a = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    rw [hv, ha]; simp
  · -- `c / a` is real
    have hr : (c / a).im = 0 := by
      have hna : (Complex.normSq a : ℝ) ≠ 0 := by
        rw [Ne, Complex.normSq_eq_zero]; exact ha
      have hconj : starRingEnd ℂ a ≠ 0 := (map_ne_zero _).2 ha
      have : c / a = (starRingEnd ℂ a * c) / (Complex.normSq a : ℂ) := by
        rw [Complex.normSq_eq_conj_mul_self, mul_div_mul_left c a hconj]
      rw [this, Complex.div_ofReal_im, ho, zero_div]
    refine ⟨(c / a).re, -1, Or.inr (by norm_num), ?_⟩
    have hca : ((c / a).re : ℂ) = c / a := Complex.ext (by simp) (by simp [hr])
    rw [neg_one_smul, ← Complex.coe_smul, hca, hv, hw, smul_smul, div_mul_cancel₀ c ha,
      add_neg_cancel]

/-- **Transversality read in one chart**: at a crossing `γ s = δ t` in the chart at `x₀`, if the
chart derivatives of `γ` and `δ` are `ℝ`-independent then the orientation of the velocities is
nonzero. -/
theorem b3Rest_orient_ne_zero_of_chart (hE : Module.finrank ℂ E = 1) (γ δ : ℝ → C) (s t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ s) (hδ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 δ t)
    (hst : γ s = δ t) (x₀ : C) (hs : γ s ∈ (chartAt E x₀).source)
    (hind : ∀ a b : ℝ, a • fderiv ℝ (chartAt E x₀ ∘ γ) s 1 + b • fderiv ℝ (chartAt E x₀ ∘ δ) t 1 = 0 →
      a = 0 ∧ b = 0) :
    b3_orient E (b3_velocity E C γ s) (b3_velocity E C δ t) ≠ 0 := by
  intro h0
  obtain ⟨a, b, hab, hlin⟩ := b3Rest_dep_of_orient_eq_zero hE _ _ h0
  have h1 := (b3A_chart_comp γ s hγ x₀ hs).2
  have h2 := (b3A_chart_comp δ t hδ x₀ (hst ▸ hs)).2
  rw [← hst] at h2
  set T := fderiv ℂ (chartAt E x₀ ∘ (chartAt E (γ s)).symm) (chartAt E (γ s) (γ s))
  have := hind a b (by
    rw [h1, h2]
    have := congrArg (fun v ↦ T v) hlin
    simp only [map_add, map_zero] at this
    rw [← this]
    congr 1
    · exact (T.map_smul_of_tower a _).symm
    · exact (T.map_smul_of_tower b _).symm)
  rcases hab with ha | hb
  · exact ha this.1
  · exact hb this.2

/-- **A polygon is transverse to `γ`** if its vertices avoid `γ` and at every crossing of `γ`
with the interior of a segment, the chart derivative of `γ` is independent of the segment. -/
theorem b3Rest_Poly.transverse (hE : Module.finrank ℂ E = 1) (K : b3Rest_Poly E C)
    (γ : b3_SmoothLoop E C) (hV : ∀ k s, γ.1 s ≠ K.w k)
    (hS : ∀ (k : ℤ) (s l : ℝ), l ∈ Ioo (0 : ℝ) 1 → γ.1 s ∈ (chartAt E (K.x k)).source →
      chartAt E (K.x k) (γ.1 s) = K.A k + l • (K.B k - K.A k) →
      ∀ a b : ℝ, a • fderiv ℝ (chartAt E (K.x k) ∘ γ.1) s 1 + b • (K.B k - K.A k) = 0 →
        a = 0 ∧ b = 0) :
    b3_Transverse E γ K.smoothLoop := by
  intro s t hst
  have hN : (0 : ℝ) < K.N := Nat.cast_pos.2 K.pos
  set k := ⌊(K.N : ℝ) * t⌋
  set τ := Int.fract ((K.N : ℝ) * t)
  set σ := Real.smoothTransition (3 * τ - 1)
  have hloop : K.smoothLoop.1 t = K.seg k τ := rfl
  have hpt := K.segPt_mem k τ
  have hseg : chartAt E (K.x k) (K.seg k τ) = K.A k + σ • (K.B k - K.A k) :=
    (chartAt E (K.x k)).right_inv (K.ball_sub k hpt)
  -- the crossing is not a vertex
  have hσ0 : σ ≠ 0 := by
    intro h0
    apply hV k s
    have h0' : Real.smoothTransition (3 * τ - 1) = 0 := h0
    rw [hst, hloop, seg, h0', zero_smul, add_zero]
    exact (chartAt E (K.x k)).left_inv (K.mem_w k).1
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hV (k + 1) s
    have h1' : Real.smoothTransition (3 * τ - 1) = 1 := h1
    rw [hst, hloop, seg, h1', one_smul, add_sub_cancel]
    exact (chartAt E (K.x k)).left_inv (K.mem_w' k).1
  have hy0 : 0 < 3 * τ - 1 := by
    by_contra h; exact hσ0 (Real.smoothTransition.zero_of_nonpos (not_lt.1 h))
  have hy1 : 3 * τ - 1 < 1 := by
    by_contra h; exact hσ1 (Real.smoothTransition.one_of_one_le (not_lt.1 h))
  obtain ⟨d, hd0, hd⟩ := b3Rest_smoothTransition_hasDerivAt_pos ⟨hy0, hy1⟩
  -- near `t` the polygon is the `k`-th segment
  have hlt : (k : ℝ) < K.N * t := by
    have : 0 < τ := by linarith
    have := Int.floor_add_fract ((K.N : ℝ) * t)
    linarith
  have hlt' : (K.N : ℝ) * t < k + 1 := Int.lt_floor_add_one _
  let g : ℝ → E := fun t' ↦ K.A k + Real.smoothTransition (3 * ((K.N : ℝ) * t' - k) - 1) •
    (K.B k - K.A k)
  have hev : chartAt E (K.x k) ∘ K.smoothLoop.1 =ᶠ[𝓝 t] g := by
    have hU : {t' : ℝ | (k : ℝ) < K.N * t' ∧ (K.N : ℝ) * t' < k + 1} ∈ 𝓝 t :=
      ((isOpen_lt continuous_const (continuous_const.mul continuous_id)).inter
        (isOpen_lt (continuous_const.mul continuous_id) continuous_const)).mem_nhds ⟨hlt, hlt'⟩
    filter_upwards [hU] with t' ht'
    have hfl : ⌊(K.N : ℝ) * t'⌋ = k := by rw [Int.floor_eq_iff]; exact ⟨ht'.1.le, ht'.2⟩
    show chartAt E (K.x k) (K.loop t') = g t'
    simp only [b3Rest_Poly.loop, hfl, Int.fract, g]
    exact (chartAt E (K.x k)).right_inv (K.ball_sub k (K.segPt_mem k _))
  have hgd : HasDerivAt g ((d * (3 * K.N)) • (K.B k - K.A k)) t := by
    have h1 : HasDerivAt (fun t' : ℝ ↦ 3 * ((K.N : ℝ) * t' - k) - 1) (3 * K.N) t := by
      have := ((hasDerivAt_id t).const_mul ((3 : ℝ) * K.N)).sub_const ((3 : ℝ) * k + 1)
      convert this using 1
      · funext t'; simp only [id]; ring
      · ring
    have h2 : HasDerivAt (fun t' : ℝ ↦ Real.smoothTransition (3 * ((K.N : ℝ) * t' - k) - 1))
        (d * (3 * K.N)) t := by
      have e : 3 * ((K.N : ℝ) * t - k) - 1 = 3 * τ - 1 := rfl
      rw [← e] at hd
      exact hd.comp t h1
    exact (h2.smul_const (K.B k - K.A k)).const_add _
  have hfd : fderiv ℝ (chartAt E (K.x k) ∘ K.smoothLoop.1) t 1 =
      (d * (3 * K.N)) • (K.B k - K.A k) := by
    rw [hev.fderiv_eq, hgd.hasFDerivAt.fderiv]
    simp
  have hs : γ.1 s ∈ (chartAt E (K.x k)).source := by
    rw [hst, hloop]; exact (K.seg_mem k τ).1
  refine b3Rest_orient_ne_zero_of_chart hE γ.1 K.smoothLoop.1 s t (γ.2.2 s)
    (K.loop_contMDiff t) hst (K.x k) hs fun a b hab ↦ ?_
  rw [hfd, smul_smul] at hab
  have hcross : chartAt E (K.x k) (γ.1 s) = K.A k + σ • (K.B k - K.A k) := by
    rw [hst, hloop, hseg]
  obtain ⟨ha, hb⟩ := hS k s σ ⟨lt_of_le_of_ne (Real.smoothTransition.nonneg _) (Ne.symm hσ0),
    lt_of_le_of_ne (Real.smoothTransition.le_one _) hσ1⟩ hs hcross a _ hab
  refine ⟨ha, ?_⟩
  have : d * (3 * K.N) ≠ 0 := by positivity
  rcases mul_eq_zero.1 hb with h | h
  · exact h
  · exact absurd h this

end Transverse

/-! ## Generic vertices -/

section Generic

open MeasureTheory

/-- **Sard's theorem in the plane, in the form used here**: a map `ℝ² → E` (`E` of real dimension
two) whose derivative has a kernel at every point of `D` maps `D` to a null set. From Mathlib's
`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`. -/
theorem b3Rest_addHaar_image_null {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F)
    [μ.IsAddHaarMeasure] (hF2 : Module.finrank ℝ F = 2) (D : Set (ℝ × ℝ)) (G : ℝ × ℝ → F)
    (hG : ∀ p ∈ D, ∃ G' : ℝ × ℝ →L[ℝ] F, HasFDerivWithinAt G G' D p ∧ ∃ q ≠ 0, G' q = 0) :
    μ (G '' D) = 0 := by
  choose! G' hG' hker using hG
  have hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ F := by
    rw [Module.finrank_prod, Module.finrank_self, hF2]
  let L : (ℝ × ℝ) ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq hdim
  have himg : (G ∘ L.symm) '' (L '' D) = G '' D := by
    rw [image_image]
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [← himg]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (f' := fun e ↦ (G' (L.symm e)).comp (L.symm : F →L[ℝ] ℝ × ℝ)) ?_ ?_
  · rintro e ⟨p, hp, rfl⟩
    have h1 := hG' p hp
    rw [← L.symm_apply_apply p] at h1
    refine h1.comp (L p) L.symm.hasFDerivAt.hasFDerivWithinAt ?_
    rintro e' ⟨p', hp', rfl⟩
    simpa using hp'
  · rintro e ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hq0⟩ := hker p hp
    show LinearMap.det _ = 0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
    refine ⟨L q, ?_, by simpa using hq⟩
    simp [hq0]

variable [FiniteDimensional ℂ E]

/-- The points of `γ` in the chart at `x`, in coordinates. -/
def b3Rest_img (γ : ℝ → C) (x : C) : Set E :=
  {v | ∃ s, γ s ∈ (chartAt E x).source ∧ chartAt E x (γ s) = v}

/-- **The bad endpoints** for chart segments from `c` in the chart at `x`: the `v` such that the
segment from `c` to `v` meets `γ` (away from `c`) with the chart derivative of `γ` dependent on
the segment. -/
def b3Rest_bad (γ : ℝ → C) (x : C) (c : E) : Set E :=
  {v | ∃ s μ, γ s ∈ (chartAt E x).source ∧ μ ∈ Ioc (0 : ℝ) 1 ∧
    chartAt E x (γ s) = c + μ • (v - c) ∧
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a • fderiv ℝ (chartAt E x ∘ γ) s 1 + b • (v - c) = 0}

theorem b3Rest_hasFDerivAt_chart_comp {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (x : C)
    {s : ℝ} (hs : γ s ∈ (chartAt E x).source) :
    HasFDerivAt (chartAt E x ∘ γ) (fderiv ℝ (chartAt E x ∘ γ) s) s :=
  (((b3A_chart_comp γ s (hγ s) x hs).1).differentiableAt one_ne_zero).hasFDerivAt

theorem b3Rest_img_null [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hE : Module.finrank ℂ E = 1) {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (x : C) :
    μ (b3Rest_img γ x) = 0 := by
  have hE2 : Module.finrank ℝ E = 2 := by rw [finrank_real_of_complex, hE]
  refine measure_mono_null ?_ (b3Rest_addHaar_image_null μ hE2
    {p : ℝ × ℝ | γ p.1 ∈ (chartAt E x).source} (fun p ↦ chartAt E x (γ p.1)) ?_)
  · rintro v ⟨s, hs, rfl⟩
    exact ⟨(s, 0), hs, rfl⟩
  · intro p hp
    refine ⟨(fderiv ℝ (chartAt E x ∘ γ) p.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ), ?_,
      (0, 1), by simp, by simp⟩
    exact ((b3Rest_hasFDerivAt_chart_comp hγ x hp).comp p hasFDerivAt_fst).hasFDerivWithinAt

theorem b3Rest_bad_null [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hE : Module.finrank ℂ E = 1) {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (x : C)
    (c : E) : μ (b3Rest_bad γ x c) = 0 := by
  have hE2 : Module.finrank ℝ E = 2 := by rw [finrank_real_of_complex, hE]
  let D : Set (ℝ × ℝ) := {p | γ p.1 ∈ (chartAt E x).source ∧ 0 < p.2 ∧
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
      a • fderiv ℝ (chartAt E x ∘ γ) p.1 1 + b • (chartAt E x (γ p.1) - c) = 0}
  refine measure_mono_null ?_ (b3Rest_addHaar_image_null μ hE2 D
    (fun p ↦ c + p.2⁻¹ • (chartAt E x (γ p.1) - c)) ?_)
  · rintro v ⟨s, m, hs, hm, heq, a, b, hab, hlin⟩
    have hm0 : m ≠ 0 := hm.1.ne'
    refine ⟨(s, m), ⟨hs, hm.1, a, b * m⁻¹, ?_, ?_⟩, ?_⟩
    · rcases hab with ha | hb
      · exact Or.inl ha
      · exact Or.inr (mul_ne_zero hb (inv_ne_zero hm0))
    · simp only
      rw [heq, add_sub_cancel_left, smul_smul, mul_assoc, inv_mul_cancel₀ hm0, mul_one]
      exact hlin
    · simp only
      rw [heq, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hm0, one_smul, add_sub_cancel]
  · rintro ⟨s, m⟩ ⟨hs, hm, a, b, hab, hlin⟩
    have hm0 : m ≠ 0 := hm.ne'
    have h1 : HasFDerivAt (fun p : ℝ × ℝ ↦ p.2⁻¹) ((-(m ^ 2)⁻¹) • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (s, m) :=
      (hasDerivAt_inv hm0).comp_hasFDerivAt (s, m) hasFDerivAt_snd
    have h2 : HasFDerivAt (fun p : ℝ × ℝ ↦ chartAt E x (γ p.1) - c)
        ((fderiv ℝ (chartAt E x ∘ γ) s).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) (s, m) :=
      ((b3Rest_hasFDerivAt_chart_comp hγ x hs).comp (s, m) hasFDerivAt_fst).sub_const c
    refine ⟨_, ((h1.smul h2).const_add c).hasFDerivWithinAt, (a * m, -b * m ^ 2), ?_, ?_⟩
    · intro h0
      simp only [Prod.mk_eq_zero, mul_eq_zero, neg_eq_zero, pow_eq_zero_iff, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true] at h0
      rcases hab with ha | hb
      · exact ha (h0.1.resolve_right hm0)
      · exact hb (h0.2.resolve_right hm0)
    · simp only [_root_.add_apply, _root_.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd', smul_eq_mul]
      have e1 : fderiv ℝ (chartAt E x ∘ γ) s (a * m) = (a * m) • fderiv ℝ (chartAt E x ∘ γ) s 1 := by
        rw [← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
      rw [e1, smul_smul]
      have e2 : m⁻¹ * (a * m) = a := by field_simp
      have e3 : -(m ^ 2)⁻¹ * (-b * m ^ 2) = b := by field_simp
      rw [e2, e3]
      exact hlin

/-- **Generic points exist**: every nonempty open set of chart coordinates contains a point off `γ`
that is not a bad endpoint for segments from `c₁` or from `c₂`. -/
theorem b3Rest_exists_generic (hE : Module.finrank ℂ E = 1) {γ : ℝ → C}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (x : C) (c₁ c₂ : E) {U : Set E} (hU : IsOpen U)
    (hne : U.Nonempty) :
    ∃ v ∈ U, v ∉ b3Rest_img γ x ∧ v ∉ b3Rest_bad γ x c₁ ∧ v ∉ b3Rest_bad γ x c₂ := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := Measure.addHaar
  by_contra hcon
  push Not at hcon
  have hsub : U ⊆ b3Rest_img γ x ∪ b3Rest_bad γ x c₁ ∪ b3Rest_bad γ x c₂ := by
    intro v hv
    by_cases h1 : v ∈ b3Rest_img γ x
    · exact Or.inl (Or.inl h1)
    by_cases h2 : v ∈ b3Rest_bad γ x c₁
    · exact Or.inl (Or.inr h2)
    exact Or.inr (hcon v hv h1 h2)
  have h0 : μ (b3Rest_img γ x ∪ b3Rest_bad γ x c₁ ∪ b3Rest_bad γ x c₂) = 0 :=
    measure_union_null (measure_union_null (b3Rest_img_null μ hE hγ x)
      (b3Rest_bad_null μ hE hγ x c₁)) (b3Rest_bad_null μ hE hγ x c₂)
  exact (hU.measure_pos μ hne).ne' (measure_mono_null hsub h0)

end Generic

/-! ## Choosing the vertices -/

section Choice

/-- **`N`-periodic choices**: if a property of `(k, a)` is `N`-periodic in `k` and satisfiable for
each `k`, an `N`-periodic family satisfies it. -/
theorem b3Rest_exists_periodic_choice {α : Type*} (N : ℕ) (Q : ℤ → α → Prop)
    (hQ : ∀ k a, Q (k + N) a ↔ Q k a) (h : ∀ k, ∃ a, Q k a) :
    ∃ w : ℤ → α, (∀ k, w (k + N) = w k) ∧ ∀ k, Q k (w k) := by
  choose f hf using h
  have hper : ∀ (j : ℤ) (n : ℤ) a, Q (j + N * n) a ↔ Q j a := by
    intro j n a
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [show j + (N : ℤ) * (n + 1) = (j + N * n) + N by ring, hQ, ih]
    | pred n ih =>
      rw [← ih, show j + (N : ℤ) * (-n) = (j + N * (-n - 1)) + N by ring, hQ]
  refine ⟨fun k ↦ f (k % N), fun k ↦ by simp only [Int.add_emod_right], fun k ↦ ?_⟩
  have := hf (k % N)
  rw [← hper (k % N) (k / N), Int.emod_add_mul_ediv] at this
  exact this

variable [FiniteDimensional ℂ E] {P : ℝ → C}

/-- **A generic junction vertex** near `P (k/N)`: off `γ`, in the ball of the arc `k`, and joined to
`P (k/N)` by a chart segment inside the balls of the arcs `k - 1` and `k`. -/
theorem b3Rest_exists_junction (hE : Module.finrank ℂ E = 1) (K : b3Rest_Cover E P) {γ : ℝ → C}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (k : ℤ) :
    ∃ w : C, (w ∈ (chartAt E (K.x k)).source ∧
        chartAt E (K.x k) w ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k)) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1,
        (chartAt E (K.x k)).symm (chartAt E (K.x k) (P (k / K.N)) +
          τ • (chartAt E (K.x k) w - chartAt E (K.x k) (P (k / K.N)))) ∈
            (chartAt E (K.x (k - 1))).source ∧
        chartAt E (K.x (k - 1)) ((chartAt E (K.x k)).symm (chartAt E (K.x k) (P (k / K.N)) +
          τ • (chartAt E (K.x k) w - chartAt E (K.x k) (P (k / K.N))))) ∈
            ball (chartAt E (K.x (k - 1)) (K.x (k - 1))) (K.r (k - 1))) ∧
      ∀ s, γ s ≠ w := by
  set φ := chartAt E (K.x k)
  set ψ := chartAt E (K.x (k - 1))
  set c := φ (P (k / K.N))
  obtain ⟨hPs, hc⟩ := K.mem_zero k
  have hP' : P (k / K.N) ∈ ψ.source ∧ ψ (P (k / K.N)) ∈ ball (ψ (K.x (k - 1))) (K.r (k - 1)) := by
    have := K.mem (k - 1) 1 ⟨zero_le_one, le_rfl⟩
    rwa [show ((k - 1 : ℤ) : ℝ) + 1 = k by push_cast; ring] at this
  let W : Set E := ball (φ (K.x k)) (K.r k) ∩ (φ.target ∩
    φ.symm ⁻¹' {y | y ∈ ψ.source ∧ ψ y ∈ ball (ψ (K.x (k - 1))) (K.r (k - 1))})
  have hWo : IsOpen W := isOpen_ball.inter (φ.continuousOn_symm.isOpen_inter_preimage
    φ.open_target (ψ.continuousOn.isOpen_inter_preimage ψ.open_source isOpen_ball))
  have hcW : c ∈ W := by
    refine ⟨hc, K.ball_sub k hc, ?_⟩
    change φ.symm c ∈ {y | y ∈ ψ.source ∧ ψ y ∈ ball (ψ (K.x (k - 1))) (K.r (k - 1))}
    rw [show φ.symm c = P (k / K.N) from φ.left_inv hPs]
    exact hP'
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hWo c hcW
  obtain ⟨v, hv, hvimg, -, -⟩ := b3Rest_exists_generic hE hγ (K.x k) 0 0 isOpen_ball
    ⟨c, mem_ball_self hε⟩
  have hvW := hεW hv
  have hvt : v ∈ φ.target := hvW.2.1
  refine ⟨φ.symm v, ⟨φ.map_target hvt, by rw [φ.right_inv hvt]; exact hvW.1⟩, fun τ hτ ↦ ?_,
    fun s hs ↦ hvimg ⟨s, by rw [hs]; exact φ.map_target hvt, by rw [hs, φ.right_inv hvt]⟩⟩
  rw [φ.right_inv hvt]
  exact (hεW (Convex.add_smul_sub_mem (convex_ball c ε) (mem_ball_self hε) hv hτ)).2.2

/-- **A generic middle vertex** in the ball of the arc `k`: off `γ`, and not a bad endpoint for
segments from `c₁` or from `c₂`. -/
theorem b3Rest_exists_middle (hE : Module.finrank ℂ E = 1) (K : b3Rest_Cover E P) {γ : ℝ → C}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (k : ℤ) (c₁ c₂ : E) :
    ∃ m : C, (m ∈ (chartAt E (K.x k)).source ∧
        chartAt E (K.x k) m ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k)) ∧
      chartAt E (K.x k) m ∉ b3Rest_bad γ (K.x k) c₁ ∧
      chartAt E (K.x k) m ∉ b3Rest_bad γ (K.x k) c₂ ∧ ∀ s, γ s ≠ m := by
  set φ := chartAt E (K.x k)
  obtain ⟨v, hv, hvimg, hv1, hv2⟩ := b3Rest_exists_generic hE hγ (K.x k) c₁ c₂ isOpen_ball
    ⟨_, (K.mem_zero k).2⟩
  have hvt : v ∈ φ.target := K.ball_sub k hv
  refine ⟨φ.symm v, ⟨φ.map_target hvt, by rw [φ.right_inv hvt]; exact hv⟩,
    by rw [φ.right_inv hvt]; exact hv1, by rw [φ.right_inv hvt]; exact hv2,
    fun s hs ↦ hvimg ⟨s, by rw [hs]; exact φ.map_target hvt, by rw [hs, φ.right_inv hvt]⟩⟩

end Choice

/-! ## The refined polygon -/

section Refine

variable [FiniteDimensional ℂ E] {P : ℝ → C}

/-- **Generic vertices for a cover**: `N`-periodic junction vertices `w k` near `P (k/N)` and middle
vertices `m k`, as given by `b3Rest_exists_junction` and `b3Rest_exists_middle`. -/
structure b3Rest_Choice (K : b3Rest_Cover E P) (γ : ℝ → C) where
  w : ℤ → C
  m : ℤ → C
  w_add : ∀ k, w (k + K.N) = w k
  m_add : ∀ k, m (k + K.N) = m k
  w_mem : ∀ k, w k ∈ (chartAt E (K.x k)).source ∧
    chartAt E (K.x k) (w k) ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k)
  w_conn : ∀ k : ℤ, ∀ τ ∈ Icc (0 : ℝ) 1,
    (chartAt E (K.x k)).symm (chartAt E (K.x k) (P (k / K.N)) +
      τ • (chartAt E (K.x k) (w k) - chartAt E (K.x k) (P (k / K.N)))) ∈
        (chartAt E (K.x (k - 1))).source ∧
    chartAt E (K.x (k - 1)) ((chartAt E (K.x k)).symm (chartAt E (K.x k) (P (k / K.N)) +
      τ • (chartAt E (K.x k) (w k) - chartAt E (K.x k) (P (k / K.N))))) ∈
        ball (chartAt E (K.x (k - 1)) (K.x (k - 1))) (K.r (k - 1))
  w_off : ∀ k s, γ s ≠ w k
  m_mem : ∀ k, m k ∈ (chartAt E (K.x k)).source ∧
    chartAt E (K.x k) (m k) ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k)
  m_bad₁ : ∀ k, chartAt E (K.x k) (m k) ∉ b3Rest_bad γ (K.x k) (chartAt E (K.x k) (w k))
  m_bad₂ : ∀ k, chartAt E (K.x k) (m k) ∉ b3Rest_bad γ (K.x k) (chartAt E (K.x k) (w (k + 1)))
  m_off : ∀ k s, γ s ≠ m k

theorem b3Rest_exists_choice (hE : Module.finrank ℂ E = 1) (hper : Function.Periodic P 1)
    (K : b3Rest_Cover E P) {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    Nonempty (b3Rest_Choice K γ) := by
  have hPk : ∀ k : ℤ, P (((k + K.N : ℤ) : ℝ) / K.N) = P (k / K.N) := by
    intro k
    have := K.P_add hper k 0
    simpa only [add_zero] using this
  have hx1 : ∀ k : ℤ, K.x (k + K.N - 1) = K.x (k - 1) := fun k ↦ by
    rw [show k + K.N - 1 = (k - 1) + K.N by ring, K.x_add]
  have hr1 : ∀ k : ℤ, K.r (k + K.N - 1) = K.r (k - 1) := fun k ↦ by
    rw [show k + K.N - 1 = (k - 1) + K.N by ring, K.r_add]
  obtain ⟨w, hw_add, hw⟩ := b3Rest_exists_periodic_choice K.N _ (fun k a ↦ by
    simp only [K.x_add, K.r_add, hPk, hx1, hr1]) (b3Rest_exists_junction hE K hγ)
  have hw1 : ∀ k : ℤ, w (k + K.N + 1) = w (k + 1) := fun k ↦ by
    rw [show k + K.N + 1 = (k + 1) + K.N by ring, hw_add]
  obtain ⟨m, hm_add, hm⟩ := b3Rest_exists_periodic_choice K.N _ (fun k a ↦ by
    simp only [K.x_add, K.r_add, hw_add, hw1])
    (fun k ↦ b3Rest_exists_middle hE K hγ k (chartAt E (K.x k) (w k))
      (chartAt E (K.x k) (w (k + 1))))
  exact ⟨⟨w, m, hw_add, hm_add, fun k ↦ (hw k).1, fun k ↦ (hw k).2.1, fun k ↦ (hw k).2.2,
    fun k ↦ (hm k).1, fun k ↦ (hm k).2.1, fun k ↦ (hm k).2.2.1, fun k ↦ (hm k).2.2.2⟩⟩

namespace b3Rest_Choice

variable {K : b3Rest_Cover E P} {γ : ℝ → C} (ch : b3Rest_Choice K γ)

/-- The vertices of the refined polygon: junctions at even indices, middles at odd ones. -/
def pw (j : ℤ) : C := if j % 2 = 0 then ch.w (j / 2) else ch.m (j / 2)

theorem pw_even (k : ℤ) : ch.pw (2 * k) = ch.w k := by
  simp only [pw, show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega, ite_true]

theorem pw_odd (k : ℤ) : ch.pw (2 * k + 1) = ch.m k := by
  simp only [pw, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]
  rfl

theorem w_mem' (k : ℤ) : ch.w (k + 1) ∈ (chartAt E (K.x k)).source ∧
    chartAt E (K.x k) (ch.w (k + 1)) ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k) := by
  have h := ch.w_conn (k + 1) 1 ⟨zero_le_one, le_rfl⟩
  have ht : chartAt E (K.x (k + 1)) (ch.w (k + 1)) ∈ (chartAt E (K.x (k + 1))).target :=
    K.ball_sub _ (ch.w_mem (k + 1)).2
  rw [one_smul, add_sub_cancel, (chartAt E (K.x (k + 1))).left_inv (ch.w_mem (k + 1)).1,
    add_sub_cancel_right] at h
  exact h

/-- **The refined polygon**: `2N` segments, two in the chart of each arc of the cover. -/
def poly : b3Rest_Poly E C where
  N := 2 * K.N
  pos := by have := K.pos; omega
  x j := K.x (j / 2)
  r j := K.r (j / 2)
  w := ch.pw
  x_add j := by
    show K.x ((j + ((2 * K.N : ℕ) : ℤ)) / 2) = K.x (j / 2)
    rw [show (j + ((2 * K.N : ℕ) : ℤ)) / 2 = j / 2 + K.N by push_cast; omega, K.x_add]
  w_add j := by
    simp only [pw]
    rw [show (j + ((2 * K.N : ℕ) : ℤ)) / 2 = j / 2 + K.N by push_cast; omega,
      show (j + ((2 * K.N : ℕ) : ℤ)) % 2 = j % 2 by push_cast; omega, ch.w_add, ch.m_add]
  ball_sub j := K.ball_sub (j / 2)
  mem_w j := by
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
    · rw [pw_even, show (2 * k) / 2 = k by omega]; exact ch.w_mem k
    · rw [pw_odd, show (2 * k + 1) / 2 = k by omega]; exact ch.m_mem k
  mem_w' j := by
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
    · rw [pw_odd, show (2 * k) / 2 = k by omega]; exact ch.m_mem k
    · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pw_even, show (2 * k + 1) / 2 = k by omega]
      exact ch.w_mem' k

theorem poly_N : ch.poly.N = 2 * K.N := rfl

theorem poly_x (j : ℤ) : ch.poly.x j = K.x (j / 2) := rfl

theorem poly_r (j : ℤ) : ch.poly.r j = K.r (j / 2) := rfl

theorem poly_w (j : ℤ) : ch.poly.w j = ch.pw j := rfl

theorem follows : ch.poly.Follows P where
  arc j τ hτ := by
    rw [poly_x, poly_r, poly_N]
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
    · have h := K.mem k (τ / 2) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have harg : (((2 * k : ℤ) : ℝ) + τ) / ((2 * K.N : ℕ) : ℝ) = (k + τ / 2) / K.N := by
        have hN : (K.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 K.pos.ne'
        push_cast; field_simp
      rw [harg, show (2 * k) / 2 = k by omega]
      exact h
    · have h := K.mem k ((1 + τ) / 2) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have harg : (((2 * k + 1 : ℤ) : ℝ) + τ) / ((2 * K.N : ℕ) : ℝ) = (k + (1 + τ) / 2) / K.N := by
        have hN : (K.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 K.pos.ne'
        push_cast; field_simp; ring
      rw [harg, show (2 * k + 1) / 2 = k by omega]
      exact h
  conn j τ hτ := by
    simp only [b3Rest_Poly.A, poly_x, poly_r, poly_N, poly_w]
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
    · have harg : (((2 * k : ℤ) : ℝ)) / ((2 * K.N : ℕ) : ℝ) = k / K.N := by
        have hN : (K.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 K.pos.ne'
        push_cast; field_simp
      rw [harg, show (2 * k) / 2 = k by omega, show (2 * k - 1) / 2 = k - 1 by omega, pw_even]
      exact ch.w_conn k τ hτ
    · rw [show (2 * k + 1) / 2 = k by omega, show (2 * k + 1 - 1) / 2 = k by omega, pw_odd]
      have hc := K.mem k (1 / 2) ⟨by norm_num, by norm_num⟩
      have harg : ((k : ℝ) + 1 / 2) / K.N = (((2 * k + 1 : ℤ) : ℝ)) / ((2 * K.N : ℕ) : ℝ) := by
        have hN : (K.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 K.pos.ne'
        push_cast; field_simp
      rw [harg] at hc
      have hpt := Convex.add_smul_sub_mem (convex_ball _ _) hc.2 (ch.m_mem k).2 hτ
      have ht := K.ball_sub k hpt
      refine ⟨(chartAt E (K.x k)).map_target ht, ?_⟩
      rw [(chartAt E (K.x k)).right_inv ht]
      exact hpt

end b3Rest_Choice

theorem b3Rest_Choice.transverse (hE : Module.finrank ℂ E = 1) {K : b3Rest_Cover E P}
    (γs : b3_SmoothLoop E C) (ch : b3Rest_Choice K γs.1) : b3_Transverse E γs ch.poly.smoothLoop := by
  refine b3Rest_Poly.transverse hE ch.poly γs (fun j s ↦ ?_) (fun j s l hl hs hcross a b hab ↦ ?_)
  · rw [b3Rest_Choice.poly_w]
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
    · rw [b3Rest_Choice.pw_even]; exact ch.w_off k s
    · rw [b3Rest_Choice.pw_odd]; exact ch.m_off k s
  · simp only [b3Rest_Poly.A, b3Rest_Poly.B, poly_x, b3Rest_Choice.poly_w] at hs hcross hab
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
    · rw [show (2 * k) / 2 = k by omega] at hs hcross hab
      rw [b3Rest_Choice.pw_odd, b3Rest_Choice.pw_even] at hcross hab
      by_contra hne
      exact ch.m_bad₁ k ⟨s, l, hs, ⟨hl.1, hl.2.le⟩, hcross, a, b, not_and_or.1 hne, hab⟩
    · rw [show (2 * k + 1) / 2 = k by omega] at hs hcross hab
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, b3Rest_Choice.pw_odd, b3Rest_Choice.pw_even] at hcross hab
      by_contra hne
      refine ch.m_bad₂ k ⟨s, 1 - l, hs, ⟨by linarith [hl.2], by linarith [hl.1]⟩, ?_, a, -b, ?_, ?_⟩
      · rw [hcross]; module
      · rcases not_and_or.1 hne with h | h
        · exact Or.inl h
        · exact Or.inr (neg_ne_zero.2 h)
      · rw [← hab]; module


attribute [local instance] b3Forms_isManifold_real in
/-- **Every pair of loops has a transverse representative**: for `C¹` loops `γ`, `δ` on a Riemann
surface there is a `C¹` loop `δ'` transverse to `γ` with the periods of `δ`. -/
theorem b3Rest_exists_transverse (hE : Module.finrank ℂ E = 1) (γ δ : b3_SmoothLoop E C) :
    ∃ δ' : b3_SmoothLoop E C, b3_Transverse E γ δ' ∧ b3_period E C δ' = b3_period E C δ := by
  obtain ⟨N, hN, x, r, hx, hr, hball, hmem⟩ :=
    b3Rest_exists_chartCover (E := E) δ.1 δ.2.2.continuous δ.2.1
  let K : b3Rest_Cover E δ.1 := ⟨N, hN, x, r, hx, hr, hball, hmem⟩
  obtain ⟨ch⟩ := b3Rest_exists_choice hE δ.2.1 K γ.2.2
  refine ⟨ch.poly.smoothLoop, b3Rest_Choice.transverse hE γ ch, ?_⟩
  funext θ
  have hF := ch.follows
  have him : b3Forms_d (b3Forms_imForm θ) = 0 := by
    rw [b3Forms_imForm_eq]; exact b3Forms_d_reForm hE _
  rw [b3Forms_period_eq, b3Forms_period_eq]
  show (b3Forms_lineIntegral (b3Forms_reForm θ) ch.poly.loop 0 1 : ℂ) +
      Complex.I * (b3Forms_lineIntegral (b3Forms_imForm θ) ch.poly.loop 0 1 : ℂ) = _
  rw [b3Rest_Poly.lineIntegral_loop hF δ.2.2 δ.2.1 (b3Forms_isSmooth_reForm θ)
      (b3Forms_d_reForm hE θ),
    b3Rest_Poly.lineIntegral_loop hF δ.2.2 δ.2.1 (b3Forms_isSmooth_imForm θ) him]

end Refine

end HodgeLean.Foundations.Program

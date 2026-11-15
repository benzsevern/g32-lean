import HodgeLean.Foundations.Program.PrymParabolicMarkedLoops
import HodgeLean.Foundations.Program.PrymParabolicRealization
import HodgeLean.Foundations.Program.CurveJacobianRest2Simplex
import HodgeLean.Foundations.Program.HurwitzPrymCovSphere

/-! # Definitions for stage H3b steps A and B: singular simplices of the base decomposition

Stage H3c (`PrymParabolicMarkedLoopsDefs`) places the arcs `f_0, …, f_12` from `b₀ = -11/2 + 10 i`
to `b_∞ = -11/2 − 10 i` at the configuration `mr_base` (marks `p_i = -12, …, -3, 0, 1, ∞`).
This file adds the remaining cells of G32 Figure 1 as explicit singular simplices of the sphere:

- the edges `e_i : b₀ → p_i` and `h_i : p_i → b_∞` (straight segments for `i < 12`; for `i = 12`
  the vertical rays above `b₀` and below `b_∞`, through `∞`);
- the triangles `A_i`, `B_i` with vertices `[b₀, p_i, b_∞]`: `A_i` fills the part of sector `i`
  between `f_i` and `e_i ∪ h_i`, `B_i` the part between `e_i ∪ h_i` and `f_{i+1}`.

For `i < 12` a triangle is the explicit map `hg5_wedge u v` (`u` the crossing point of its arc,
`v` the real mark): at barycentric weights `(a₀, a₁, a₂)` its height is `10 (a₀ − a₂)` and its real
part runs from the profile of the arc through `u` to the profile of the edges through `v`.
For `i = 12` it is the radial cone from the centre `-11/2` beyond the arc `f_12` (or `f_0`) out to
`∞`, written in the chart `w = 1 / (z + 11/2)` (`hg5_cone`).

The cells are indexed by the cells of H3a's complex for the trivial group (`hg2_Tri Unit 13`,
`hg2_Edge Unit 13`, `hg2_Vert`), so that the base decomposition is `X̃` of the trivial tuple.
For a lift of the triangles into a cover (a family `L` of singular `2`-simplices), the lifted
edges are read off as faces of the lifted `A`-triangles and the lifted vertices as vertices of
them; `hg5_chain0/1/2` turn families of simplices into maps from cellular to singular chains.

Nothing here proves face compatibility, that the cells decompose the sphere, or anything about
lifts; those are the statements of `PrymParabolicSimplices.lean`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Complex Convexity CategoryTheory

namespace HodgeLean.Foundations.Program

/-! ## The real marks and the chart at `∞` -/

/-- The real parts of the finite marks `p_0, …, p_11 = -12, …, -3, 0, 1` of `mr_base`.
Source: `mr_base`, `b6_branch` (MarkedRootCoverDefs). -/
def hg5_markRe : Fin 12 → ℝ := ![-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, 0, 1]

example : ((hg5_markRe 3 : ℝ) : ℂ) = mr_base 3 := by
  simp [hg5_markRe, mr_base]; norm_num

/-- The inverse of the chart `w = 1 / (z + 11/2)` at `∞`: `w ↦ -11/2 + 1 / w`, with `0 ↦ ∞`.
Source: `b4cov_sphInvHomeo` (the inversion of the sphere); Mathlib `Homeomorph.onePointCongr`. -/
def hg5_chartInv : C(ℂ, OnePoint ℂ) :=
  ⟨fun w ↦ OnePoint.map (fun z ↦ z + mr_centre) (b4cov_sphInv (w : OnePoint ℂ)),
    (Homeomorph.addRight mr_centre).onePointCongr.continuous.comp
      (b4cov_sphInv_continuous.comp OnePoint.continuous_coe)⟩

theorem hg5_chartInv_zero : hg5_chartInv 0 = OnePoint.infty := by
  change OnePoint.map (fun z ↦ z + mr_centre) (b4cov_sphInv ((0 : ℂ) : OnePoint ℂ)) = _
  simp

theorem hg5_chartInv_ne {w : ℂ} (hw : w ≠ 0) :
    hg5_chartInv w = ((mr_centre + w⁻¹ : ℂ) : OnePoint ℂ) := by
  change OnePoint.map (fun z ↦ z + mr_centre) (b4cov_sphInv (w : OnePoint ℂ)) = _
  rw [b4cov_sphInv_coe hw, OnePoint.map_some, add_comm]

example : hg5_chartInv 0 = OnePoint.infty := hg5_chartInv_zero

/-! ## The edges -/

/-- The edge `e_i : b₀ → p_i`: for `i < 12` the segment from `b₀` to the real mark; for `i = 12`
the vertical ray `s ↦ -11/2 + 10 i / (1 − s)` above `b₀`, reaching `∞` at `s = 1`.
Source: G32 v0.16, Figure 1 (the edge `e_i`); `docs/specs/PrymParabolicMarkedLoops.md`, plan A. -/
def hg5_edgeE (i : Fin 13) : C(unitInterval, OnePoint ℂ) :=
  if h : i.val < 12 then
    ⟨fun s ↦ ((mr_basePoint + ((s : ℝ) : ℂ) * ((hg5_markRe ⟨i.val, h⟩ : ℂ) - mr_basePoint) : ℂ) :
      OnePoint ℂ), by fun_prop⟩
  else hg5_chartInv.comp ⟨fun s ↦ -I * (((1 - (s : ℝ)) / 10 : ℝ) : ℂ), by fun_prop⟩

example (i : Fin 13) : hg5_edgeE i 0 = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
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

/-- The edge `h_i : p_i → b_∞`: for `i < 12` the segment from the real mark to `b_∞`; for
`i = 12` the vertical ray `s ↦ -11/2 − 10 i / s` below `b_∞`, starting at `∞`.
Source: G32 v0.16, Figure 1 (the edge `h_i`); `docs/specs/PrymParabolicMarkedLoops.md`, plan A. -/
def hg5_edgeH (i : Fin 13) : C(unitInterval, OnePoint ℂ) :=
  if h : i.val < 12 then
    ⟨fun s ↦ (((hg5_markRe ⟨i.val, h⟩ : ℂ) + ((s : ℝ) : ℂ) * (hg3_bottom - hg5_markRe ⟨i.val, h⟩) :
      ℂ) : OnePoint ℂ), by fun_prop⟩
  else hg5_chartInv.comp ⟨fun s ↦ I * ((((s : ℝ)) / 10 : ℝ) : ℂ), by fun_prop⟩

example : hg5_edgeH 12 0 = OnePoint.infty := by
  simp [hg5_edgeH, hg5_chartInv_zero]

/-- The arc `f_i` of stage H3c as a path in the sphere.
Source: `hg3_arc`. -/
def hg5_edgeF (i : Fin 13) : C(unitInterval, OnePoint ℂ) :=
  ⟨fun s ↦ ((hg3_arc i s : ℂ) : OnePoint ℂ), by
    have : Continuous (hg3_arc i) := by unfold hg3_arc; fun_prop
    exact OnePoint.continuous_coe.comp (this.comp continuous_subtype_val)⟩

example (i : Fin 13) : hg5_edgeF i 0 = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
  simp [hg5_edgeF, hg3_arc]

/-! ## The triangles -/

/-- The finite triangle with vertices `[b₀, v, b_∞]` between the arc through the real point `u`
and the edges through the real point `v`: at weights `(a₀, a₁, a₂)`, height `10 (a₀ − a₂)` and
real part `-11/2 + (u + 11/2)(1 − |a₀ − a₂|) + (v − u) a₁`.
Source: G32 v0.16, Figure 1 (the triangles `A_i`, `B_i`); barycentric coordinates. -/
def hg5_wedge (u v : ℝ) : C(StdSimplex ℝ (Fin 3), ℂ) :=
  ⟨fun a ↦ ((-11 / 2 + (u + 11 / 2) * (1 - |a.weights 0 - a.weights 2|) +
      (v - u) * a.weights 1 : ℝ) : ℂ) + ((10 * (a.weights 0 - a.weights 2) : ℝ) : ℂ) * I, by
    have h0 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 0
    have h1 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 1
    have h2 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 2
    fun_prop⟩

example (u v : ℝ) : hg5_wedge u v (StdSimplex.single 1) = (v : ℂ) := by
  simp [hg5_wedge]; ring

/-- The chart value of the cone over the arc through `u` (`k = 2 (u + 11/2)`):
`(a₀ + a₂)² / (k · min a₀ a₂ + 10 (a₀ − a₂) i)`, which is `0` (the point `∞`) at `a₁ = 1`.
Source: the radial cone `z = -11/2 + (f(s) + 11/2) / (a₀ + a₂)`, `s = a₂ / (a₀ + a₂)`, in the
chart `w = 1 / (z + 11/2)`. -/
def hg5_coneFun (k : ℝ) (a : StdSimplex ℝ (Fin 3)) : ℂ :=
  (((a.weights 0 + a.weights 2) ^ 2 : ℝ) : ℂ) /
    (((k * min (a.weights 0) (a.weights 2) : ℝ) : ℂ) +
      ((10 * (a.weights 0 - a.weights 2) : ℝ) : ℂ) * I)

example (k : ℝ) : hg5_coneFun k (StdSimplex.single 1) = 0 := by
  simp [hg5_coneFun]

theorem hg5_coneFun_norm_le (k : ℝ) (hk : k ≠ 0) (a : StdSimplex ℝ (Fin 3)) :
    ‖hg5_coneFun k a‖ ≤ (2 / |k| + 1 / 10) * (a.weights 0 + a.weights 2) := by
  have h0 := a.weights_nonneg 0
  have h2 := a.weights_nonneg 2
  set D : ℂ := ((k * min (a.weights 0) (a.weights 2) : ℝ) : ℂ) +
      ((10 * (a.weights 0 - a.weights 2) : ℝ) : ℂ) * I with hD
  have hk' : 0 < |k| := abs_pos.mpr hk
  have hC : 0 ≤ 2 / |k| + 1 / 10 := by positivity
  have hs : 0 ≤ a.weights 0 + a.weights 2 := by linarith
  by_cases hD0 : D = 0
  · simp only [hg5_coneFun, ← hD, hD0, div_zero, norm_zero]
    positivity
  have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD0
  have hre : abs (k * min (a.weights 0) (a.weights 2)) ≤ ‖D‖ := by
    have := Complex.abs_re_le_norm D
    simpa [hD] using this
  have him : abs (10 * (a.weights 0 - a.weights 2)) ≤ ‖D‖ := by
    have := Complex.abs_im_le_norm D
    simpa [hD] using this
  have hmin : 0 ≤ min (a.weights 0) (a.weights 2) := le_min h0 h2
  have hsplit : a.weights 0 + a.weights 2 =
      2 * min (a.weights 0) (a.weights 2) + |a.weights 0 - a.weights 2| := by
    rcases le_total (a.weights 0) (a.weights 2) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  have hs_le : a.weights 0 + a.weights 2 ≤ (2 / |k| + 1 / 10) * ‖D‖ := by
    rw [abs_mul, abs_of_nonneg hmin] at hre
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10)] at him
    have e1 : 2 * min (a.weights 0) (a.weights 2) ≤ 2 / |k| * ‖D‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hk']
      nlinarith
    have e2 : |a.weights 0 - a.weights 2| ≤ 1 / 10 * ‖D‖ := by linarith
    linarith
  have hnum : ‖(((a.weights 0 + a.weights 2) ^ 2 : ℝ) : ℂ)‖ = (a.weights 0 + a.weights 2) ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [hg5_coneFun, ← hD, norm_div, hnum]
  rw [div_le_iff₀ hDpos]
  calc (a.weights 0 + a.weights 2) ^ 2
      = (a.weights 0 + a.weights 2) * (a.weights 0 + a.weights 2) := sq _
    _ ≤ (a.weights 0 + a.weights 2) * ((2 / |k| + 1 / 10) * ‖D‖) :=
        mul_le_mul_of_nonneg_left hs_le hs
    _ = (2 / |k| + 1 / 10) * (a.weights 0 + a.weights 2) * ‖D‖ := by ring

theorem hg5_coneFun_continuous (k : ℝ) (hk : k ≠ 0) : Continuous (hg5_coneFun k) := by
  have h0 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 0
  have h2 := StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 3) 2
  rw [continuous_iff_continuousAt]
  intro a
  set D : StdSimplex ℝ (Fin 3) → ℂ := fun b ↦
    ((k * min (b.weights 0) (b.weights 2) : ℝ) : ℂ) +
      ((10 * (b.weights 0 - b.weights 2) : ℝ) : ℂ) * I with hD
  have hDc : Continuous D := by simp only [hD]; fun_prop
  by_cases hDa : D a = 0
  · have hw : a.weights 0 = 0 ∧ a.weights 2 = 0 := by
      have him := congrArg Complex.im hDa
      have hre := congrArg Complex.re hDa
      simp [hD] at him hre
      have e : a.weights 0 = a.weights 2 := by linarith
      rcases hre with hre | hre
      · exact absurd hre hk
      · rw [e, min_self] at hre
        exact ⟨e.trans hre, hre⟩
    have hval : hg5_coneFun k a = 0 := by simp [hg5_coneFun, hw]
    have ht : Filter.Tendsto (fun b : StdSimplex ℝ (Fin 3) ↦
        (2 / |k| + 1 / 10) * (b.weights 0 + b.weights 2)) (nhds a) (nhds 0) := by
      have := ((h0.add h2).const_mul (2 / |k| + 1 / 10)).tendsto a
      simpa [hw] using this
    show Filter.Tendsto _ _ _
    rw [hval]
    exact squeeze_zero_norm (hg5_coneFun_norm_le k hk) ht
  · have hn : Continuous (fun b : StdSimplex ℝ (Fin 3) ↦
        (((b.weights 0 + b.weights 2) ^ 2 : ℝ) : ℂ)) := by fun_prop
    exact hn.continuousAt.div hDc.continuousAt hDa

/-- The cone triangle in sector `12` with vertices `[b₀, ∞, b_∞]`, over the arc through `u`:
`hg5_chartInv ∘ hg5_coneFun (2 (u + 11/2))`. For `u = w_12` it is `A_12`, for `u = w_0` it is
`B_12`; its faces are `h_12` (weight `a₀ = 0`), the arc (`a₁ = 0`) and `e_12` (`a₂ = 0`).
Source: G32 v0.16, Figure 1 (the sector of `∞`); the radial cone from `-11/2`. -/
def hg5_cone (i : Fin 13) (hi : hg3_waist i + 11 / 2 ≠ 0) : C(StdSimplex ℝ (Fin 3), OnePoint ℂ) :=
  hg5_chartInv.comp ⟨hg5_coneFun (2 * (hg3_waist i + 11 / 2)),
    hg5_coneFun_continuous _ (mul_ne_zero two_ne_zero hi)⟩

theorem hg5_waist12_ne : hg3_waist 12 + 11 / 2 ≠ 0 := by norm_num [hg3_waist]

theorem hg5_waist0_ne : hg3_waist 0 + 11 / 2 ≠ 0 := by norm_num [hg3_waist]

example : hg5_cone 12 hg5_waist12_ne (StdSimplex.single 1) = OnePoint.infty := by
  simp [hg5_cone, hg5_coneFun, hg5_chartInv_zero]

/-- The triangle `A_i`, vertices `[b₀, p_i, b_∞]`, between `f_i` and `e_i ∪ h_i`.
Source: G32 v0.16, Figure 1; `hg2_face0/1/2` (faces `h_i`, `f_i`, `e_i`). -/
def hg5_triA (i : Fin 13) : C(StdSimplex ℝ (Fin 3), OnePoint ℂ) :=
  if h : i.val < 12 then
    (⟨((↑) : ℂ → OnePoint ℂ), OnePoint.continuous_coe⟩ : C(ℂ, OnePoint ℂ)).comp
      (hg5_wedge (hg3_waist i) (hg5_markRe ⟨i.val, h⟩))
  else hg5_cone 12 hg5_waist12_ne

example : hg5_triA 0 (StdSimplex.single 1) = ((-12 : ℂ) : OnePoint ℂ) := by
  simp [hg5_triA, hg5_wedge, hg5_markRe]; ring

/-- The triangle `B_i`, vertices `[b₀, p_i, b_∞]`, between `e_i ∪ h_i` and `f_{i+1}` (index
mod `13`).
Source: G32 v0.16, Figure 1; `hg2_face0/1/2` (faces `h_i`, `f_{i+1}`, `e_i`). -/
def hg5_triB (i : Fin 13) : C(StdSimplex ℝ (Fin 3), OnePoint ℂ) :=
  if h : i.val < 12 then
    (⟨((↑) : ℂ → OnePoint ℂ), OnePoint.continuous_coe⟩ : C(ℂ, OnePoint ℂ)).comp
      (hg5_wedge (hg3_waist (finRotate 13 i)) (hg5_markRe ⟨i.val, h⟩))
  else hg5_cone 0 hg5_waist0_ne

example : hg5_triB 12 (StdSimplex.single 1) = OnePoint.infty := by
  simp [hg5_triB, hg5_cone, hg5_coneFun, hg5_chartInv_zero]

/-! ## The base cells, indexed by H3a's complex for the trivial group -/

/-- The trivial tuple of length `13`: the base decomposition is `X̃` of this tuple.
Source: `hg2_Vert`, `hg2_Edge`, `hg2_Tri` with `G = Unit`. -/
def hg5_one : Fin 13 → Unit := fun _ ↦ 1

example : (List.ofFn hg5_one).prod = 1 := rfl

/-- The base triangles: `A_i` for `Sum.inl (i, ·)`, `B_i` for `Sum.inr (i, ·)`.
Source: G32 v0.16, Figure 1; `hg2_Tri`. -/
def hg5_tri : hg2_Tri Unit 13 → C(StdSimplex ℝ (Fin 3), OnePoint ℂ)
  | Sum.inl (i, _) => hg5_triA i
  | Sum.inr (i, _) => hg5_triB i

example (i : Fin 13) : hg5_tri (Sum.inl (i, ())) = hg5_triA i := rfl

/-- The base edges: `e_i`, `f_i`, `h_i` in the order of `hg2_Edge`.
Source: G32 v0.16, Figure 1; `hg2_Edge`. -/
def hg5_edge : hg2_Edge Unit 13 → C(unitInterval, OnePoint ℂ)
  | Sum.inl (i, _) => hg5_edgeE i
  | Sum.inr (Sum.inl (i, _)) => hg5_edgeF i
  | Sum.inr (Sum.inr (i, _)) => hg5_edgeH i

example (i : Fin 13) : hg5_edge (Sum.inr (Sum.inl (i, ()))) = hg5_edgeF i := rfl

/-- The base vertices: `b₀`, `b_∞` and the marks `p_i = b6_branch mr_base i`.
Source: G32 v0.16, Figure 1; `hg2_Vert`; `b6_branch`. -/
def hg5_vert : hg2_Vert hg5_one → OnePoint ℂ
  | Sum.inl _ => ((mr_basePoint : ℂ) : OnePoint ℂ)
  | Sum.inr (Sum.inl _) => ((hg3_bottom : ℂ) : OnePoint ℂ)
  | Sum.inr (Sum.inr ⟨i, _⟩) => b6_branch mr_base i

example : hg5_vert (Sum.inr (Sum.inr ⟨12, (1 : Unit)⟩)) = OnePoint.infty := rfl

set_option maxHeartbeats 400000 in
theorem hg5_push_continuous (t : b6t_polydisc mr_base) :
    Continuous (fun x ↦ b6t_sphere mr_base t.val x) := by
  have h := b6t_continuous mr_base mr_base_mem_chart
  exact h.comp (Continuous.prodMk (continuous_const : Continuous fun _ : OnePoint ℂ ↦ t)
    continuous_id)

/-- The B6-2a radial push at a configuration `t` of the polydisc about `mr_base`, as a
continuous map of the sphere.
Source: `b6t_sphere`, `b6t_continuous`, `mr_base_mem_chart`. -/
def hg5_push (t : b6t_polydisc mr_base) : C(OnePoint ℂ, OnePoint ℂ) :=
  ⟨fun x ↦ b6t_sphere mr_base t.val x, hg5_push_continuous t⟩

example (t : b6t_polydisc mr_base) : hg5_push t OnePoint.infty = OnePoint.infty := rfl

/-! ## Simplices, faces and chains -/

/-- The singular `0`-simplex at a point.
Source: Mathlib `TopCat.toSSetObj₀Equiv`. -/
def hg5_pointSimplex {T : Type} [TopologicalSpace T] (x : T) :
    (TopCat.toSSet.obj (TopCat.of T)).obj (Opposite.op (SimplexCategory.mk 0)) :=
  TopCat.toSSetObj₀Equiv.symm x

example {T : Type} [TopologicalSpace T] (x : T) :
    TopCat.toSSetObj₀Equiv (hg5_pointSimplex x) = x := by simp [hg5_pointSimplex]

/-- The `k`-th face of a singular `2`-simplex as a path, `t ↦ σ (map (succAbove k) t)`.
Source: Mathlib `Convexity.StdSimplex.map`, `Convexity.StdSimplex.homeomorphI`. -/
def hg5_face {T : Type} [TopologicalSpace T] (σ : C(StdSimplex ℝ (Fin 3), T)) (k : Fin 3) :
    C(unitInterval, T) :=
  σ.comp ⟨fun t ↦ StdSimplex.map k.succAbove (StdSimplex.homeomorphI.symm t),
    (StdSimplex.continuous_map (R := ℝ) _).comp StdSimplex.homeomorphI.symm.continuous⟩

/-- The `k`-th simplicial face of the singular `2`-simplex of `σ` is the singular `1`-simplex of
the path `hg5_face σ k`. -/
theorem hg5_delta_face {T : Type} [TopologicalSpace T] (σ : C(StdSimplex ℝ (Fin 3), T))
    (k : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of T)).δ k (b3Rest2_triSimplex σ) =
      b3Rest2_pathSimplex (hg5_face σ k) := by
  rw [← b3Rest2_pathSimplex_simplexPath ((TopCat.toSSet.obj (TopCat.of T)).δ k _)]
  congr 1

example {T : Type} [TopologicalSpace T] (σ : C(StdSimplex ℝ (Fin 3), T)) :
    (TopCat.toSSet.obj (TopCat.of T)).δ 2 (b3Rest2_triSimplex σ) =
      b3Rest2_pathSimplex (hg5_face σ 2) := hg5_delta_face σ 2

theorem hg5_obj0_delta_zero {T : Type} [TopologicalSpace T]
    (σ : (TopCat.toSSet.obj (TopCat.of T)).obj (Opposite.op (SimplexCategory.mk 1))) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of T)).δ 0 σ) =
      HodgeLean.Adapters.simplexPath σ 1 := by
  rw [TopCat.toSSetObj₀Equiv_apply]
  erw [TopCat.toSSetObjEquiv_δ_apply]
  change _ = (TopCat.of T).toSSetObjEquiv _ σ (Convexity.StdSimplex.homeomorphI.symm 1)
  rw [Convexity.StdSimplex.homeomorphI_symm_one]
  congr 1
  rw [Subsingleton.elim (default : Convexity.StdSimplex ℝ (Fin 1)) (Convexity.StdSimplex.single 0),
    Convexity.StdSimplex.map_single]
  rfl

theorem hg5_obj0_delta_one {T : Type} [TopologicalSpace T]
    (σ : (TopCat.toSSet.obj (TopCat.of T)).obj (Opposite.op (SimplexCategory.mk 1))) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of T)).δ 1 σ) =
      HodgeLean.Adapters.simplexPath σ 0 := by
  rw [TopCat.toSSetObj₀Equiv_apply]
  erw [TopCat.toSSetObjEquiv_δ_apply]
  change _ = (TopCat.of T).toSSetObjEquiv _ σ (Convexity.StdSimplex.homeomorphI.symm 0)
  rw [Convexity.StdSimplex.homeomorphI_symm_zero]
  congr 1
  rw [Subsingleton.elim (default : Convexity.StdSimplex ℝ (Fin 1)) (Convexity.StdSimplex.single 0),
    Convexity.StdSimplex.map_single]
  rfl

/-- The face `δ 0` of the singular `1`-simplex of a path is its end point. -/
theorem hg5_delta_path_zero {T : Type} [TopologicalSpace T] (g : C(unitInterval, T)) :
    (TopCat.toSSet.obj (TopCat.of T)).δ 0 (b3Rest2_pathSimplex g) = hg5_pointSimplex (g 1) := by
  apply TopCat.toSSetObj₀Equiv.injective
  rw [hg5_pointSimplex, Equiv.apply_symm_apply, hg5_obj0_delta_zero,
    b3Rest2_simplexPath_pathSimplex]

/-- The face `δ 1` of the singular `1`-simplex of a path is its start point. -/
theorem hg5_delta_path_one {T : Type} [TopologicalSpace T] (g : C(unitInterval, T)) :
    (TopCat.toSSet.obj (TopCat.of T)).δ 1 (b3Rest2_pathSimplex g) = hg5_pointSimplex (g 0) := by
  apply TopCat.toSSetObj₀Equiv.injective
  rw [hg5_pointSimplex, Equiv.apply_symm_apply, hg5_obj0_delta_one,
    b3Rest2_simplexPath_pathSimplex]

/-- The cellular-to-singular map in degree `2` of a family of singular `2`-simplices:
`τ ↦ [σ τ]`, extended linearly.
Source: Hatcher, *Algebraic Topology*, §2.1 (singular chains); `Simplicial.chainOfSimplex`. -/
def hg5_chain2 {ι T : Type} [TopologicalSpace T] (σ : ι → C(StdSimplex ℝ (Fin 3), T)) :
    (ι →₀ ℤ) →ₗ[ℤ] AlgebraicTopology.Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 2 :=
  Finsupp.linearCombination ℤ fun τ ↦
    AlgebraicTopology.Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex (σ τ))

example {ι T : Type} [TopologicalSpace T] (σ : ι → C(StdSimplex ℝ (Fin 3), T)) (τ : ι) :
    hg5_chain2 σ (Finsupp.single τ 1) =
      Finsupp.linearCombination ℤ (fun τ ↦
        AlgebraicTopology.Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex (σ τ))) (Finsupp.single τ 1) :=
  rfl

/-- The cellular-to-singular map in degree `1` of a family of paths.
Source: Hatcher, §2.1; `b3Rest2_pathSimplex`. -/
def hg5_chain1 {ι T : Type} [TopologicalSpace T] (e : ι → C(unitInterval, T)) :
    (ι →₀ ℤ) →ₗ[ℤ] AlgebraicTopology.Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 1 :=
  Finsupp.linearCombination ℤ fun ε ↦
    AlgebraicTopology.Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (e ε))

example {ι T : Type} [TopologicalSpace T] (e : ι → C(unitInterval, T)) (ε : ι) :
    hg5_chain1 e (Finsupp.single ε 1) =
      Finsupp.linearCombination ℤ (fun ε ↦
        AlgebraicTopology.Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (e ε))) (Finsupp.single ε 1) :=
  rfl

/-- The cellular-to-singular map in degree `0` of a family of points.
Source: Hatcher, §2.1; `hg5_pointSimplex`. -/
def hg5_chain0 {ι T : Type} [TopologicalSpace T] (v : ι → T) :
    (ι →₀ ℤ) →ₗ[ℤ] AlgebraicTopology.Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 0 :=
  Finsupp.linearCombination ℤ fun x ↦
    AlgebraicTopology.Simplicial.chainOfSimplex ℤ (hg5_pointSimplex (v x))

example {ι T : Type} [TopologicalSpace T] (v : ι → T) (x : ι) :
    hg5_chain0 v (Finsupp.single x 1) =
      Finsupp.linearCombination ℤ (fun x ↦
        AlgebraicTopology.Simplicial.chainOfSimplex ℤ (hg5_pointSimplex (v x))) (Finsupp.single x 1) :=
  rfl

/-! ## Lifted cells -/

/-- The base cell under a lifted triangle: `A_i(x) ↦ A_i`, `B_i(x) ↦ B_i`.
Source: `hg2_Tri`. -/
def hg5_triBase {G : Type*} : hg2_Tri G 13 → hg2_Tri Unit 13
  | Sum.inl (i, _) => Sum.inl (i, ())
  | Sum.inr (i, _) => Sum.inr (i, ())

example {G : Type*} (i : Fin 13) (x : G) : hg5_triBase (Sum.inr (i, x)) = Sum.inr (i, ()) := rfl

/-- The sheet label of a lifted triangle, the label `x` of its vertex `b₀(x)`.
Source: `hg2_Tri`; G32 v0.16, Figure 1. -/
def hg5_triSheet {G : Type*} : hg2_Tri G 13 → G
  | Sum.inl (_, x) => x
  | Sum.inr (_, x) => x

example {G : Type*} (i : Fin 13) (x : G) : hg5_triSheet (Sum.inl (i, x)) = x := rfl

/-- The lifted edges of a family `L` of lifted triangles, read off from the `A`-triangles:
`e_i(x)`, `f_i(x)`, `h_i(x)` are the faces `2`, `1`, `0` of `L (A_i(x))`.
Source: `hg2_face0/1/2` on `A_i(x)`. -/
def hg5_liftEdge {G T : Type} [TopologicalSpace T]
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), T)) : hg2_Edge G 13 → C(unitInterval, T)
  | Sum.inl (i, x) => hg5_face (L (Sum.inl (i, x))) 2
  | Sum.inr (Sum.inl (i, x)) => hg5_face (L (Sum.inl (i, x))) 1
  | Sum.inr (Sum.inr (i, x)) => hg5_face (L (Sum.inl (i, x))) 0

example {G T : Type} [TopologicalSpace T] (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), T))
    (i : Fin 13) (x : G) :
    hg5_liftEdge L (Sum.inl (i, x)) = hg5_face (L (Sum.inl (i, x))) 2 := rfl

/-- The lifted vertices of a family `L`: `b₀(x)` is vertex `0` of `L (A_0(x))`, `b_∞(z)` is
vertex `2` of `L (A_0(z))` (the end of `f_0(z)`, `Q_0 = 1`), and `p_i(c)` is vertex `1` of
`L (A_i(x))` for the chosen representative `x` of the coset `c`.
Source: `hg2_Vert`, `hg2_tgt`; `Quotient.out`. -/
def hg5_liftVert {G T : Type} [Group G] [TopologicalSpace T] (g : Fin 13 → G)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), T)) : hg2_Vert g → T
  | Sum.inl x => L (Sum.inl (0, x)) (StdSimplex.single 0)
  | Sum.inr (Sum.inl z) => L (Sum.inl (0, z)) (StdSimplex.single 2)
  | Sum.inr (Sum.inr ⟨i, c⟩) => L (Sum.inl (i, c.out)) (StdSimplex.single 1)

example {G T : Type} [Group G] [TopologicalSpace T] (g : Fin 13 → G)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), T)) (x : G) :
    hg5_liftVert g L (Sum.inl x) = L (Sum.inl (0, x)) (StdSimplex.single 0) := rfl

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.HurwitzPrymMarked
import HodgeLean.Foundations.Program.HurwitzFamilyMarked
import HodgeLean.Foundations.Program.PrymVariationCentreChevalleyWeil

/-! # The marked root cover: explicit configuration, peripheral loops, product check

Definitions for an explicit normalized configuration on the negative real axis, an explicit
base point above it, and thirteen explicit based curves: a lasso around each finite mark
(straight segment, counterclockwise circle of radius `1/4`, segment back) and a clockwise
circle of radius `10` around all finite marks, which is a counterclockwise loop around `∞`.
The curves avoid every branch disc of `b6t_polydisc mr_base`, so the same curves serve every
configuration of that polydisc.

**Convention.** Chronological concatenation of loops multiplies in reverse order in
`FundamentalGroup` (`fromPath (c.trans d) = fromPath d * fromPath c`); Mathlib's covering
monodromy `IsQuotientCoveringMap.fundamentalGroupToMulOpposite` takes values in `Gᵐᵒᵖ`, and
`unop` reverses it back (`HurwitzPrymRexCover.psi_trans`). H6's certificate matches endpoint
transport `x ↦ x gᵢ`, hence the monodromy value `op (gᵢ)` on loop `i`, and the loop relation
reads `(List.ofFn γ).reverse.prod = 1`. HC no distance; AV milestone no distance.
-/

noncomputable section

open Complex

namespace HodgeLean.Foundations.Program

/-- The explicit base configuration: the ten moving marks at `-12, -11, …, -3`, so that the
thirteen marks of `b6_branch mr_base` are `-12, …, -3, 0, 1, ∞` in index order, increasing
along the real axis.
Source: G32 v0.16, §3.1 (normalized configurations); `b6_branch`. -/
def mr_base : Fin 10 → ℂ := fun i ↦ (i.val : ℂ) - 12

example : mr_base 0 = -12 := by simp [mr_base]

/-- The twelve finite marks of the base configuration, in index order.
Source: `b6_branch`, restricted to its finite entries at `mr_base`. -/
def mr_marks : Fin 12 → ℂ := Fin.append mr_base ![0, 1]

example : mr_marks 10 = 0 := rfl

/-- Centre of the outer circle: the midpoint of `-12` and `1`.
Source: elementary plane geometry. -/
def mr_centre : ℂ := -11 / 2

example : mr_centre = -11 / 2 := rfl

/-- The base point `-11/2 + 10 i`, the top of the outer circle, above every mark.
Source: elementary plane geometry. -/
def mr_basePoint : ℂ := mr_centre + 10 * I

example : mr_basePoint.im = 10 := by simp [mr_basePoint, mr_centre]

/-- The lasso around a finite mark `p`: on `[0, 1/3]` the segment from the base point to
`p + i/4`, on `[1/3, 2/3]` the counterclockwise circle `p + (i/4) e^{2πi(3s-1)}`, on
`[2/3, 1]` the segment back.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §4 and §13 (standard generators of
a punctured sphere); Völklein, *Groups as Galois Groups*, §4.1 (standard loop systems). -/
def mr_lasso (p : ℂ) (s : ℝ) : ℂ :=
  if s ≤ 1 / 3 then mr_basePoint + ((3 * s : ℝ) : ℂ) * (p + I / 4 - mr_basePoint)
  else if s ≤ 2 / 3 then p + I / 4 * exp (2 * Real.pi * I * ((3 * s - 1 : ℝ) : ℂ))
  else mr_basePoint + ((3 - 3 * s : ℝ) : ℂ) * (p + I / 4 - mr_basePoint)

example (p : ℂ) : mr_lasso p 0 = mr_basePoint := by simp [mr_lasso]

/-- The outer loop: the clockwise circle of radius `10` about `mr_centre` from the base point.
In the coordinate `1/z` at `∞` it is counterclockwise.
Source: Forster, GTM 81, §1.3 (the chart at `∞`) and §13. -/
def mr_outer (s : ℝ) : ℂ := mr_centre + 10 * I * exp (-(2 * Real.pi * I * (s : ℂ)))

example : mr_outer 0 = mr_basePoint := by simp [mr_outer, mr_basePoint]

/-- The thirteen explicit peripheral curves on the sphere: lassos around the finite marks
`0, …, 11` and the outer loop around `∞` for index `12`.
Source: `mr_lasso`, `mr_outer`; the ordering of `b6_branch`. -/
def mr_curve (i : Fin 13) (s : ℝ) : OnePoint ℂ :=
  if h : i.val < 12 then ((mr_lasso (mr_marks ⟨i.val, h⟩) s : ℂ) : OnePoint ℂ)
  else ((mr_outer s : ℂ) : OnePoint ℂ)

example : mr_curve 12 0 = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
  simp [mr_curve, mr_outer, mr_basePoint]

/-- A loop class at the configuration `t` is the `i`-th explicit peripheral class when some
based path representing it traces exactly the curve `mr_curve i`.
Source: `mr_curve`; Mathlib `FundamentalGroup.fromPath`. -/
def mr_IsLoop (t : Fin 10 → ℂ) (y₀ : b6t_punctured t) (i : Fin 13)
    (c : FundamentalGroup (b6t_punctured t) y₀) : Prop :=
  ∃ p : Path y₀ y₀, (∀ s : unitInterval, (p s : OnePoint ℂ) = mr_curve i s) ∧
    FundamentalGroup.fromPath ⟦p⟧ = c

/-- A class traced by an explicit curve has the base point of that curve. -/
example (t : Fin 10 → ℂ) (y₀ : b6t_punctured t) (i : Fin 13)
    (c : FundamentalGroup (b6t_punctured t) y₀) (h : mr_IsLoop t y₀ i c) :
    (y₀ : OnePoint ℂ) = mr_curve i 0 := by
  obtain ⟨p, hp, -⟩ := h
  simpa using hp 0

/-- **Satisfiability check.** The product `(List.ofFn b4b_root).prod = 1` (B6-3d) makes
the loop relation `(List.ofFn γ).reverse.prod = 1` consistent with sending loop `i` to
`op (b4b_root i)`: the reversed product of the opposite values is one.
Source: `b63d_root_product`; `MulOpposite.op_list_prod`. -/
theorem mr_root_op_reverse_prod :
    (List.ofFn fun i ↦ MulOpposite.op (b4b_root i)).reverse.prod = 1 := by
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_list_prod, MulOpposite.unop_one, List.map_reverse,
    List.reverse_reverse, List.map_ofFn]
  exact b63d_root_product

/-- The root tuple itself has product one (B6-3d, cited, not restated). -/
example : (List.ofFn b4b_root).prod = 1 := b63d_root_product

/-- **Non-degeneracy.** No monodromy value `op (b4b_root j)` is trivial: every local
generator has order `3`, or `2` at `∞` (`b63_root_order`). -/
example (j : Fin 13) : MulOpposite.op (b4b_root j) ≠ 1 := by
  intro h
  have h1 : b4b_root j = 1 := MulOpposite.op_injective (h.trans MulOpposite.op_one.symm)
  have h2 := b63_root_order j
  rw [h1, orderOf_one] at h2
  split_ifs at h2 <;> omega

end HodgeLean.Foundations.Program

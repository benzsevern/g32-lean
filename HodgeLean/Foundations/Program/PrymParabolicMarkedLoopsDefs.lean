import HodgeLean.Foundations.Program.MarkedRootCover
import HodgeLean.Foundations.Program.PrymParabolicComparisonLemmas
import HodgeLean.Foundations.Program.PrymVariationCentreChevalleyWeil

/-! # Definitions for stage H3c: the oriented base decomposition of G32 Figure 1 at `mr_base`

Stage H3a (`PrymParabolicComparisonDefs`) builds the lifted Δ-complex `X̃(g)` of G32 Figure 1
from vertices `b₀`, `b_∞`, `p_i`, arcs `f_i : b₀ → b_∞`, edges `e_i : b₀ → p_i`,
`h_i : p_i → b_∞`, and declares that the loop `ℓ_i = f_i f_{i+1}⁻¹` goes once around `p_i`. This
file places the arcs `f_0, …, f_12` in the sphere at the explicit configuration of the marked
root cover (`MarkedRootCoverDefs`: `mr_base`, marks `-12, …, -3, 0, 1, ∞` and the base
point `mr_basePoint = -11/2 + 10 i`): each `f_i` runs from the base point `b₀` straight down to the real point
`w_i` and on to the auxiliary vertex `b_∞ = -11/2 − 10 i`. The crossing points increase,
`w_0 < p_0 < w_1 < ⋯ < p_11 < w_12`, so the arcs leave `b₀` in counterclockwise order, `ℓ_i`
runs counterclockwise around `p_i`, and `ℓ_12 = f_12 f_0⁻¹` runs clockwise in `ℂ`, that is,
counterclockwise around `∞`. The sectors are the open regions between consecutive arcs; sector
`12` is the outside of the fan bounded by `f_0` and `f_12`, and contains `∞`.

The configuration, the base point, the lassos `mr_curve` and the loop predicate `mr_IsLoop` are
those of `MarkedRootCoverDefs`, used directly.

Nothing here proves that the arcs avoid the marks, that the sectors partition the complement,
or that `ℓ_i` is homotopic to the lasso; those are the statements of
`PrymParabolicMarkedLoops.lean`. HC no distance; AV milestone no distance.
-/

noncomputable section

open Complex

namespace HodgeLean.Foundations.Program

/-! ## The arcs `f_i` and the sectors -/

/-- The auxiliary vertex `b_∞ = -11/2 − 10 i`, the bottom of the outer circle (not the mark
`∞ = p_12`).
Source: G32 v0.16, Figure 1 (the vertex `b_∞`); elementary plane geometry. -/
def hg3_bottom : ℂ := mr_centre - 10 * I

example : hg3_bottom.im = -10 := by simp [hg3_bottom, mr_centre]

/-- The real crossing point `w_i` of the arc `f_i`: `w_0 = -25/2` left of every mark,
`w_i` the midpoint of the marks `p_{i−1}, p_i` for `1 ≤ i ≤ 11`, and `w_12 = 3/2` right of every
finite mark.
Source: G32 v0.16, Figure 1 (the arcs `f_i` separate consecutive marks). -/
def hg3_waist : Fin 13 → ℝ :=
  ![-25 / 2, -23 / 2, -21 / 2, -19 / 2, -17 / 2, -15 / 2, -13 / 2, -11 / 2, -9 / 2, -7 / 2,
    -3 / 2, 1 / 2, 3 / 2]

example : hg3_waist 10 = -3 / 2 := rfl

/-- The arc `f_i`: on `[0, 1/2]` the segment from `b₀` to `w_i`, on `[1/2, 1]` the segment from
`w_i` to `b_∞`. Its imaginary part is `10 − 20 s`.
Source: G32 v0.16, Figure 1; polygonal paths. -/
def hg3_arc (i : Fin 13) (s : ℝ) : ℂ :=
  mr_basePoint + ((2 * min s (1 / 2) : ℝ) : ℂ) * ((hg3_waist i : ℂ) - mr_basePoint) +
    ((2 * max s (1 / 2) - 1 : ℝ) : ℂ) * (hg3_bottom - hg3_waist i)

example (i : Fin 13) : hg3_arc i 0 = mr_basePoint := by simp [hg3_arc]

example (i : Fin 13) : hg3_arc i 1 = hg3_bottom := by
  have h1 : min (1 : ℝ) (1 / 2) = 1 / 2 := by norm_num
  have h2 : max (1 : ℝ) (1 / 2) = 1 := by norm_num
  simp only [hg3_arc, h1, h2]
  push_cast
  ring

/-- The arc `f_i` as a subset of the sphere.
Source: `hg3_arc`. -/
def hg3_arcSet (i : Fin 13) : Set (OnePoint ℂ) :=
  (fun s : ℝ ↦ ((hg3_arc i s : ℂ) : OnePoint ℂ)) '' Set.Icc 0 1

example (i : Fin 13) : ((mr_basePoint : ℂ) : OnePoint ℂ) ∈ hg3_arcSet i :=
  ⟨0, ⟨le_refl 0, zero_le_one⟩, by simp [hg3_arc]⟩

/-- The real part of `f_i` at height `y`, `|y| ≤ 10`:
`-11/2 + (w_i + 11/2)(1 − |y|/10)`.
Source: `hg3_arc` (both segments are graphs over the imaginary axis). -/
def hg3_profile (i : Fin 13) (y : ℝ) : ℝ := -11 / 2 + (hg3_waist i + 11 / 2) * (1 - |y| / 10)

example (i : Fin 13) : hg3_profile i 0 = hg3_waist i := by simp [hg3_profile]; ring

/-- The fan between `f_0` and `f_12`: the quadrilateral with vertices `b₀`, `w_0`, `b_∞`,
`w_12` with its boundary, which contains every finite mark.
Source: `hg3_profile`. -/
def hg3_fan : Set ℂ :=
  {z | |z.im| ≤ 10 ∧ hg3_profile 0 z.im ≤ z.re ∧ z.re ≤ hg3_profile 12 z.im}

example : (mr_centre : ℂ) ∈ hg3_fan := by
  simp only [hg3_fan, hg3_profile, mr_centre, hg3_waist, Set.mem_ofPred_eq]
  norm_num

/-- The open sector `i` of the base decomposition: for `i < 12` the region strictly between the
arcs `f_i` and `f_{i+1}`; for `i = 12` the complement of the fan with its boundary, which contains `∞`.
Source: G32 v0.16, Figure 1 (the triangles `A_i, B_i` fill the sector between `f_i` and
`f_{i+1}` around `p_i`). -/
def hg3_sector (i : Fin 13) : Set (OnePoint ℂ) :=
  if i.val < 12 then
    ((↑) : ℂ → OnePoint ℂ) '' {z | |z.im| < 10 ∧ hg3_profile i z.im < z.re ∧
      z.re < hg3_profile (finRotate 13 i) z.im}
  else (((↑) : ℂ → OnePoint ℂ) '' hg3_fan)ᶜ

example : OnePoint.infty ∈ hg3_sector 12 := by
  simp [hg3_sector]

end HodgeLean.Foundations.Program

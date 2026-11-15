import HodgeLean.Foundations.Program.HurwitzFamily
import HodgeLean.Foundations.Program.HurwitzPrymRexCover

/-! # B6-2a: explicit local transport data

Implication from a normalized configuration to finite radial displacements on the sphere.
The cover domain and its group action remain fixed. HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.Program

/-- A common radius bounded by one quarter of every relevant separation.
Source: finite reciprocal-distance construction; `b6_chart_coordinates`. -/
def b6t_radius (b : Fin 10 → ℂ) : ℝ :=
  (4 * (1 + ∑ i : Fin 10, (‖b i‖⁻¹ + ‖b i - 1‖⁻¹ +
    ∑ j : Fin 10, if i = j then 0 else (dist (b i) (b j))⁻¹)))⁻¹

example (b : Fin 10 → ℂ) : b6t_radius b =
    (4 * (1 + ∑ i : Fin 10, (‖b i‖⁻¹ + ‖b i - 1‖⁻¹ +
      ∑ j : Fin 10, if i = j then 0 else (dist (b i) (b j))⁻¹)))⁻¹ := rfl

/-- Product of the interiors of the ten branch discs.
Source: Mathlib `Metric.ball` and the finite product topology. -/
def b6t_polydisc (b : Fin 10 → ℂ) : Set (Fin 10 → ℂ) :=
  {t | ∀ i, t i ∈ Metric.ball (b i) (b6t_radius b)}

example (b t : Fin 10 → ℂ) : t ∈ b6t_polydisc b ↔
    ∀ i, dist (t i) (b i) < b6t_radius b := Iff.rfl

/-- Radial tent displacement, summed over the disjoint supports.
Source: the tent function `max 0 (1 - dist z c / r)` and finite sums. -/
def b6t_plane (b t : Fin 10 → ℂ) (z : ℂ) : ℂ :=
  z + ∑ i : Fin 10, (max 0 (1 - dist z (b i) / b6t_radius b)) • (t i - b i)

example (b t : Fin 10 → ℂ) (z : ℂ) : b6t_plane b t z =
    z + ∑ i : Fin 10, (max 0 (1 - dist z (b i) / b6t_radius b)) • (t i - b i) := rfl

/-- Extension of the finite radial displacement fixing infinity.
Source: Mathlib `OnePoint.map`; `b6t_plane`. -/
def b6t_sphere (b t : Fin 10 → ℂ) : OnePoint ℂ → OnePoint ℂ :=
  OnePoint.map (b6t_plane b t)

example (b t : Fin 10 → ℂ) : b6t_sphere b t OnePoint.infty = OnePoint.infty := rfl

/-- The sphere punctured at all thirteen ordered marks.
Source: B4 `HurwitzPrymRexCover.exists_galoisCovering`; `b6_branch`. -/
def b6t_punctured (b : Fin 10 → ℂ) : Set (OnePoint ℂ) :=
  (Set.range (b6_branch b))ᶜ

example (b : Fin 10 → ℂ) (x : b6t_punctured b) :
    (x : OnePoint ℂ) ∉ Set.range (b6_branch b) := x.property

/-- Projection on the fixed total space after moving the sphere coordinates.
Source: composition of the B4 covering projection with `b6t_sphere`. -/
def b6t_projection (b t : Fin 10 → ℂ) {U : Type} (π : U → b6t_punctured b)
    (u : U) : OnePoint ℂ := b6t_sphere b t (π u)

example (b t : Fin 10 → ℂ) {U : Type} (π : U → b6t_punctured b) (u : U) :
    b6t_projection b t π u = b6t_sphere b t (π u) := rfl

end HodgeLean.Foundations.Program

import HodgeLean.Adapters.AutomorphyLineBundleOnXDefs
import HodgeLean.Foundations.AppellHumbertSections

/-! # Theta functions exist for positive `H`: definitions (FROZEN)

The Poincaré theta series of an Appell–Humbert datum `D`,
`P_D(v) = Σ_{l ∈ Λ} a(l, v)⁻¹` with `a = holFactor D`. Written out, with this repository's convention
(`H` conjugate-linear in the first argument), the term is
`χ(l)⁻¹ exp(-π H(l, v) - (π/2) H(l, l))`, so `P_D(v)` is the classical series
`Σ_l χ(l)⁻¹ exp(π H_BL(v, l) - (π/2) H(l, l))` of Birkenhake–Lange §3.2 evaluated at `-v`, written
without a decomposition of `Λ`. No convergence is built in: for a non-summable family `tsum` is `0`,
so statements about `poincareTheta` carry positivity of `H` as an explicit binder where it is needed.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Adapters

open HodgeLean.Foundations.AppellHumbert

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The Poincaré theta series `P_D(v) = Σ_{l ∈ Λ} a(l, v)⁻¹` of a datum `D`, `a = holFactor D`:
the average over `Λ` of the constant function `1` against the factor of automorphy.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §3.2 (the classical theta series
`Σ_l χ(l)⁻¹ exp(π H(v, l) - (π/2) H(l, l))`, here at `-v`); Weil, *Introduction à l'étude des
variétés kählériennes*, Ch. VI (theta functions as Poincaré series). -/
def poincareTheta (D : Datum (V := V)) (v : V) : ℂ :=
  ∑' l : D.lattice, (holFactor D l v)⁻¹

example (D : Datum (V := V)) (v : V) :
    poincareTheta D v = ∑' l : D.lattice, (D.semicharacter l : ℂ)⁻¹ *
      Complex.exp (-(Real.pi * D.hermitian.toFun l v + (Real.pi / 2) * D.hermitian.toFun l l)) := by
  simp only [poincareTheta, holFactor, mul_inv, Complex.exp_neg]

end HodgeLean.Adapters

import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian6Proofs
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-! # The elliptic theta equation for the witness split

The function is an explicit shifted series, independent of the desired component statements.
HC no distance; AV milestone no distance.
-/
noncomputable section
namespace HodgeLean.Adapters
/-- Shift the classical theta series so its simple zeros are the period lattice.
Source: Mumford, *Tata Lectures on Theta I*, section 1, the zero of the elliptic theta function. -/
def bh6_theta (τ z : ℂ) : ℂ := jacobiTheta₂ (z - (1 + τ) / 2) τ

example (z : ℂ) : bh6_theta Complex.I z =
    jacobiTheta₂ (z - (1 + Complex.I) / 2) Complex.I := rfl
end HodgeLean.Adapters

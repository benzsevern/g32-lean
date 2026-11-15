import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian9Proofs

/-! # First prerequisites for the stage-eight comparison gaps

This stage supplies implications from analytic factorization and chart data. The complete
singular-restriction and component-normalization compositions require further infrastructure.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Adapters

/-- An irreducible analytic equation has a directional derivative outside its principal ideal.
Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, Chapter II.B,
convergent power series and order of vanishing in characteristic zero. -/
theorem bh9_irreducible_derivative (n : ℕ) (p : Fin n → ℂ)
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
    (hirr : IsIrreducibleAt f p) :
    ∃ v : Fin n → ℂ, ¬ ∃ g : (Fin n → ℂ) → ℂ,
      AnalyticAt ℂ g p ∧
      (fun z ↦ fderiv ℂ f z v) =ᶠ[𝓝 p] (fun z ↦ f z * g z) :=
  bh9_irreducible_derivative_aux n p f hf hirr

open HodgeLean.Foundations.AnalyticDivisorAlgebraic18

example : ∃ v : Fin 2 → ℂ, ¬ ∃ g : (Fin 2 → ℂ) → ℂ,
    AnalyticAt ℂ g 0 ∧
    (fun z ↦ fderiv ℂ gaga18_axis z v) =ᶠ[𝓝 0] (fun z ↦ gaga18_axis z * g z) :=
  bh9_irreducible_derivative 2 0 gaga18_axis
    gaga18_concrete_data.1 gaga18_concrete_data.2.1

example : ∃ v : Fin 2 → ℂ, ¬ ∃ g : (Fin 2 → ℂ) → ℂ,
    AnalyticAt ℂ g 0 ∧
    (fun z ↦ fderiv ℂ gaga18_cusp z v) =ᶠ[𝓝 0] (fun z ↦ gaga18_cusp z * g z) :=
  bh9_irreducible_derivative 2 0 gaga18_cusp
    gaga18_concrete_data.2.2.2.1 gaga18_concrete_data.2.2.2.2.1

end HodgeLean.Adapters

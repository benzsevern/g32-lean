import HodgeLean.Foundations.AnalyticGermRemmertStein

/-! # Finite fibre polynomials

Actual finite fibres supply products with multiplicity for a linear observable.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
namespace HodgeLean.Foundations

/-- The characteristic polynomial of a linear observable on a finite reduced fibre.
Distinct points with the same observable value contribute separate factors.
Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, III.C,
local parametrization and elementary symmetric functions of sheets. -/
def adim9_fibrePolynomial (n : ℕ) (s : Finset (Fin n → ℂ))
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) : Polynomial ℂ :=
  ∏ z ∈ s, (Polynomial.X - Polynomial.C (ℓ z))

/-- A singleton cusp fibre at parameter 1 has observable value 1.
Source: the parametrization s ↦ (s²,s³). -/
example : adim9_fibrePolynomial 2 {![1, 1]}
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1) =
    Polynomial.X - Polynomial.C 1 := by
  classical
  simp [adim9_fibrePolynomial]

end HodgeLean.Foundations

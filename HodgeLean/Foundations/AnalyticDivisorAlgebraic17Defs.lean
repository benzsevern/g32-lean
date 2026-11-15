import HodgeLean.Foundations.AnalyticDivisorAlgebraic16

/-! # Nearby factor grouping: definitions

This file records the finite union selected by a group of local factors.  The neighbourhood and
factorization hypotheses occur in the frozen statements, not in this set-theoretic definition.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic17

open Set
open HodgeLean.Foundations.AnalyticDivisorAlgebraic16

/-- The union of the local components belonging to a finite group of factors.
Source: Chirka, *Complex Analytic Sets*, §§2.3 and 5.1 (local irreducible components). -/
def gaga17_groupedLocalComponent {n k : ℕ} {ι : Type*}
    (V : ι → Set ((Fin n → ℂ) × ℂ)) (f : ι → (Fin n → ℂ) × ℂ → ℂ)
    (i : ι) (Q : Fin k → (Fin n → ℂ) × ℂ → ℂ) : Set ((Fin n → ℂ) × ℂ) :=
  ⋃ j, gaga16_localComponent V f i (Q j)

example {n : ℕ} {ι : Type*} (V : ι → Set ((Fin n → ℂ) × ℂ))
    (f : ι → (Fin n → ℂ) × ℂ → ℂ) (i : ι)
    (Q : Fin 0 → (Fin n → ℂ) × ℂ → ℂ) :
    gaga17_groupedLocalComponent V f i Q = ∅ := by
  simp [gaga17_groupedLocalComponent]

/-- The two coordinate factors of the normal crossing equation in complex dimension two.
Source: Chirka, *Complex Analytic Sets*, §2.3 (coordinate hypersurfaces). -/
def gaga17_crossingFactors : Fin 2 → (Fin 1 → ℂ) × ℂ → ℂ :=
  ![fun y ↦ y.1 0, fun y ↦ y.2]

example (y : (Fin 1 → ℂ) × ℂ) :
    gaga17_crossingFactors 0 y * gaga17_crossingFactors 1 y = y.1 0 * y.2 := rfl

end HodgeLean.Foundations.AnalyticDivisorAlgebraic17

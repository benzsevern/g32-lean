import HodgeLean.Foundations.AnalyticDivisorAlgebraic11

/-! # Definitions for resultant and discriminant locality at nearby points

This file supplies only the coefficient polynomial at a nearby point built from a family of
coefficient representatives. Its resultant and discriminant identities are theorems in the
stage-twelve frozen specification, not definitions. HC no distance; AV milestone no distance.
-/

noncomputable section
open Filter Polynomial Topology
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic12

open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11

/-- The polynomial over germs at `p` whose coefficient in each degree of the support of `P` is the
germ at `p` of the corresponding representative. This is the polynomial `A` of the stage-eleven
statement `spec_simultaneous_representatives_translate`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1;
Bourbaki, *Algebra*, Ch. IV, §1. -/
def gaga12_polynomialAt {n : ℕ} (P : Polynomial (AnalyticGerm n))
    (a : ℕ → (Fin n → ℂ) → ℂ) (p : Fin n → ℂ) (ha : ∀ j, AnalyticAt ℂ (a j) p) :
    Polynomial (AnalyticGermAt n p) :=
  P.sum fun j _ ↦ monomial j
    ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (a j), ⟨a j, ha j, rfl⟩⟩

example {n : ℕ} (a : ℕ → (Fin n → ℂ) → ℂ) (p : Fin n → ℂ)
    (ha : ∀ j, AnalyticAt ℂ (a j) p) :
    gaga12_polynomialAt (0 : Polynomial (AnalyticGerm n)) a p ha = 0 := by
  simp [gaga12_polynomialAt]

end HodgeLean.Foundations.AnalyticDivisorAlgebraic12

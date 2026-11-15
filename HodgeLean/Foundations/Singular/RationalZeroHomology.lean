import HodgeLean.Foundations.Singular.RationalHomologyComplex
import HodgeConjecture.Lemmas.Algebra.Homology.LinearDual

/-! Homology of actual rational complexes with zero differential. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- Homology of an actual rational complex with zero differential is its actual chain group.
Source: Hatcher, Algebraic Topology, §2.1, homology of a zero differential. -/
def rationalZeroDifferentialHomologyIso (K : ChainComplex (ModuleCat ℚ) ℕ)
    (hK : ∀ i j : ℕ, K.d i j = 0) (n : ℕ) : K.homology n ≅ K.X n :=
  (CategoryTheory.ShortComplex.HomologyData.ofZeros (K.sc n) (hK _ _) (hK _ _)).left.homologyIso

#print axioms rationalZeroDifferentialHomologyIso
end HodgeLean.Foundations.Singular

import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Linear duality obtained from the actual middle cap map. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

def localTraceCap (X : TopCat.{0}) (p q : ℕ) (c : Homology ℚ X (p + q)) :
    Cohomology ℚ X p →ₗ[ℚ] Homology ℚ X q :=
  ((capCohomologyLinear ℚ X p q).comp
    (cochainCohomologyEquiv ℚ X p).symm.toLinearMap).flip c

theorem localTracePairing_bijective_of_cap (X : TopCat.{0}) (m : ℕ)
    (c : Homology ℚ X (m + m)) [FiniteDimensional ℚ (Cohomology ℚ X m)]
    (hcap : Function.Bijective (localTraceCap X m m c)) :
    Function.Bijective (localTracePairing X m m c) := by
  let A := Cohomology ℚ X m
  let e := LinearEquiv.ofBijective (localTraceCap X m m c) hcap
  let h : A ≃ₗ[ℚ] Module.Dual ℚ A := (cohomologyEquivDualHomology ℚ X m).trans e.dualMap
  let j : A ≃ₗ[ℚ] Module.Dual ℚ A := (Module.evalEquiv ℚ A).trans h.dualMap
  have hj : (localTracePairing X m m c : A → Module.Dual ℚ A) = j := by
    funext a
    ext b
    rfl
  rw [hj]
  exact j.bijective

#print axioms localTracePairing_bijective_of_cap
end HodgeLean.Foundations.QuotientDuality

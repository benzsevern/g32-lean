import HodgeLean.Foundations.Program.SchoenCycleC1LocalDenominatorDescent
import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Regularity in the original maximal affine stalks supplies a section on
the entire actual affine chart with its exact rational embedding. -/
theorem s2e_c1_affine_rational_of_maximal_stalks
    (X : Scheme) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (t : X.functionField)
    (ht : ∀ P : PrimeSpectrum Γ(X, U), P.asIdeal.IsMaximal →
      ∃ a : X.presheaf.stalk (hU.fromSpec P),
        algebraMap (X.presheaf.stalk (hU.fromSpec P)) X.functionField a = t) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = t := by
  apply s2e_c1_local_denominator_descent (X.germToFunctionField U).hom t
  intro M hM
  let P : PrimeSpectrum Γ(X, U) := ⟨M, hM.isPrime⟩
  have hx : hU.fromSpec P ∈ U := by
    change P ∈ hU.fromSpec ⁻¹ᵁ U
    rw [hU.fromSpec_preimage_self]
    trivial
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec P)) :=
    (X.presheaf.germ U (hU.fromSpec P) hx).hom.toAlgebra
  letI : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec P)) M :=
    hU.isLocalization_stalk' P hx
  obtain ⟨a, ha⟩ := ht P hM
  obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj M.primeCompl a
  refine ⟨s, s.property, b, ?_⟩
  have he := congrArg (algebraMap (X.presheaf.stalk (hU.fromSpec P)) X.functionField) hs
  change algebraMap (X.presheaf.stalk (hU.fromSpec P)) X.functionField
    (a * (X.presheaf.germ U (hU.fromSpec P) hx).hom s) =
    algebraMap (X.presheaf.stalk (hU.fromSpec P)) X.functionField
      ((X.presheaf.germ U (hU.fromSpec P) hx).hom b) at he
  rw [map_mul, ha, X.algebraMap_germ_eq_germToFunctionField,
    X.algebraMap_germ_eq_germToFunctionField] at he
  exact (mul_comm _ _).trans he

end HodgeLean.Foundations.Program

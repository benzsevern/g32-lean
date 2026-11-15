import Mathlib.RingTheory.Localization.Submodule
import HodgeLean.Adapters.NormalConeB4aGysinRegularFlat
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.AtPrime.Basic

noncomputable section
namespace HodgeLean.Adapters

/-- Regular maximal ideal parameters at a stalk of a finite module give
a principal neighborhood that is free, with the same rank as that stalk. -/
theorem a3b4a_gysin_exists_free_neighborhood_of_regular_parameters
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] (xs : List (Localization.AtPrime p))
    (hreg : RingTheory.Sequence.IsWeaklyRegular (LocalizedModule p.primeCompl M) xs)
    (hspan : Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    ∃ f : R, f ∉ p ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
      Module.finrank (Localization.Away f) (LocalizedModule.Away f M) =
        Module.finrank (Localization.AtPrime p) (LocalizedModule p.primeCompl M) := by
  letI : Module.Finite (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.Finite.of_isLocalizedModule p.primeCompl (Rₚ := Localization.AtPrime p)
      (LocalizedModule.mkLinearMap p.primeCompl M)
  letI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    a3b4a_gysin_finite_free_of_regular_parameters xs hreg hspan
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)

end HodgeLean.Adapters

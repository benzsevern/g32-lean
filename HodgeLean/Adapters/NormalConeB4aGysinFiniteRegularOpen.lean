import HodgeLean.Adapters.NormalConeB4aGysinFiniteSourceLocalization
import HodgeLean.Adapters.NormalConeB4aGysinRegularFlatOpen

noncomputable section
namespace HodgeLean.Adapters

/-- A finite model with local special fibre and regular parameters at the
source stalk has a free principal neighborhood on the base. -/
theorem a3b4a_gysin_finite_model_free_neighborhood
    {R S : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] [IsLocalRing (p.Fiber S)]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (xs : List (Localization.AtPrime p))
    (hspan : Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime q) xs →
      ∃ f : R, f ∉ p ∧ Module.Free (Localization.Away f) (LocalizedModule.Away f S) ∧
        Module.finrank (Localization.Away f) (LocalizedModule.Away f S) =
          Module.finrank (Localization.AtPrime p) (Localization.AtPrime q) := by
  letI := Localization.AtPrime.algebraOfLiesOver p q
  intro hreg
  letI : IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl)
      (Localization.AtPrime q) := a3b4a_gysin_finite_source_isLocalization p q
  letI : Module.Finite (Localization.AtPrime p) (Localization.AtPrime q) :=
    Module.Finite.of_isLocalization R S p.primeCompl
  letI : Module.Free (Localization.AtPrime p) (Localization.AtPrime q) :=
    a3b4a_gysin_finite_free_of_regular_parameters xs hreg hspan
  letI : Module.FinitePresentation R S := Module.finitePresentation_of_finite R S
  exact Module.FinitePresentation.exists_free_localizedModule_powers p.primeCompl
    (IsScalarTower.toAlgHom R S (Localization.AtPrime q)).toLinearMap (Localization.AtPrime p)

end HodgeLean.Adapters

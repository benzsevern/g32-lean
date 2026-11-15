import Mathlib.Logic.Function.Basic

/-! # Comparing functions through related surjective families -/
namespace HodgeLean.Foundations.TubularEuler

/-- Related surjective families determine a function by its values on them.
Source: `Function.Surjective.forall` and function extensionality. -/
theorem function_eq_of_related_surjective_values
    {V E I : Type*} (F G : V → E) (s t : I → V)
    (hs : Function.Surjective s) (hst : ∀ i, s i = t i)
    (h : ∀ i, F (s i) = G (t i)) : F = G :=
  funext (hs.forall.mpr (fun i => (h i).trans (congrArg G (hst i).symm)))

#print axioms function_eq_of_related_surjective_values
end HodgeLean.Foundations.TubularEuler

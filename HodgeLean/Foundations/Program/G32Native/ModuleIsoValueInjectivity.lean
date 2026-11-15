import HodgeLean.Foundations.Program.G32Native.ModuleIsoValueBoundary

/-! # Injectivity through the module evaluation boundary -/
open CategoryTheory
namespace HodgeLean.Foundations.TubularEuler

/-- Isomorphism evaluation is injective without expanding its concrete modules.
Source: `ModuleCat.Iso.toLinearEquiv` and `LinearEquiv.injective`. -/
theorem moduleIsoValue_injective {R : Type*} [Ring R] {P T : ModuleCat R}
    (e : P ≅ T) : Function.Injective (moduleIsoValue e) := e.toLinearEquiv.injective

/-- An underlying linear-equivalence equation passes through module evaluation.
Source: `moduleIsoValue_toLinearEquiv`. -/
theorem moduleIsoValue_of_linear_equation {R : Type*} [Ring R] {P T : ModuleCat R}
    (e : P ≅ T) (x : P) (y : T) (h : e.toLinearEquiv x = y) :
    moduleIsoValue e x = y := (moduleIsoValue_toLinearEquiv e x).trans h

#print axioms moduleIsoValue_injective
#print axioms moduleIsoValue_of_linear_equation
end HodgeLean.Foundations.TubularEuler

import Mathlib.Logic.Function.Basic

universe u v w
namespace HodgeLean.Foundations.Program.G32Native

/-- Transport a mapped value through source and target representatives. -/
theorem mapped_value_transport {α : Type u} {β : Type v} {δ : Type w}
    (f : α → δ) (g : β → δ) {x y : α} {a b : β} {z : δ}
    (hxy : x = y) (hfg : f y = g a) (hab : a = b) (hgz : g b = z) : f x = z :=
  (congrArg f hxy).trans (hfg.trans ((congrArg g hab).trans hgz))

#print axioms mapped_value_transport
end HodgeLean.Foundations.Program.G32Native

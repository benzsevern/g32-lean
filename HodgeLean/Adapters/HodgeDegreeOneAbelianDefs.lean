import HodgeLean.Adapters.HolomorphicFormValuesDefs

/-! # Local exact holomorphic `1`-forms

For an open `U` of `X(ℂ)` and a holomorphic function `f` on `U`, the section `df` of the sheaf of
holomorphic `1`-forms on `U`: the class of the Kähler form `d f` of `𝒪(U)`, through the
sheafification unit. Stage 4l (`HodgeDegreeOneAbelian`) glues such local sections, for local
primitives `f` of a covector `a` read through `exp : ℂ^d → X(ℂ)`, into the invariant global form
with value `a`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The section `df` of the sheaf of holomorphic `1`-forms on an open `U` of `X(ℂ)`, for a
holomorphic function `f` on `U`: the class of the Kähler form `d f` of `𝒪(U)` in upstream's
presheaf `holomorphicDeRhamPresheaf`, followed by the sheafification unit.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the differential of a
holomorphic function); upstream `holomorphicDeRhamPresheaf` and `holomorphicDeRhamSheaf`
(`HodgeConjecture/Definitions/AlgebraicGeometry/Hodge/HolomorphicDeRham.lean` at `2ead713`),
Mathlib's `Algebra.DeRham.differential`, `Algebra.DeRham.ofFunction` and `toSheafify`. -/
def localExactOneForm (U : Opens (TopCat.of (ComplexPoint X)))
    (f : OpenHolomorphicFunctions X d (op U)) :
    (holomorphicDeRhamSheaf X d 1).presheaf.obj (op U) :=
  (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d 1)).app (op U)
    (Submodule.Quotient.mk (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d (op U)) 0
      (Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions X d (op U)) f)))

example (U : Opens (TopCat.of (ComplexPoint X))) : localExactOneForm X d U 0 = 0 := by
  simp only [localExactOneForm, map_zero, Submodule.Quotient.mk_zero]
  exact map_zero _

end HodgeLean.Adapters

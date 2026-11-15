import HodgeLean.Adapters.HolomorphicOneFormsDefs

/-! # Holomorphic functions as holomorphic `0`-forms

Upstream's holomorphic `0`-forms on an open `U ⊆ X(ℂ)` are `⋀^0 Ω_{𝒪(U)/ℂ}` modulo the forms that
vanish in every chart. A holomorphic function `f ∈ 𝒪(U)` gives the `0`-form `f`; this is a map of
presheaves of abelian groups from upstream's `holomorphicFunctionPresheaf` to
`holomorphicDeRhamPresheaf X d 0`. Followed by sheafification and taken on `X(ℂ)`, it sends a
global holomorphic function to a global section of `Ω^0`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- Holomorphic functions as holomorphic `0`-forms, a map of presheaves of abelian groups on
`X(ℂ)`: on an open `U`, `f ↦` the class of the Kähler `0`-form `f`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §6 (`Ω^0 = 𝒪`); upstream
`Algebra.DeRham.ofFunction` and `holomorphicDeRhamPresheaf`
(`HodgeConjecture/Definitions/AlgebraicGeometry/Hodge/HolomorphicDeRham.lean` at `2ead713`). -/
def holomorphicFunctionsToZeroForms :
    holomorphicFunctionPresheaf X d ⋙ forget₂ CommRingCat RingCat ⋙
        forget₂ RingCat AddCommGrpCat ⟶
      holomorphicDeRhamPresheaf X d 0 where
  app U := AddCommGrpCat.ofHom
    ((chartEvaluationKernel X d U 0).mkQ.comp
      (Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions X d U))).toAddMonoidHom
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    ext f
    change Submodule.Quotient.mk (Algebra.DeRham.ofFunction ℂ _ _) =
      Submodule.Quotient.mk (formRestriction X d i 0 (Algebra.DeRham.ofFunction ℂ _ f))
    rw [formRestriction, Algebra.DeRham.map_ofFunction]
    rfl

example (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    (holomorphicFunctionsToZeroForms X d).app U 0 = 0 := map_zero _

/-- A global holomorphic function on `X(ℂ)` as a global section of the sheaf `Ω^0` of holomorphic
`0`-forms: `holomorphicFunctionsToZeroForms` followed by the sheafification unit, on `X(ℂ)`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §6; Mathlib's `toSheafify`. -/
def globalHolomorphicFunctionToZeroForm :
    (holomorphicFunctionSheaf X d).presheaf.obj (op ⊤) →+
      (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).obj (holomorphicDeRhamSheaf X d 0) :=
  ((holomorphicFunctionsToZeroForms X d ≫
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d 0)).app (op ⊤)).hom

example : globalHolomorphicFunctionToZeroForm X d 0 = 0 := map_zero _

end HodgeLean.Adapters

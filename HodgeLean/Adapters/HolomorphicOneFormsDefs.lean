import HodgeLean.Foundations.ComplexSheafSingularDefs
import HodgeLean.RealDefs.Filtration

/-! # Global holomorphic `1`-forms and their de Rham classes

Global holomorphic `1`-forms on `X(ℂ)` are global sections of upstream's sheafified
`holomorphicDeRhamSheaf X g 1`, `g = dim X.left`. A global cycle of degree `1` of `Γ(X(ℂ), F^1 Ω•)`
is such a form, and the edge map of `HodgeLean.Foundations` (`globalSectionsToHypercohomology`)
followed by upstream's `filteredToDeRhamCohomology` sends it to its class in `H_dR^1(X)`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- Global holomorphic `p`-forms on `X(ℂ)`: the global sections of upstream's sheaf of holomorphic
`p`-forms (the sheafification of the presheaf `HolomorphicForm`).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §6 (`H^0(X, Ω^p)`);
upstream `holomorphicDeRhamSheaf`
(`HodgeConjecture/Definitions/AlgebraicGeometry/Hodge/HolomorphicDeRham.lean` at `2ead713`). -/
abbrev GlobalHolomorphicForm (p : ℕ) : Type :=
  (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor (TopCat.of (ComplexPoint X))).obj
    (holomorphicDeRhamSheaf X (dim X.left) p)

example : (0 : GlobalHolomorphicForm X 1) = 0 := rfl

/-- The exterior derivative on global holomorphic `p`-forms.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §6; upstream
`holomorphicDeRhamSheafDifferential`. -/
def globalHolomorphicDifferential (p : ℕ) :
    GlobalHolomorphicForm X p →+ GlobalHolomorphicForm X (p + 1) :=
  ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))).map (holomorphicDeRhamSheafDifferential X (dim X.left) p)).hom

example (p : ℕ) : globalHolomorphicDifferential X p 0 = 0 := map_zero _

/-- Closed global holomorphic `1`-forms: the kernel of `d : Γ(Ω^1) → Γ(Ω^2)`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §6. -/
def closedGlobalHolomorphicOneForms : AddSubgroup (GlobalHolomorphicForm X 1) :=
  (globalHolomorphicDifferential X 1).ker

example : (0 : GlobalHolomorphicForm X 1) ∈ closedGlobalHolomorphicOneForms X :=
  zero_mem _

/-- The complex of global sections `Γ(X(ℂ), F^1 Ω•)`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.3; upstream
`globalSectionsComplexInt` and `hodgeFilteredDeRhamComplex`. -/
abbrev filteredGlobalSections : CochainComplex AddCommGrpCat ℤ :=
  TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) (F^1 Ω•(X))

example : filteredGlobalSections X =
    TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) (F^1 Ω•(X)) := rfl

/-- The degree-one term of `F^1 Ω•` is the sheaf of holomorphic `1`-forms.
Source: Mathlib's `HomologicalComplex.stupidTruncXIso` and `HomologicalComplex.extendXIso`. -/
def filteredDeRhamXOneIso :
    (F^1 Ω•(X)).X ((1 : ℕ) : ℤ) ≅ holomorphicDeRhamSheaf X (dim X.left) 1 :=
  HomologicalComplex.stupidTruncXIso Ω•(X) (ComplexShape.embeddingUpIntGE 1)
      (i := 0) (by simp) ≪≫
    (holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
      (i := 1) rfl

example : (filteredDeRhamXOneIso X).hom ≫ (filteredDeRhamXOneIso X).inv = 𝟙 _ :=
  Iso.hom_inv_id _

/-- The global holomorphic `1`-form of a degree-one cycle of `Γ(X(ℂ), F^1 Ω•)`.
Source: Mathlib's `HomologicalComplex.iCycles`, through `filteredDeRhamXOneIso`. -/
def cycleOneForm :
    (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ) →+ GlobalHolomorphicForm X 1 :=
  ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).map (filteredDeRhamXOneIso X).hom).hom.comp
    ((filteredGlobalSections X).iCycles ((1 : ℕ) : ℤ)).hom

example : cycleOneForm X 0 = 0 := map_zero _

/-- The de Rham class of a degree-one cycle of `Γ(X(ℂ), F^1 Ω•)`, that is of a closed global
holomorphic `1`-form: its homology class, the edge map to `ℍ^1(X(ℂ); F^1 Ω•)`, then upstream's map
to `H_dR^1(X)`. Its range lies in `F^1 H_dR^1(X)` by construction.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.3 (the edge map
`H^0(X, Ω^1) → F^1 H^1(X, ℂ)`); `globalSectionsToHypercohomology`
(`HodgeLean/Foundations/ComplexSheafSingularDefs.lean`) and upstream `filteredToDeRhamCohomology`. -/
def cycleDeRhamClass :
    (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ) →+ H_dR^((1 : ℕ) : ℤ)(X) :=
  ((filteredToDeRhamCohomology X 1 ((1 : ℕ) : ℤ)).comp
    (globalSectionsToHypercohomology X (F^1 Ω•(X)) ((1 : ℕ) : ℤ))).comp
    ((filteredGlobalSections X).homologyπ ((1 : ℕ) : ℤ)).hom

example (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) :
    cycleDeRhamClass X z ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) :=
  ⟨_, rfl⟩

end HodgeLean.Adapters

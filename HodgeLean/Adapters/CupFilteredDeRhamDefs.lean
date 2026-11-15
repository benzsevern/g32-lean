import HodgeLean.Adapters.HodgeHigherDegreeAbelian
import HodgeLean.Adapters.HolomorphicFormValues
import HodgeLean.Adapters.CupProductOf

/-! # Closed global holomorphic `p`-forms and their classes in `F^p H_dR^p`

Stage `CupFilteredDeRham` (`docs/specs/CupFilteredDeRham.md`). Stage 4c
(`HolomorphicOneFormsDefs.lean`) sent a degree-one cycle of `Γ(X(ℂ), F^1 Ω•)`, that is a closed
global holomorphic `1`-form, to its class in `F^1 H_dR^1(X)`. The same construction works in every
degree `p`: the complex `F^p Ω•` starts in degree `p` with the sheaf `Ω^p`, so a degree-`p` cycle
of `Γ(X(ℂ), F^p Ω•)` is a closed global holomorphic `p`-form, and the edge map followed by
upstream's `filteredToDeRhamCohomology` sends it to `F^p H_dR^p(X)`. For `p = 1` the definitions
below are stage 4c's, by `rfl`.

HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- Closed global holomorphic `p`-forms: the kernel of `d : Γ(Ω^p) → Γ(Ω^{p+1})`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §6; stage 4c's
`globalHolomorphicDifferential`. -/
def closedGlobalHolomorphicForms (p : ℕ) : AddSubgroup (GlobalHolomorphicForm X p) :=
  (globalHolomorphicDifferential X p).ker

/-- In degree one these are stage 4c's closed global holomorphic `1`-forms. -/
example : closedGlobalHolomorphicForms X 1 = closedGlobalHolomorphicOneForms X := rfl

/-- The complex of global sections `Γ(X(ℂ), F^p Ω•)`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.3; upstream
`globalSectionsComplexInt` and `hodgeFilteredDeRhamComplex`. -/
abbrev filteredGlobalSectionsOf (p : ℕ) : CochainComplex AddCommGrpCat ℤ :=
  TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) (F^(p : ℤ) Ω•(X))

example : filteredGlobalSectionsOf X 1 = filteredGlobalSections X := rfl

/-- The degree-`p` term of `F^p Ω•` is the sheaf of holomorphic `p`-forms.
Source: Mathlib's `HomologicalComplex.stupidTruncXIso` and `HomologicalComplex.extendXIso`. -/
def filteredDeRhamXIso (p : ℕ) :
    (F^(p : ℤ) Ω•(X)).X (p : ℤ) ≅ holomorphicDeRhamSheaf X (dim X.left) p :=
  HomologicalComplex.stupidTruncXIso Ω•(X) (ComplexShape.embeddingUpIntGE (p : ℤ))
      (i := 0) (by simp) ≪≫
    (holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
      (i := p) rfl

example (p : ℕ) : (filteredDeRhamXIso X p).hom ≫ (filteredDeRhamXIso X p).inv = 𝟙 _ :=
  Iso.hom_inv_id _

/-- The global holomorphic `p`-form of a degree-`p` cycle of `Γ(X(ℂ), F^p Ω•)`.
Source: Mathlib's `HomologicalComplex.iCycles`, through `filteredDeRhamXIso`. -/
def cycleForm (p : ℕ) :
    (filteredGlobalSectionsOf X p).cycles (p : ℤ) →+ GlobalHolomorphicForm X p :=
  ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).map (filteredDeRhamXIso X p).hom).hom.comp
    ((filteredGlobalSectionsOf X p).iCycles (p : ℤ)).hom

/-- In degree one this is stage 4c's `cycleOneForm`. -/
example : cycleForm X 1 = cycleOneForm X := rfl

/-- The de Rham class of a degree-`p` cycle of `Γ(X(ℂ), F^p Ω•)`, that is of a closed global
holomorphic `p`-form: its homology class, the edge map to `ℍ^p(X(ℂ); F^p Ω•)`, then upstream's map
to `H_dR^p(X)`. Its range lies in `F^p H_dR^p(X)` by construction.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.3 (the edge map
`H^0(X, Ω^p) → F^p H^p(X, ℂ)`); `globalSectionsToHypercohomology`
(`HodgeLean/Foundations/ComplexSheafSingularDefs.lean`) and upstream `filteredToDeRhamCohomology`. -/
def cycleFormDeRhamClass (p : ℕ) :
    (filteredGlobalSectionsOf X p).cycles (p : ℤ) →+ H_dR^(p : ℤ)(X) :=
  ((filteredToDeRhamCohomology X p (p : ℤ)).comp
    (globalSectionsToHypercohomology X (F^(p : ℤ) Ω•(X)) (p : ℤ))).comp
    ((filteredGlobalSectionsOf X p).homologyπ (p : ℤ)).hom

/-- The class of a closed global holomorphic `p`-form lies in `F^p H_dR^p(X)`. -/
example (p : ℕ) (z : (filteredGlobalSectionsOf X p).cycles (p : ℤ)) :
    cycleFormDeRhamClass X p z ∈ F^(p : ℤ) H_dR^(p : ℤ)(X) :=
  ⟨_, rfl⟩

/-- In degree one this is stage 4c's `cycleDeRhamClass`. -/
example : cycleFormDeRhamClass X 1 = cycleDeRhamClass X := rfl

end HodgeLean.Adapters

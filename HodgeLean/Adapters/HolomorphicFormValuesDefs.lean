import HodgeLean.Adapters.ExpHolomorphic

/-! # Pointwise values of holomorphic forms and their pullback along the uniformization

Upstream's holomorphic `p`-forms on an open `U ⊆ X(ℂ)` (`HolomorphicForm X d U p`) are Kähler
forms modulo the forms whose evaluation vanishes in every chart, and upstream evaluates a Kähler
form in the chart at any point `z` (`chartEvaluation`). The sheaf `Ω^p` of holomorphic `p`-forms
(`holomorphicDeRhamSheaf`) is the sheafification of that presheaf, so its sections have no
evaluation of their own.

This file gives them one. A holomorphic form on `U ∋ x` is evaluated at `x` in the chart at `x`
itself, which is compatible with restriction and so descends to the stalk of the presheaf at `x`;
sheafification does not change stalks (Mathlib's `stalkFunctor_map_unit_toSheafify_isIso`), so it
descends to the stalk of `Ω^p`. A global holomorphic `p`-form `θ` then has a value
`θ(x) : ℂ^d [⋀^p]→L ℂ` at each point, written in the chart at `x`. For `p = 1` this is a covector,
and the pullback of `θ` along `exp : ℂ^d → X(ℂ)` is `v ↦ θ(exp v) ∘ D exp(v)`, with `D exp(v)` the
manifold derivative (`mfderiv`), which is computed in the same chart at `exp v`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations
open scoped Manifold

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- A point of an open `U` lies, in the chart at itself, in upstream's coordinate domain over `U`.
Source: Mathlib's `mem_extChartAt_target` and `extChartAt_to_inv`. -/
theorem extChartAt_self_mem_chartSectionDomain (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {x : ComplexPoint X} (hx : x ∈ U.unop) :
    extChartAt 𝓘(ℂ, Fin d → ℂ) x x ∈ chartSectionDomain X d U x :=
  ⟨mem_extChartAt_target x, by
    change (extChartAt 𝓘(ℂ, Fin d → ℂ) x).symm (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) ∈
      ((U.unop : Opens (ComplexPoint X)) : Set (ComplexPoint X))
    rw [extChartAt_to_inv]
    exact hx⟩

example (x : ComplexPoint X) :
    extChartAt 𝓘(ℂ, Fin d → ℂ) x x ∈ chartSectionDomain X d (op ⊤) x :=
  extChartAt_self_mem_chartSectionDomain X d (op ⊤) trivial

/-- The value at `x ∈ U` of a holomorphic `p`-form on `U`, in the chart at `x`: upstream's
`chartEvaluation` in the chart at `x`, at the coordinate of `x`, which vanishes on the forms that
vanish in every chart.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (a holomorphic form in
local coordinates); upstream `chartEvaluationAt` and `mem_chartEvaluationKernel_iff`
(`HodgeConjecture/Definitions/AlgebraicGeometry/Hodge/AnalyticDifferentialForms.lean` at
`2ead713`). -/
def holomorphicFormValueAt (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (x : ComplexPoint X)
    (hx : x ∈ U.unop) (p : ℕ) :
    HolomorphicForm X d U p →ₗ[ℂ] (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
  (chartEvaluationKernel X d U p).liftQ
    (chartEvaluationAt X d U x p (extChartAt 𝓘(ℂ, Fin d → ℂ) x x)) (by
      intro θ hθ
      rw [LinearMap.mem_ker]
      exact (mem_chartEvaluationKernel_iff X d U p θ).1 hθ x _
        (extChartAt_self_mem_chartSectionDomain X d U hx))

example (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (x : ComplexPoint X) (hx : x ∈ U.unop)
    (p : ℕ) (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :
    holomorphicFormValueAt X d U x hx p (Submodule.Quotient.mk θ) =
      chartEvaluation X d U x p θ (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) :=
  rfl

/-- The values `holomorphicFormValueAt` at `x`, on the opens containing `x`, as a cocone: they are
compatible with restriction (upstream `chartEvaluation_formRestriction`).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2; upstream
`chartEvaluation_formRestriction`. -/
def presheafFormValueCocone (x : ComplexPoint X) (p : ℕ) :
    Cocone ((OpenNhds.inclusion x).op ⋙ holomorphicDeRhamPresheaf X d p) where
  pt := AddCommGrpCat.of ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
  ι :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        (holomorphicFormValueAt X d (op U.unop.1) x U.unop.2 p).toAddMonoidHom
      naturality := by
        intro U V i
        apply AddCommGrpCat.hom_ext
        ext s
        induction s using Submodule.Quotient.induction_on with
        | H θ =>
          change chartEvaluation X d (op V.unop.1) x p
              (formRestriction X d ((OpenNhds.inclusion x).op.map i) p θ)
                (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) =
            chartEvaluation X d (op U.unop.1) x p θ (extChartAt 𝓘(ℂ, Fin d → ℂ) x x)
          exact chartEvaluation_formRestriction X d _ x p θ
            (extChartAt_self_mem_chartSectionDomain X d (op V.unop.1) V.unop.2) }

example (x : ComplexPoint X) (p : ℕ) :
    (presheafFormValueCocone X d x p).pt = AddCommGrpCat.of ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :=
  rfl

/-- The value at `x` on the stalk at `x` of the presheaf of holomorphic `p`-forms: the cocone
`presheafFormValueCocone` descends to the colimit.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2; Mathlib's
`TopCat.Presheaf.stalk` (a colimit over the open neighbourhoods of `x`). -/
def presheafFormStalkValue (x : ComplexPoint X) (p : ℕ) :
    (holomorphicDeRhamPresheaf X d p).stalk x ⟶
      AddCommGrpCat.of ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :=
  colimit.desc _ (presheafFormValueCocone X d x p)

example (x : ComplexPoint X) (p : ℕ) (U : Opens (TopCat.of (ComplexPoint X))) (hx : x ∈ U)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p) :
    presheafFormStalkValue X d x p
        ((holomorphicDeRhamPresheaf X d p).germ U x hx (Submodule.Quotient.mk θ)) =
      chartEvaluation X d (op U) x p θ (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) := by
  change ((holomorphicDeRhamPresheaf X d p).germ U x hx ≫ presheafFormStalkValue X d x p)
    (Submodule.Quotient.mk θ) = _
  rw [TopCat.Presheaf.germ, presheafFormStalkValue]
  erw [colimit.ι_desc]
  rfl

/-- The value at `x` on the stalk at `x` of the sheaf `Ω^p` of holomorphic `p`-forms: the inverse
of the isomorphism of stalks induced by sheafification, then `presheafFormStalkValue`.
Source: Godement, *Topologie algébrique et théorie des faisceaux*, II.1.2 (a presheaf and its
sheafification have the same stalks); Mathlib's `stalkFunctor_map_unit_toSheafify_isIso`. -/
def formStalkValue (x : ComplexPoint X) (p : ℕ) :
    (holomorphicDeRhamSheaf X d p).presheaf.stalk x ⟶
      AddCommGrpCat.of ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :=
  @inv _ _ _ _ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)))
    (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf X d p)) ≫
    presheafFormStalkValue X d x p

example (x : ComplexPoint X) (p : ℕ) : formStalkValue X d x p 0 = 0 := map_zero _

/-- The value at `x` of a global holomorphic `p`-form on `X(ℂ)`, an alternating `p`-form on the
coordinate space of the chart at `x`: its germ at `x`, then `formStalkValue`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2; Mathlib's
`TopCat.Presheaf.germ`. -/
def globalFormValue (p : ℕ) (x : ComplexPoint X) :
    (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤) →+ (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
  ((holomorphicDeRhamSheaf X d p).presheaf.germ ⊤ x trivial ≫ formStalkValue X d x p).hom

example (x : ComplexPoint X) : globalFormValue X d 1 x 0 = 0 := map_zero _

example (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] (θ : GlobalHolomorphicForm Y 1)
    (x : ComplexPoint Y) : (Fin (dim Y.left) → ℂ) [⋀^Fin 1]→L[ℂ] ℂ :=
  globalFormValue Y (dim Y.left) 1 x θ

/-- The value at `x` of a global holomorphic `1`-form, as a covector on the coordinate space of
the chart at `x`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2; Mathlib's
`ContinuousAlternatingMap.ofSubsingleton` (`1`-forms are linear forms). -/
def globalOneFormCovector (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (x : ComplexPoint X) : (Fin d → ℂ) →L[ℂ] ℂ :=
  (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin d → ℂ) ℂ (0 : Fin 1)).symm
    (globalFormValue X d 1 x θ)

example (x : ComplexPoint X) (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (u : Fin d → ℂ) : globalOneFormCovector X d θ x u = globalFormValue X d 1 x θ (fun _ ↦ u) :=
  rfl

/-- The pullback of a global holomorphic `1`-form along the uniformization `exp : ℂ^d → X(ℂ)`:
`v ↦ θ(exp v) ∘ D exp(v)`, where `D exp(v) = mfderiv exp v` is the derivative of `exp` read in
the chart at `exp v`, the chart in which `θ(exp v)` is written.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (pullback of forms); Mathlib's
`mfderiv`; S12's `complexExponential` (`HodgeLean/Foundations/Uniformization.lean`). -/
def expPullback [GrpObj X] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (v : Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] ℂ :=
  (globalOneFormCovector X d θ (complexExponential X d v).toMul).comp
    (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) (fun w ↦ (complexExponential X d w).toMul) v)

example [GrpObj X] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (v u : Fin d → ℂ) :
    expPullback X d θ v u = globalOneFormCovector X d θ (complexExponential X d v).toMul
      (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) (fun w ↦ (complexExponential X d w).toMul) v u) :=
  rfl

end HodgeLean.Adapters

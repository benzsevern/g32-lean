import HodgeLean.Adapters.HolomorphicPeriodsComparisonDefs
import HodgeLean.Adapters.HolomorphicPeriodsCocycle
import HodgeLean.Adapters.HolomorphicFormValuesDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicPoincare
import Mathlib.Algebra.Homology.Double

/-! # Two-term resolutions of `ℂ` between holomorphic forms and singular cochains

Sheaves on `X(ℂ)` for smooth integral `X`, `g = dim X`: the sheaf `Ω^1_cl` of closed holomorphic
`1`-forms (the kernel of `d : Ω^1 → Ω^2`), the two-term complex `T = [Ω^0 → Ω^1_cl]` with its map
from `ℂ[0]` and its inclusion into `Ω•`, and the two-term complex `T' = [Ω^0 → Ω^0/ℂ]` (the
cokernel of the inclusion of constants) with its maps from `ℂ[0]`, to `T` and to the singular
cochain resolution `S•` of `ℂ`. In degree `0` the map `T' → S•` sends a holomorphic function to
the `0`-cochain of its values; in degree `1` it sends the class of a local primitive `f` to the
singular coboundary of the values of `f` (`σ ↦ f(σ(1)) - f(σ(0))`), which is how a closed form is
integrated along small `1`-simplices. The map `T' → S•` is defined on `T'` and not on `T`: the
comparison `T' → T` is an isomorphism only by the holomorphic Poincaré lemma, an open statement of
`HodgeLean.Adapters.HolomorphicPeriodsDeRham`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open AlgebraicTopology.Simplicial AlgebraicTopology.Singular
open HodgeLean.Foundations
open scoped Simplicial

namespace HodgeLean.Adapters

section Complexes

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The sheaf `Ω^1_cl` of closed holomorphic `1`-forms on `X(ℂ)`: the kernel of the exterior
derivative `d : Ω^1 → Ω^2` in the abelian category of sheaves of abelian groups.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3 (the sheaf of closed
forms); upstream `holomorphicDeRhamSheafDifferential`. -/
abbrev closedOneFormSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  kernel (holomorphicDeRhamSheafDifferential X (dim X.left) 1)

example : closedOneFormSheaf X = kernel (holomorphicDeRhamSheafDifferential X (dim X.left) 1) :=
  rfl

/-- `d ∘ d = 0` from `Ω^0` to `Ω^2`.
Source: upstream `holomorphicDeRhamComplex` (`d_comp_d`) and `holomorphicDeRhamComplex_d`. -/
theorem holomorphicDeRhamSheafDifferential_zero_comp_one :
    holomorphicDeRhamSheafDifferential X (dim X.left) 0 ≫
      holomorphicDeRhamSheafDifferential X (dim X.left) 1 = 0 := by
  have h := (holomorphicDeRhamComplex X (dim X.left)).d_comp_d 0 (0 + 1) (0 + 1 + 1)
  rwa [holomorphicDeRhamComplex_d, holomorphicDeRhamComplex_d] at h

example : holomorphicDeRhamSheafDifferential X (dim X.left) 0 ≫
    holomorphicDeRhamSheafDifferential X (dim X.left) 1 ≫
      holomorphicDeRhamSheafDifferential X (dim X.left) 2 = 0 := by
  rw [reassoc_of% holomorphicDeRhamSheafDifferential_zero_comp_one X, zero_comp]

/-- The exterior derivative `Ω^0 → Ω^1_cl` of holomorphic functions, a closed form.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3; Mathlib's
`CategoryTheory.Limits.kernel.lift`. -/
def closedOneFormDifferential :
    holomorphicDeRhamSheaf X (dim X.left) 0 ⟶ closedOneFormSheaf X :=
  kernel.lift _ (holomorphicDeRhamSheafDifferential X (dim X.left) 0)
    (holomorphicDeRhamSheafDifferential_zero_comp_one X)

example : closedOneFormDifferential X ≫ kernel.ι _ =
    holomorphicDeRhamSheafDifferential X (dim X.left) 0 :=
  kernel.lift_ι _ _ _

/-- Constants have exterior derivative zero, as closed forms.
Source: upstream `constantsToHolomorphicDeRhamZeroSheaf_comp_differential`. -/
theorem constantsToHolomorphicDeRhamZeroSheaf_comp_closedOneFormDifferential :
    constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫ closedOneFormDifferential X = 0 := by
  refine (cancel_mono (kernel.ι (holomorphicDeRhamSheafDifferential X (dim X.left) 1))).1 ?_
  simpa [closedOneFormDifferential] using
    constantsToHolomorphicDeRhamZeroSheaf_comp_differential X (dim X.left)

example : constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫ closedOneFormDifferential X ≫
    kernel.ι (holomorphicDeRhamSheafDifferential X (dim X.left) 1) = 0 := by
  rw [reassoc_of% constantsToHolomorphicDeRhamZeroSheaf_comp_closedOneFormDifferential X,
    zero_comp]

/-- The two-term complex `[Ω^0 → Ω^1_cl]` in degrees `0` and `1`, indexed by `ℕ`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3; Mathlib's
`HomologicalComplex.double`. -/
abbrev closedFormComplexNat :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℕ :=
  HomologicalComplex.double (closedOneFormDifferential X)
    (show (ComplexShape.up ℕ).Rel 0 1 from rfl)

example : (closedFormComplexNat X).d 0 1 =
    (HomologicalComplex.doubleXIso₀ _ _).hom ≫ closedOneFormDifferential X ≫
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv :=
  HomologicalComplex.double_d _ _ _

/-- The two-term complex `T = [Ω^0 → Ω^1_cl]`, extended by zero to integer degrees.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3; Mathlib's
`HomologicalComplex.extend` along `ComplexShape.embeddingUpNat`, as for upstream's `Ω•(X)`. -/
def closedFormComplex :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  (closedFormComplexNat X).extend ComplexShape.embeddingUpNat

example : closedFormComplex X = (closedFormComplexNat X).extend ComplexShape.embeddingUpNat := rfl

/-- The map `ℂ[0] → T`: locally constant functions as holomorphic functions in degree `0`.
Source: upstream `constantsToHolomorphicDeRhamZeroSheaf`; Mathlib's
`CochainComplex.fromSingle₀Equiv` and `HomologicalComplex.extendMap`. -/
def constantsToClosedFormComplex :
    constantComplexSheafComplexInt X ⟶ closedFormComplex X :=
  HomologicalComplex.extendMap
    ((CochainComplex.fromSingle₀Equiv _ _).symm
      ⟨constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫
          (HomologicalComplex.doubleXIso₀ _ _).inv, by
        rw [HomologicalComplex.double_d _ _ (by decide), Category.assoc, Iso.inv_hom_id_assoc,
          reassoc_of% constantsToHolomorphicDeRhamZeroSheaf_comp_closedOneFormDifferential X,
          zero_comp]⟩)
    ComplexShape.embeddingUpNat

example : constantsToClosedFormComplex X ≫ 𝟙 _ = constantsToClosedFormComplex X :=
  Category.comp_id _

/-- The inclusion `[Ω^0 → Ω^1_cl] → Ω•` of `ℕ`-indexed complexes: the identity in degree `0` and the
inclusion of closed forms in degree `1`.
Source: Mathlib's `HomologicalComplex.mkHomFromDouble` and `kernel.ι`. -/
def closedFormComplexNatToDeRham :
    closedFormComplexNat X ⟶ holomorphicDeRhamComplex X (dim X.left) :=
  HomologicalComplex.mkHomFromDouble _ (by decide) (𝟙 _) (kernel.ι _)
    (by
      change 𝟙 _ ≫ (holomorphicDeRhamComplex X (dim X.left)).d 0 (0 + 1) = _
      rw [holomorphicDeRhamComplex_d]
      exact (Category.id_comp _).trans (kernel.lift_ι _ _ _).symm)
    (by
      rintro k rfl
      change _ ≫ (holomorphicDeRhamComplex X (dim X.left)).d 1 (1 + 1) = 0
      rw [holomorphicDeRhamComplex_d]
      exact kernel.condition _)

example : closedFormComplexNatToDeRham X ≫ 𝟙 _ = closedFormComplexNatToDeRham X :=
  Category.comp_id _

/-- The inclusion `T = [Ω^0 → Ω^1_cl] → Ω•`, extended by zero to integer degrees.
Source: Mathlib's `HomologicalComplex.extendMap`; upstream `holomorphicDeRhamComplexInt`. -/
def closedFormComplexToDeRham : closedFormComplex X ⟶ Ω•(X) :=
  HomologicalComplex.extendMap (closedFormComplexNatToDeRham X) ComplexShape.embeddingUpNat

example : closedFormComplexToDeRham X =
    HomologicalComplex.extendMap (closedFormComplexNatToDeRham X) ComplexShape.embeddingUpNat :=
  rfl

/-- The sheaf `Ω^0/ℂ`: the cokernel of the inclusion of locally constant functions into
holomorphic functions. Its sections are local primitives modulo locally constant functions.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3; upstream
`constantsToHolomorphicDeRhamZeroSheaf`; Mathlib's `CategoryTheory.Limits.cokernel`. -/
abbrev primitiveQuotientSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  cokernel (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))

example : primitiveQuotientSheaf X = cokernel (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) :=
  rfl

/-- The two-term complex `[Ω^0 → Ω^0/ℂ]` in degrees `0` and `1`, indexed by `ℕ`.
Source: Mathlib's `HomologicalComplex.double` and `cokernel.π`. -/
abbrev primitiveComplexNat :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℕ :=
  HomologicalComplex.double (cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)))
    (show (ComplexShape.up ℕ).Rel 0 1 from rfl)

example : (primitiveComplexNat X).d 0 1 =
    (HomologicalComplex.doubleXIso₀ _ _).hom ≫ cokernel.π _ ≫
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv :=
  HomologicalComplex.double_d _ _ _

/-- The two-term complex `T' = [Ω^0 → Ω^0/ℂ]`, extended by zero to integer degrees.
Source: Mathlib's `HomologicalComplex.extend` along `ComplexShape.embeddingUpNat`. -/
def primitiveComplex :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  (primitiveComplexNat X).extend ComplexShape.embeddingUpNat

example : primitiveComplex X = (primitiveComplexNat X).extend ComplexShape.embeddingUpNat := rfl

/-- The map `ℂ[0] → T'`: locally constant functions as holomorphic functions in degree `0`.
Source: upstream `constantsToHolomorphicDeRhamZeroSheaf`; Mathlib's `cokernel.condition`. -/
def constantsToPrimitiveComplex :
    constantComplexSheafComplexInt X ⟶ primitiveComplex X :=
  HomologicalComplex.extendMap
    ((CochainComplex.fromSingle₀Equiv _ _).symm
      ⟨constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫
          (HomologicalComplex.doubleXIso₀ _ _).inv, by
        rw [HomologicalComplex.double_d _ _ (by decide), Category.assoc, Iso.inv_hom_id_assoc,
          cokernel.condition_assoc, zero_comp]⟩)
    ComplexShape.embeddingUpNat

example : constantsToPrimitiveComplex X ≫ 𝟙 _ = constantsToPrimitiveComplex X :=
  Category.comp_id _

/-- The exterior derivative on `Ω^0/ℂ`, with values in closed forms: `[f] ↦ df`, well defined
because constants have derivative zero.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3; Mathlib's
`cokernel.desc`. -/
def primitiveQuotientToClosedOneForm : primitiveQuotientSheaf X ⟶ closedOneFormSheaf X :=
  cokernel.desc _ (closedOneFormDifferential X)
    (constantsToHolomorphicDeRhamZeroSheaf_comp_closedOneFormDifferential X)

example : cokernel.π _ ≫ primitiveQuotientToClosedOneForm X = closedOneFormDifferential X :=
  cokernel.π_desc _ _ _

/-- The comparison `[Ω^0 → Ω^0/ℂ] → [Ω^0 → Ω^1_cl]` of `ℕ`-indexed complexes: the identity in
degree `0` and `[f] ↦ df` in degree `1`.
Source: Mathlib's `HomologicalComplex.mkHomFromDouble`. -/
def primitiveComplexNatToClosedFormComplexNat : primitiveComplexNat X ⟶ closedFormComplexNat X :=
  HomologicalComplex.mkHomFromDouble _ (by decide) (HomologicalComplex.doubleXIso₀ _ _).inv
    (primitiveQuotientToClosedOneForm X ≫ (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv)
    (by
      change _ ≫ HomologicalComplex.d _ 0 1 = _
      rw [HomologicalComplex.double_d _ _ (by decide), Iso.inv_hom_id_assoc,
        primitiveQuotientToClosedOneForm, cokernel.π_desc_assoc])
    (by
      intro k _
      rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by decide), comp_zero])

example : primitiveComplexNatToClosedFormComplexNat X ≫ 𝟙 _ =
    primitiveComplexNatToClosedFormComplexNat X :=
  Category.comp_id _

/-- The comparison `T' = [Ω^0 → Ω^0/ℂ] → T = [Ω^0 → Ω^1_cl]`, extended by zero to integer degrees.
Source: Mathlib's `HomologicalComplex.extendMap`. -/
def primitiveComplexToClosedFormComplex : primitiveComplex X ⟶ closedFormComplex X :=
  HomologicalComplex.extendMap (primitiveComplexNatToClosedFormComplexNat X)
    ComplexShape.embeddingUpNat

example : primitiveComplexToClosedFormComplex X = HomologicalComplex.extendMap
    (primitiveComplexNatToClosedFormComplexNat X) ComplexShape.embeddingUpNat :=
  rfl

end Complexes

section Integration

/-- Two singular cochains that agree on every simplex are equal.
Source: Mathlib's `SSet.chainComplex_hom_ext` (chains are free on simplices). -/
theorem cochain_ext_chainOfSimplex {R : Type} [CommRing R] {Y : SSet.{0}} {n : ℕ}
    (φ ψ : Cochain R Y n) (h : ∀ σ : Y _⦋n⦌, φ (chainOfSimplex R σ) = ψ (chainOfSimplex R σ)) :
    φ = ψ := by
  have hc : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hi : (Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a = a • chainOfSimplex R σ := by
      rw [chainOfSimplex, ← map_smul]
      simp
    change φ ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a) =
      ψ ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hc

example {R : Type} [CommRing R] {Y : SSet.{0}} {n : ℕ} (φ : Cochain R Y n) : φ = φ :=
  cochain_ext_chainOfSimplex φ φ fun _ ↦ rfl

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The value at `x ∈ U` of a holomorphic function on `U` (a holomorphic `0`-form): stage 4f's
`holomorphicFormValueAt` in degree `0`, an alternating `0`-form, read at the empty tuple.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2; stage 4f
`holomorphicFormValueAt`. -/
def holomorphicFunctionValue (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (x : ComplexPoint X)
    (hx : x ∈ U.unop) : HolomorphicForm X (dim X.left) U 0 →ₗ[ℂ] ℂ where
  toFun F := holomorphicFormValueAt X (dim X.left) U x hx 0 F 0
  map_add' F G := by simp
  map_smul' c F := by simp

example (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (x : ComplexPoint X) (hx : x ∈ U.unop) :
    holomorphicFunctionValue X U x hx 0 = 0 :=
  map_zero _

open scoped Manifold in
/-- The value of a holomorphic function does not change under restriction.
Source: upstream `chartEvaluation_formRestriction`. -/
theorem holomorphicFunctionValue_restriction {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    (i : U ⟶ V) (x : ComplexPoint X) (hx : x ∈ V.unop) (F : HolomorphicForm X (dim X.left) U 0) :
    holomorphicFunctionValue X V x hx (holomorphicFormRestriction X (dim X.left) i 0 F) =
      holomorphicFunctionValue X U x (leOfHom i.unop hx) F := by
  induction F using Submodule.Quotient.induction_on with
  | H θ =>
    change chartEvaluation X (dim X.left) V x 0 (formRestriction X (dim X.left) i 0 θ)
        (extChartAt 𝓘(ℂ, Fin (dim X.left) → ℂ) x x) 0 =
      chartEvaluation X (dim X.left) U x 0 θ (extChartAt 𝓘(ℂ, Fin (dim X.left) → ℂ) x x) 0
    rw [chartEvaluation_formRestriction X (dim X.left) i x 0 θ
      (extChartAt_self_mem_chartSectionDomain X (dim X.left) V hx)]

example (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (x : ComplexPoint X) (hx : x ∈ U.unop)
    (F : HolomorphicForm X (dim X.left) U 0) :
    holomorphicFunctionValue X U x hx (holomorphicFormRestriction X (dim X.left) (𝟙 U) 0 F) =
      holomorphicFunctionValue X U x hx F :=
  holomorphicFunctionValue_restriction X (𝟙 U) x hx F

open scoped Manifold in
/-- A constant function has its constant as value.
Source: upstream `chartEvaluation_ofConstant`. -/
theorem holomorphicFunctionValue_ofConstant (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hx : x ∈ U.unop) (c : ℂ) :
    holomorphicFunctionValue X U x hx (holomorphicFormOfConstant X (dim X.left) U c) = c := by
  change chartEvaluation X (dim X.left) U x 0 (Algebra.DeRham.ofConstant ℂ _ c)
      (extChartAt 𝓘(ℂ, Fin (dim X.left) → ℂ) x x) 0 = c
  rw [chartEvaluation_ofConstant X (dim X.left) U x c
    (extChartAt_self_mem_chartSectionDomain X (dim X.left) U hx)]
  rfl

example (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (x : ComplexPoint X) (hx : x ∈ U.unop) :
    holomorphicFunctionValue X U x hx (holomorphicFormOfConstant X (dim X.left) U 1) = 1 :=
  holomorphicFunctionValue_ofConstant X U x hx 1

/-- The singular `0`-cochain of values of a holomorphic function `F` on an open `U`: a singular
`0`-simplex of `U` is a point `x` of `U`, sent to `F(x)`.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15 (the de Rham map in degree `0`);
stage 4i `simplexCochain`; Mathlib's `TopCat.toSSetObj₀Equiv`. -/
def functionValueCochain (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    HolomorphicForm X (dim X.left) U 0 →+
      OpenCochains ℂ (TopCat.of (ComplexPoint X)) U 0 where
  toFun F := simplexCochain ℂ _ 0 fun σ ↦
    holomorphicFunctionValue X U (TopCat.toSSetObj₀Equiv σ).1 (TopCat.toSSetObj₀Equiv σ).2 F
  map_zero' := cochain_ext_chainOfSimplex _ _ fun σ ↦ by
    rw [spec_simplexCochain_chainOfSimplex, map_zero]
    rfl
  map_add' F G := cochain_ext_chainOfSimplex _ _ fun σ ↦ by
    erw [LinearMap.add_apply, spec_simplexCochain_chainOfSimplex, spec_simplexCochain_chainOfSimplex,
      spec_simplexCochain_chainOfSimplex]
    exact map_add _ F G

example (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) : functionValueCochain X U 0 = 0 := map_zero _

/-- The values of holomorphic functions, as a morphism from the presheaf of holomorphic `0`-forms to
the presheaf of singular `0`-cochains: compatible with restriction because values are.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15; upstream
`singularCochainPresheaf`. -/
def functionValuePresheafMap :
    holomorphicDeRhamPresheaf X (dim X.left) 0 ⟶
      singularCochainPresheaf ℂ (TopCat.of (ComplexPoint X)) 0 where
  app U := AddCommGrpCat.ofHom (functionValueCochain X U)
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    ext F : 1
    refine cochain_ext_chainOfSimplex _ _ fun σ ↦ ?_
    change functionValueCochain X V (holomorphicFormRestriction X (dim X.left) i 0 F)
        (chainOfSimplex ℂ σ) =
      functionValueCochain X U F
        (((SSet.chainComplexMap (TopCat.toSSet.map ((Opens.toTopCat _).map i.unop))
          (ModuleCat.of ℂ ℂ)).f 0).hom (chainOfSimplex ℂ σ))
    rw [chainOfSimplex_map]
    change simplexCochain ℂ _ 0 _ (chainOfSimplex ℂ σ) = simplexCochain ℂ _ 0 _ (chainOfSimplex ℂ _)
    rw [spec_simplexCochain_chainOfSimplex, spec_simplexCochain_chainOfSimplex]
    exact holomorphicFunctionValue_restriction X i _ _ F

example : functionValuePresheafMap X ≫ 𝟙 _ = functionValuePresheafMap X := Category.comp_id _

/-- The degree-`0` integration map `Ω^0 → S^0` of sheaves: the sheafification of
`functionValuePresheafMap`.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15; upstream
`singularCochainSheaf` and `holomorphicDeRhamSheaf` (both sheafifications). -/
def functionValueSheafMap :
    holomorphicDeRhamSheaf X (dim X.left) 0 ⟶
      singularCochainSheaf ℂ (TopCat.of (ComplexPoint X)) 0 :=
  (presheafToSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat).map
    (functionValuePresheafMap X)

example : functionValueSheafMap X ≫ 𝟙 _ = functionValueSheafMap X := Category.comp_id _

/-- Constants, viewed as holomorphic functions and then through their values, are the constant
`0`-cochains of upstream's resolution.
Source: upstream `chartEvaluation_ofConstant` and `constantsToSingularCochainZero`. -/
theorem constantsToHolomorphicDeRhamZeroSheaf_comp_functionValueSheafMap :
    constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫ functionValueSheafMap X =
      constantsToSingularCochainZeroSheaf ℂ (TopCat.of (ComplexPoint X)) := by
  have h : constantsToHolomorphicDeRhamZero X (dim X.left) ≫ functionValuePresheafMap X =
      constantsToSingularCochainZero ℂ (TopCat.of (ComplexPoint X)) := by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    ext c : 1
    change ℂ at c
    refine cochain_ext_chainOfSimplex _ _ fun σ ↦ ?_
    change simplexCochain ℂ _ 0 _ (chainOfSimplex ℂ σ) =
      c * (openZeroAugmentation ℂ (TopCat.of (ComplexPoint X)) U).hom (chainOfSimplex ℂ σ)
    rw [spec_simplexCochain_chainOfSimplex]
    change holomorphicFunctionValue X U _ _ (holomorphicFormOfConstant X (dim X.left) U c) = _
    rw [holomorphicFunctionValue_ofConstant]
    have h1 := ConcreteCategory.congr_hom (ιChainComplex_comp_simplicialZeroAugmentation ℂ
      (TopCat.toSSet.obj ((Opens.toTopCat (TopCat.of (ComplexPoint X))).obj U.unop)) σ) 1
    change (openZeroAugmentation ℂ (TopCat.of (ComplexPoint X)) U).hom (chainOfSimplex ℂ σ) = 1
      at h1
    rw [h1, mul_one]
  change (presheafToSheaf _ _).map _ ≫ (presheafToSheaf _ _).map _ = (presheafToSheaf _ _).map _
  rw [← Functor.map_comp, h]

example : constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫ functionValueSheafMap X ≫
    singularCochainSheafCoboundary ℂ (TopCat.of (ComplexPoint X)) 0 = 0 := by
  rw [reassoc_of% constantsToHolomorphicDeRhamZeroSheaf_comp_functionValueSheafMap X,
    constantsToSingularCochainZeroSheaf_comp_coboundary]

/-- The degree-`1` integration map `Ω^0/ℂ → S^1`: the class of a local primitive `f` goes to the
singular coboundary of the values of `f`, the cochain `σ ↦ f(σ(1)) - f(σ(0))` on small
`1`-simplices; well defined because constants have zero coboundary.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15 (integration along small
simplices through local primitives); upstream `constantsToSingularCochainZeroSheaf_comp_coboundary`;
Mathlib's `cokernel.desc`. -/
def primitiveQuotientToSingular :
    primitiveQuotientSheaf X ⟶ singularCochainSheaf ℂ (TopCat.of (ComplexPoint X)) 1 :=
  cokernel.desc _ (functionValueSheafMap X ≫ singularCochainSheafCoboundary ℂ _ 0) (by
    rw [reassoc_of% constantsToHolomorphicDeRhamZeroSheaf_comp_functionValueSheafMap X,
      constantsToSingularCochainZeroSheaf_comp_coboundary])

example : cokernel.π _ ≫ primitiveQuotientToSingular X =
    functionValueSheafMap X ≫ singularCochainSheafCoboundary ℂ _ 0 :=
  cokernel.π_desc _ _ _

/-- The integration map `[Ω^0 → Ω^0/ℂ] → S•` of `ℕ`-indexed complexes.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15; Mathlib's
`HomologicalComplex.mkHomFromDouble`. -/
def primitiveComplexNatToSingular :
    primitiveComplexNat X ⟶ singularCochainSheafComplex ℂ (TopCat.of (ComplexPoint X)) :=
  HomologicalComplex.mkHomFromDouble _ (by decide) (functionValueSheafMap X)
    (primitiveQuotientToSingular X)
    (by
      change _ ≫ (singularCochainSheafComplex ℂ _).d 0 (0 + 1) = _
      rw [singularCochainSheafComplex_d]
      exact (cokernel.π_desc _ _ _).symm)
    (by
      rintro k rfl
      change _ ≫ (singularCochainSheafComplex ℂ _).d 1 (1 + 1) = 0
      rw [singularCochainSheafComplex_d, ← cancel_epi (cokernel.π _), comp_zero]
      have h := (singularCochainSheafComplex ℂ (TopCat.of (ComplexPoint X))).d_comp_d 0 (0 + 1)
        (0 + 1 + 1)
      rw [singularCochainSheafComplex_d, singularCochainSheafComplex_d] at h
      erw [cokernel.π_desc_assoc, Category.assoc, h, comp_zero])

example : primitiveComplexNatToSingular X ≫ 𝟙 _ = primitiveComplexNatToSingular X :=
  Category.comp_id _

/-- The integration map `T' = [Ω^0 → Ω^0/ℂ] → S•` to upstream's singular cochain resolution of the
constant sheaf `ℂ`, extended by zero to integer degrees.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15; upstream
`singularCochainSheafComplexInt`; Mathlib's `HomologicalComplex.extendMap`. -/
def primitiveComplexToSingular : primitiveComplex X ⟶ singularCochainSheafComplexInt X ℂ :=
  HomologicalComplex.extendMap (primitiveComplexNatToSingular X) ComplexShape.embeddingUpNat

example : primitiveComplexToSingular X =
    HomologicalComplex.extendMap (primitiveComplexNatToSingular X) ComplexShape.embeddingUpNat :=
  rfl

/-- The global section of the singular cochain sheaf `S^n` of a singular `n`-cochain of `X(ℂ)`:
the cochain on the top open (`singularCochainComplexIsoTopOpen`), then upstream's comparison of raw
cochains with global sections of the sheafification, the first legs of stage 3c's
`singularToFieldCohomology`.
Source: upstream `topOpenToGlobalSingularCochainSheafComplex` and
`singularCochainComplexIsoTopOpen`. -/
def globalCochainSection (n : ℕ) :
    Cochain ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) n →+
      (globalSingularCochainSheafComplex ℂ (TopCat.of (ComplexPoint X))).X n :=
  ((topOpenToGlobalSingularCochainSheafComplex ℂ (TopCat.of (ComplexPoint X))).f n).hom.comp
    ((singularCochainComplexIsoTopOpen ℂ (TopCat.of (ComplexPoint X))).hom.f n).hom.toAddMonoidHom

example (n : ℕ) : globalCochainSection X n 0 = 0 := map_zero _

end Integration

end HodgeLean.Adapters

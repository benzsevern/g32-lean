import HodgeLean.Adapters.CupFilteredDeRham

/-! # Wedge with a global holomorphic `1`-form: the predicates and the hypercohomology shift

Stage `WedgeThetaComplex` (`docs/specs/WedgeThetaComplex.md`), stages 2 and 3 of the `hL` track
of `docs/specs/CupFilteredDeRham.md`. A global holomorphic `1`-form `θ` on `X(ℂ)` acts on
holomorphic forms by `ω ↦ θ ∧ ω`. The sheaves `Ω^p` are sheafifications, so this file does not
construct that action: it defines what it means for a morphism of sheaves `Ω^n ⟶ Ω^{n+1}`, or a
morphism of complexes `Ω• ⟶ Ω•[1]`, to be the wedge with `θ`, through pointwise values
(`formStalkValue`). Values determine sections, so at most one morphism has this property; the
frozen file states that one exists.

It also defines the shift map `ℍ^k(X(ℂ); K[1]) → ℍ^{k+1}(X(ℂ); K)` (composition with the identity
of `K[1]`, read as a degree-one shifted morphism `K[1] ⟶ K`), as upstream's
`HypercohomologyShift.lean` uses it.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations

namespace HodgeLean.Adapters

/-- The wedge `a ∧ α` of a covector `a` with an alternating `n`-form `α` on `ℂ^d`:
`(a ∧ α)(v_0, …, v_n) = ∑ᵢ (-1)^i a(v_i) α(v_0, …, v̂_i, …, v_n)`. For `α` a wedge of covectors
this is upstream's `wedgeCovectors` with `a` put first (Laplace expansion along the first row).
Source: Bourbaki, *Algèbre*, Ch. III §11 (the exterior product of alternating forms); Mathlib's
`ContinuousAlternatingMap.alternatizeUncurryFin`, the convention of cupf1's
`laneB_chartEvaluationHolo_ι_mul`. -/
def covectorWedgeForm {d n : ℕ} (a : (Fin d → ℂ) →L[ℂ] ℂ)
    (α : (Fin d → ℂ) [⋀^Fin n]→L[ℂ] ℂ) : (Fin d → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ :=
  ContinuousAlternatingMap.alternatizeUncurryFin (a.smulRight α)

/-- The wedge with the zero covector is zero. -/
example {d n : ℕ} (α : (Fin d → ℂ) [⋀^Fin n]→L[ℂ] ℂ) :
    covectorWedgeForm (0 : (Fin d → ℂ) →L[ℂ] ℂ) α = 0 := by
  ext v
  simp [covectorWedgeForm, ContinuousAlternatingMap.alternatizeUncurryFin_apply]

/-- On a wedge of covectors it is upstream's `wedgeCovectors` with `a` put first. -/
example {d n : ℕ} (a : (Fin d → ℂ) →L[ℂ] ℂ) (L : Fin n → (Fin d → ℂ) →L[ℂ] ℂ) :
    covectorWedgeForm a (ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) L) =
      ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) (Fin.cons a L) := by
  rw [ContinuousAlternatingMap.wedgeCovectors_succ]
  rfl

section Sheaf

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- A morphism of sheaves `w : Ω^n ⟶ Ω^{n+1}` on `X(ℂ)` is the wedge with the global holomorphic
`1`-form `θ` if, for every open `U`, every `x ∈ U` and every section `s` of `Ω^n` on `U`, the value
of `w s` at `x` is `θ(x) ∧ s(x)`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the exterior product of
holomorphic forms is computed pointwise); `formStalkValue`, `globalOneFormCovector`. -/
def IsWedgeBy (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (n : ℕ)
    (w : holomorphicDeRhamSheaf X d n ⟶ holomorphicDeRhamSheaf X d (n + 1)) : Prop :=
  ∀ (U : Opens (TopCat.of (ComplexPoint X))) (x : ComplexPoint X) (hx : x ∈ U)
    (s : (holomorphicDeRhamSheaf X d n).presheaf.obj (op U)),
    formStalkValue X d x (n + 1)
        ((holomorphicDeRhamSheaf X d (n + 1)).presheaf.germ U x hx (w.hom.app (op U) s)) =
      covectorWedgeForm (globalOneFormCovector X d θ x)
        (formStalkValue X d x n ((holomorphicDeRhamSheaf X d n).presheaf.germ U x hx s))

/-- The zero morphism is the wedge with the zero form, once values are additive. -/
example (n : ℕ) (U : Opens (TopCat.of (ComplexPoint X))) (x : ComplexPoint X) (hx : x ∈ U) :
    formStalkValue X d x (n + 1)
        ((holomorphicDeRhamSheaf X d (n + 1)).presheaf.germ U x hx
          ((0 : holomorphicDeRhamSheaf X d n ⟶ holomorphicDeRhamSheaf X d (n + 1)).hom.app
            (op U) 0)) = 0 := by
  simp

end Sheaf

section Complex

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The degree-`n` term of `Ω•(X)` is the sheaf `Ω^n` of holomorphic `n`-forms.
Source: Mathlib's `HomologicalComplex.extendXIso`; upstream `holomorphicDeRhamComplexInt`. -/
def wedgeThetaXIso (n : ℕ) :
    Ω•(X).X (n : ℤ) ≅ holomorphicDeRhamSheaf X (dim X.left) n :=
  (holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat (i := n) rfl

example (n : ℕ) : (wedgeThetaXIso X n).inv ≫ (wedgeThetaXIso X n).hom = 𝟙 _ :=
  Iso.inv_hom_id _

/-- The degree-`n` term of `Ω•(X)[1]` is the sheaf `Ω^{n+1}`: Mathlib's `(K⟦1⟧).X n = K.X (n+1)`.
Source: Mathlib's `CochainComplex.shiftFunctorObjXIso` and `HomologicalComplex.extendXIso`. -/
def wedgeThetaShiftXIso (n : ℕ) :
    (Ω•(X)⟦(1 : ℤ)⟧).X (n : ℤ) ≅ holomorphicDeRhamSheaf X (dim X.left) (n + 1) :=
  Ω•(X).shiftFunctorObjXIso 1 (n : ℤ) ((n : ℤ) + 1) rfl ≪≫
    (holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
      (i := n + 1) (by simp)

example (n : ℕ) : (wedgeThetaShiftXIso X n).inv ≫ (wedgeThetaShiftXIso X n).hom = 𝟙 _ :=
  Iso.inv_hom_id _

/-- The degree-`n` component `Ω^n ⟶ Ω^{n+1}` of a morphism of complexes `Ω•(X) ⟶ Ω•(X)[1]`.
Source: Mathlib's `HomologicalComplex.Hom.f`, through `wedgeThetaXIso` and `wedgeThetaShiftXIso`. -/
def wedgeThetaComponent (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (n : ℕ) :
    holomorphicDeRhamSheaf X (dim X.left) n ⟶ holomorphicDeRhamSheaf X (dim X.left) (n + 1) :=
  (wedgeThetaXIso X n).inv ≫ L.f (n : ℤ) ≫ (wedgeThetaShiftXIso X n).hom

example (n : ℕ) : wedgeThetaComponent X 0 n = 0 := by
  simp [wedgeThetaComponent]

/-- A morphism of complexes `L : Ω•(X) ⟶ Ω•(X)[1]` is the wedge with the global holomorphic
`1`-form `θ` if each component `Ω^n ⟶ Ω^{n+1}`, `n ≥ 0`, is (`IsWedgeBy`). In negative degrees
`Ω•(X)` is zero. Being a morphism to `Ω•(X)[1]` means commuting with Mathlib's shifted
differential `(K⟦1⟧).d n (n+1) = -K.d (n+1) (n+2)`, that is `d(θ ∧ ω) = -θ ∧ dω`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§8.1 (morphisms of complexes of sheaves); `IsWedgeBy`, `wedgeThetaComponent`. -/
def IsWedgeThetaHom (θ : GlobalHolomorphicForm X 1) (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) : Prop :=
  ∀ n : ℕ, IsWedgeBy X (dim X.left) θ n (wedgeThetaComponent X L n)

example (θ : GlobalHolomorphicForm X 1) (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧)
    (h : IsWedgeThetaHom X θ L) : IsWedgeBy X (dim X.left) θ 0 (wedgeThetaComponent X L 0) :=
  h 0

end Complex

section Shift

variable (X : Over (Spec ↧ℂ))

local instance wedgeThetaHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- The shift map `ℍ^k(X(ℂ); K[1]) → ℍ^{k+1}(X(ℂ); K)`: composition with the identity of `K[1]`,
read as a degree-one shifted morphism `K[1] ⟶ K` (upstream's "right unshift"). In the derived
category it is the canonical isomorphism `Hom(ℤ, K[1][k]) ≅ Hom(ℤ, K[k+1])`.
Source: Kashiwara–Schapira, *Sheaves on Manifolds*, Grundlehren 292, §1.3 (shifts of complexes);
Mathlib's `Localization.SmallShiftedHom.comp`; upstream
`hypercohomologyAddEquivGlobalSectionsKInjective_rightUnshift`
(`Other/AlgebraicGeometry/Cohomology/HypercohomologyShift.lean` at `2ead713`). -/
def hypercohomologyShift (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (k : ℤ) :
    ℍ^k(X; K⟦(1 : ℤ)⟧) →+ ℍ^(k + 1)(X; K) where
  toFun α := α.comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
      (show ShiftedHom (K⟦(1 : ℤ)⟧) K (1 : ℤ) from 𝟙 _)) (add_comm 1 k)
  map_zero' := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_zero, ShiftedHom.zero_comp]
  map_add' α β := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_add, ShiftedHom.add_comp]

example (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (k : ℤ) :
    hypercohomologyShift X K k 0 = 0 :=
  map_zero _

end Shift

end HodgeLean.Adapters

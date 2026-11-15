import HodgeLean.Adapters.ResolutionClassActionProofs

/-! # Degree-one endomorphisms of resolutions act by a class: frozen specification

Stage hl3 of the `hL` track, comparison stage 1 (`docs/specs/ResolutionClassAction.md`). The de
Rham complex `Ω•` and the sheafified singular cochains `S•` both resolve the constant sheaf
`ℂ[0]`, through upstream's quasi-isomorphisms `q_Ω = constantsToHolomorphicDeRhamComplexInt` and
`q_S = constantsToSingularCochainComplexInt`. A morphism of complexes `L : K ⟶ K⟦1⟧` on a complex
`K` with a quasi-isomorphism `q : A ⟶ K` defines the class
`e_L = Q(q)⁻¹[1] ∘ Q(L) ∘ Q(q) : A ⟶ A[1]` in the derived category (`resolutionClass`,
`HodgeLean.Adapters.ResolutionClassActionDefs`).

Claimed:
* the transport, for every `X`, every quasi-isomorphism `q : A ⟶ K` and every `L : K ⟶ K⟦1⟧`:
  `e_L` satisfies `Q(q)[1] ∘ e_L = Q(L) ∘ Q(q)` and is the only degree-one morphism that does; the
  action of `L` on hypercohomology (composition with `L` as a degree-one shifted morphism, the
  form of hl1's statement 11 and hl2's `cupLeftHypercohomology`), transported along the bijection
  `ℍ(q)`, is composition with `e_L`;
* naturality in `L`: `e_{L+L'} = e_L + e_{L'}`, `e_0 = 0` (in the derived category), and `e_L`
  depends only on `Q(L)`;
* de Rham side, for smooth integral `X` and a morphism `L` that is the wedge with a global
  holomorphic `1`-form `θ` (hl1's `IsWedgeThetaHom`): the degree-`0` component of `L ∘ q_Ω` sends
  the constant `c` to the global form with values `c θ(x)`; and the class of the unit
  `ℤ[0] ⟶ ℂ[0]` composed with `e_L`, sent to `ℍ^1(Ω•)` by `ℍ(q_Ω)`, is the de Rham class of `θ`
  (`cycleDeRhamClass`), for `θ` the form of a cycle;
* singular side: on presheaf sections, left cup with a `1`-cochain `a` sends the constant
  `0`-cochain `r` to `r a` (any space, any commutative ring); for every `X` and every commutative
  ring `K`, the unit class composed with `C_a` is the image of `[a]` under hl2's
  `singularToSheafHypercohomology`; and for smooth integral `X`, the unit class composed with
  `e_{C_a}`, sent to `ℍ^1(S•)` by `ℍ(q_S)`, is the same class.

Not claimed: the comparison `e_{L_θ} = e_{C_{a_θ}}` for the integration cocycle `a_θ` of `θ` on
abelian `X` (the first item of the next stage, recorded in the spec doc); the identification of
`Hom_D(ℂ[0], ℂ[0][1])` with `H^1(X(ℂ); ℂ)`, which is false in the derived category of sheaves of
abelian groups (precomposition with the unit `ℤ[0] ⟶ ℂ[0]` is not injective there, see the spec
doc); the transport of the singular cup to `cupProductOf X` and `bettiDeRhamHQ`; the binder `hL`.
No statement assumes `BettiDeRhamIso` or `HodgeDecomposition`, and none adds a hypothesis. It is an
implication from no geometric input: the formal statements hold for every `X`, the de Rham
statements for every smooth integral `X`, the singular statements for every `X` (every smooth
integral `X` where `e_{C_a}` needs `q_S` to be a quasi-isomorphism).
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Simplicial
open AlgebraicGeometry ComplexPoint Opposite
open HodgeLean.Foundations

namespace HodgeLean.Adapters

local instance resolutionClassHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- **The defining property of `e_L`.** For a quasi-isomorphism `q : A ⟶ K` and a morphism of
complexes `L : K ⟶ K⟦1⟧`, `Q(q)[1] ∘ e_L = Q(L) ∘ Q(q)`, written with Mathlib's
`SmallShiftedHom.comp` (`α.comp β` is `β[a] ∘ α`).
Source: Iversen, *Cohomology of Sheaves*, Springer Universitext 1986, Ch. I (Yoneda products);
Mathlib's `Localization.SmallShiftedHom.comp_assoc` and `mk₀Inv_comp_mk₀`. -/
theorem spec_resolutionClass_comp_mk₀ (X : Over (Spec ↧ℂ))
    {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L : K ⟶ K⟦(1 : ℤ)⟧) :
    (resolutionClass X q hq L).comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q)
        (zero_add 1) =
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom K K (1 : ℤ) from L)) (add_zero 1) :=
  spec_resolutionClass_comp_mk₀_aux X q hq L

/-- With the identity resolution, `e_L` is `L` itself. -/
example (X : Over (Spec ↧ℂ)) {K : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    (L : K ⟶ K⟦(1 : ℤ)⟧) :
    (resolutionClass X (𝟙 K) (MorphismProperty.id_mem _ K) L).comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl (𝟙 K))
        (zero_add 1) =
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl (𝟙 K)).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom K K (1 : ℤ) from L)) (add_zero 1) :=
  spec_resolutionClass_comp_mk₀ X (𝟙 K) _ L

/-- **Uniqueness of `e_L`.** A degree-one morphism `e : A ⟶ A[1]` of the derived category with
`Q(q)[1] ∘ e = Q(L) ∘ Q(q)` is `e_L`: composition with the isomorphism `Q(q)[1]` is injective.
Source: Iversen, *Cohomology of Sheaves*, Ch. I; Mathlib's
`Localization.SmallShiftedHom.postcompEquiv`. -/
theorem spec_resolutionClass_unique (X : Over (Spec ↧ℂ))
    {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L : K ⟶ K⟦(1 : ℤ)⟧)
    (e : Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms X) A A (1 : ℤ))
    (he : e.comp (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q)
        (zero_add 1) =
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom K K (1 : ℤ) from L)) (add_zero 1)) :
    e = resolutionClass X q hq L :=
  spec_resolutionClass_unique_aux X q hq L e he

/-- Existence and uniqueness together. -/
example (X : Over (Spec ↧ℂ)) {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L : K ⟶ K⟦(1 : ℤ)⟧) :
    ∃! e : Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms X) A A (1 : ℤ),
      e.comp (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q)
          (zero_add 1) =
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q).comp
          (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
            (show ShiftedHom K K (1 : ℤ) from L)) (add_zero 1) :=
  ⟨resolutionClass X q hq L, spec_resolutionClass_comp_mk₀ X q hq L,
    fun e he => spec_resolutionClass_unique X q hq L e he⟩

/-- **The transport.** For a quasi-isomorphism `q : A ⟶ K`, `L : K ⟶ K⟦1⟧` and a class
`α ∈ ℍ^k(A)`: `ℍ(q)` sends `α` composed with `e_L` to `ℍ(q) α` composed with `L`. Since `ℍ(q)` is
bijective (Mathlib's `SmallShiftedHom.postcompEquiv`; see the `example`), the action of `L` on
`ℍ^•(K)` is, through `ℍ(q)`, composition with `e_L` on `ℍ^•(A)`.
Source: Iversen, *Cohomology of Sheaves*, Ch. I–II (Yoneda products act on Ext); Mathlib's
`Localization.SmallShiftedHom.comp_assoc`; statement `spec_resolutionClass_comp_mk₀`. -/
theorem spec_hypercohomologyMap_comp_resolutionClass (X : Over (Spec ↧ℂ))
    {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L : K ⟶ K⟦(1 : ℤ)⟧) {k m : ℤ} (h : 1 + k = m)
    (α : ℍ^k(X; A)) :
    hypercohomologyMap X q m (α.comp (resolutionClass X q hq L) h) =
      (hypercohomologyMap X q k α).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom K K (1 : ℤ) from L)) h :=
  spec_hypercohomologyMap_comp_resolutionClass_aux X q hq L h α

/-- The action of `L` on every class of `ℍ^k(K)`, through the inverse of the bijection `ℍ(q)`. -/
example (X : Over (Spec ↧ℂ)) {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L : K ⟶ K⟦(1 : ℤ)⟧) {k m : ℤ} (h : 1 + k = m)
    (β : ℍ^k(X; K)) :
    β.comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom K K (1 : ℤ) from L)) h =
      hypercohomologyMap X q m
        (((Localization.SmallShiftedHom.postcompEquiv q hq).symm β).comp
          (resolutionClass X q hq L) h) := by
  rw [spec_hypercohomologyMap_comp_resolutionClass]
  exact congrArg (fun γ => Localization.SmallShiftedHom.comp γ _ h)
    ((Localization.SmallShiftedHom.postcompEquiv q hq).apply_symm_apply β).symm

/-- **Additivity in `L`.** In the derived category, `e_{L+L'} = e_L + e_{L'}`.
Source: Mathlib's `DerivedCategory.Q` (an additive functor), `ShiftedHom.add_comp` and
`ShiftedHom.comp_add`. -/
theorem spec_resolutionClass_add (X : Over (Spec ↧ℂ))
    {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L L' : K ⟶ K⟦(1 : ℤ)⟧) :
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (resolutionClass X q hq (L + L')) =
      Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
          (resolutionClass X q hq L) +
        Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
          (resolutionClass X q hq L') :=
  spec_resolutionClass_add_aux X q hq L L'

example (X : Over (Spec ↧ℂ)) {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L : K ⟶ K⟦(1 : ℤ)⟧) :
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (resolutionClass X q hq (L + L)) =
      2 • Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (resolutionClass X q hq L) := by
  rw [spec_resolutionClass_add, two_smul]

/-- **`e_0 = 0`.**
Source: Mathlib's `ShiftedHom.zero_comp` and `ShiftedHom.comp_zero`. -/
theorem spec_resolutionClass_zero (X : Over (Spec ↧ℂ))
    {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) :
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (resolutionClass X q hq 0) = 0 :=
  spec_resolutionClass_zero_aux X q hq

/-- With additivity, `e_{-L} = -e_L`. -/
example (X : Over (Spec ↧ℂ)) {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L : K ⟶ K⟦(1 : ℤ)⟧) :
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (resolutionClass X q hq (-L)) =
      -Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (resolutionClass X q hq L) := by
  rw [eq_neg_iff_add_eq_zero, ← spec_resolutionClass_add, neg_add_cancel,
    spec_resolutionClass_zero]

/-- **`e_L` depends only on `Q(L)`.** In particular homotopic morphisms have the same class.
Source: Mathlib's `Localization.SmallShiftedHom.equiv_mk` (`mk L` is determined by `Q.map L`) and
`DerivedCategory.Q_map_eq_of_homotopy`. -/
theorem spec_resolutionClass_eq_of_Q_map_eq (X : Over (Spec ↧ℂ))
    {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L L' : K ⟶ K⟦(1 : ℤ)⟧)
    (h : DerivedCategory.Q.map L = DerivedCategory.Q.map L') :
    resolutionClass X q hq L = resolutionClass X q hq L' :=
  spec_resolutionClass_eq_of_Q_map_eq_aux X q hq L L' h

/-- Homotopic morphisms have the same class. -/
example (X : Over (Spec ↧ℂ)) {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L L' : K ⟶ K⟦(1 : ℤ)⟧) (H : Homotopy L L') :
    resolutionClass X q hq L = resolutionClass X q hq L' :=
  spec_resolutionClass_eq_of_Q_map_eq X q hq L L' (DerivedCategory.Q_map_eq_of_homotopy (h := H))

/-- **De Rham side: `L_θ ∘ q_Ω` sends `1` to `θ`.** For smooth integral `X`, a global holomorphic
`1`-form `θ` and a morphism `L : Ω• ⟶ Ω•⟦1⟧` that is the wedge with `θ` (hl1's
`IsWedgeThetaHom`), the degree-`0` component of `L ∘ q_Ω`, a sheaf morphism `ℂ_X ⟶ Ω^1`, sends
the global constant section `c` to the global `1`-form whose value at every point `x` is
`c θ(x)`. Values determine global forms, and a morphism out of the constant sheaf is determined by
the images of the constant global sections (`constantSheafAdj`), so this pins `L ∘ q_Ω` as the
morphism `c ↦ cθ`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (`θ ∧ c = cθ` for a
function `c`); hl1's `IsWedgeBy` in degree `0`; upstream `constantsToHolomorphicDeRhamComplexInt`
(constants as holomorphic `0`-forms) and `chartEvaluation_ofConstant`. -/
theorem spec_constantsToHolomorphicDeRham_comp_wedgeTheta_value (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X θ L) (c : ℂ) (x : ComplexPoint X) :
    globalOneFormCovector X (dim X.left)
        (((constantCoefficientXZeroIso X ℂ).inv ≫
            (constantsToHolomorphicDeRhamComplexInt X ≫ L).f ((0 : ℕ) : ℤ) ≫
              (wedgeThetaShiftXIso X 0).hom).hom.app (op ⊤)
          (constantGlobalSection X ℂ c)) x =
      c • globalOneFormCovector X (dim X.left) θ x :=
  spec_constantsToHolomorphicDeRham_comp_wedgeTheta_value_aux X θ L hL c x

/-- The constant `1` is sent to a form with the values of `θ`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X θ L) (x : ComplexPoint X) :
    globalOneFormCovector X (dim X.left)
        (((constantCoefficientXZeroIso X ℂ).inv ≫
            (constantsToHolomorphicDeRhamComplexInt X ≫ L).f ((0 : ℕ) : ℤ) ≫
              (wedgeThetaShiftXIso X 0).hom).hom.app (op ⊤)
          (constantGlobalSection X ℂ 1)) x =
      globalOneFormCovector X (dim X.left) θ x := by
  rw [spec_constantsToHolomorphicDeRham_comp_wedgeTheta_value X θ L hL, one_smul]

/-- **De Rham side, the unit class.** For smooth integral `X`, a degree-one cycle `z` of
`Γ(F^1 Ω•)` with form `θ` and `L` the wedge with `θ`: the class `ℤ[0] → ℂ[0] → Ω•`, composed with
`L` as a degree-one shifted morphism, is the de Rham class of `θ`. Both are the morphism
`ℤ[0] ⟶ Ω•[1]` sending `1` to `θ` in `Ω•[1]^0 = Ω^1`; the edge map behind `cycleDeRhamClass`
carries no sign (`Cocycle.equivHomShift`, built on `rightShift`).
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, II.4 (the edge map); Voisin, *Hodge Theory and
Complex Algebraic Geometry I*, §8.1.3; statement `spec_constantsToHolomorphicDeRham_comp_wedgeTheta_value`. -/
theorem spec_constantsToHolomorphicDeRham_comp_wedgeTheta (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X (cycleOneForm X z) L) :
    (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        (constantsIntToCoefficient X ℂ ≫ constantsToHolomorphicDeRhamComplexInt X)).comp
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom Ω•(X) Ω•(X) (1 : ℤ) from L))
      (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num) =
      cycleDeRhamClass X z :=
  spec_constantsToHolomorphicDeRham_comp_wedgeTheta_aux X z L hL

/-- With hl1's `L_θ` (existence frozen there): the unit class composed with `L_θ` is `[θ]`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) :
    ∃ L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧, IsWedgeThetaHom X (cycleOneForm X z) L ∧
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
          (constantsIntToCoefficient X ℂ ≫ constantsToHolomorphicDeRhamComplexInt X)).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom Ω•(X) Ω•(X) (1 : ℤ) from L))
        (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num) = cycleDeRhamClass X z := by
  have hz : cycleOneForm X z ∈ closedGlobalHolomorphicForms X 1 := by
    rw [show closedGlobalHolomorphicForms X 1 = closedGlobalHolomorphicOneForms X from rfl,
      ← spec_range_cycleOneForm X]
    exact ⟨z, rfl⟩
  obtain ⟨L, hL⟩ := spec_exists_isWedgeThetaHom X _ hz
  exact ⟨L, hL, spec_constantsToHolomorphicDeRham_comp_wedgeTheta X z L hL⟩

/-- **De Rham side: `e_{L_θ}` is the class of `θ`.** For smooth integral `X`, a degree-one cycle
`z` of `Γ(F^1 Ω•)` with form `θ` and `L` the wedge with `θ`: the unit `ℤ[0] ⟶ ℂ[0]` composed
with `e_L`, a class in `ℍ^1(ℂ[0]) = H^1(X(ℂ); ℂ)`, is sent by `ℍ(q_Ω)` to the de Rham class of
`θ`.
Source: statements `spec_hypercohomologyMap_comp_resolutionClass` and
`spec_constantsToHolomorphicDeRham_comp_wedgeTheta`; upstream `smallShiftedHomMkZero_comp`. -/
theorem spec_hypercohomologyMap_resolutionClass_wedgeTheta (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X (cycleOneForm X z) L) :
    hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) ((1 : ℕ) : ℤ)
        ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
            (constantsIntToCoefficient X ℂ)).comp
          (resolutionClass X (constantsToHolomorphicDeRhamComplexInt X)
            (constantsToHolomorphicDeRham_mem X) L)
          (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num)) =
      cycleDeRhamClass X z :=
  spec_hypercohomologyMap_resolutionClass_wedgeTheta_aux X z L hL

/-- Through upstream's equivalence `H^1(X(ℂ); ℂ) ≃ H_dR^1(X)`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X (cycleOneForm X z) L) :
    complexConstantCohomologyDeRhamEquiv X ((1 : ℕ) : ℤ)
        ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
            (constantsIntToCoefficient X ℂ)).comp
          (resolutionClass X (constantsToHolomorphicDeRhamComplexInt X)
            (constantsToHolomorphicDeRham_mem X) L)
          (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num)) =
      cycleDeRhamClass X z :=
  spec_hypercohomologyMap_resolutionClass_wedgeTheta X z L hL

/-- **Singular side: cup with the unit cochain.** For a singular `1`-cochain `a` on any space `Y`,
any commutative ring `K`, an open `U` and `r ∈ K`: left cup with `a|_U` sends the constant
`0`-cochain `r` (upstream's `constantsToSingularCochainZero`, `r` times the augmentation) to
`r a|_U`. This is the right unit law `a ∪ 1 = a` with the scalar pulled out.
Source: Hatcher, *Algebraic Topology*, §3.2 (the unit of the cup product); the repository's
`cupCochain_one`. -/
theorem spec_cupLeftPresheafHom_constants {K : Type} [CommRing K] {Y : TopCat.{0}}
    (a : Cochain K (TopCat.toSSet.obj Y) 1) (U : (Opens Y)ᵒᵖ) (r : K) :
    (cupLeftPresheafHom a 0).app U
        ((AlgebraicTopology.Singular.constantsToSingularCochainZero K Y).app U r) =
      (r • cupLeftRestrict a U : AlgebraicTopology.Singular.OpenCochains K Y U 1) :=
  spec_cupLeftPresheafHom_constants_aux a U r

/-- On the top open set with `r = 1`, the constant cochain is sent to `a|_⊤`. -/
example {Y : TopCat.{0}} (a : Cochain ℂ (TopCat.toSSet.obj Y) 1) :
    (cupLeftPresheafHom a 0).app (op ⊤)
        ((AlgebraicTopology.Singular.constantsToSingularCochainZero ℂ Y).app (op ⊤) (1 : ℂ)) =
      (cupLeftRestrict a (op ⊤) : AlgebraicTopology.Singular.OpenCochains ℂ Y (op ⊤) 1) := by
  rw [spec_cupLeftPresheafHom_constants, one_smul]

/-- **Singular side, the unit class.** For every `X`, every commutative ring `K` and every singular
`1`-cocycle `a` on `X(ℂ)`: the class `ℤ[0] → K[0] → S•`, composed with `C_a` as a degree-one
shifted morphism, is the image of `[a]` under hl2's `singularToSheafHypercohomology`. Both are the
morphism `ℤ[0] ⟶ S•[1]` sending `1` to the global section of `a` (statement
`spec_cupLeftPresheafHom_constants` with `r = 1`); no quasi-isomorphism is inverted.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, II.4 and III.1; Hatcher, *Algebraic Topology*,
§3.2; hl2's statement `spec_cupLeftHypercohomology_singularToSheafHypercohomology`. -/
theorem spec_constantsToSingular_comp_cupLeft (X : Over (Spec ↧ℂ)) (K : Type) [CommRing K]
    (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1) :
    (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        (constantsIntToCoefficient X K ≫ constantsToSingularCochainComplexInt X K)).comp
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom (singularCochainSheafComplexInt X K) (singularCochainSheafComplexInt X K)
          (1 : ℤ) from cupLeftComplexHom X a))
      (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num) =
      singularToSheafHypercohomology X K 1
        (HodgeLean.Foundations.Singular.cohomologyClass _ 1 a) :=
  spec_constantsToSingular_comp_cupLeft_aux X K a

/-- The unit class composed with `C_0` is zero. -/
example (X : Over (Spec ↧ℂ)) :
    (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        (constantsIntToCoefficient X ℂ ≫ constantsToSingularCochainComplexInt X ℂ)).comp
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom (singularCochainSheafComplexInt X ℂ) (singularCochainSheafComplexInt X ℂ)
          (1 : ℤ) from cupLeftComplexHom X 0))
      (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num) =
      (0 : ℍ^((1 : ℕ) : ℤ)(X; singularCochainSheafComplexInt X ℂ)) := by
  rw [spec_constantsToSingular_comp_cupLeft, map_zero, map_zero]

/-- **Singular side: `e_{C_a}` is the class of `a`.** For smooth integral `X`, every commutative
ring `K` and every singular `1`-cocycle `a` on `X(ℂ)`: the unit `ℤ[0] ⟶ K[0]` composed with
`e_{C_a}`, a class in `ℍ^1(K[0]) = H^1(X(ℂ); K)`, is sent by `ℍ(q_S)` to the image of `[a]` under
`singularToSheafHypercohomology`.
Source: statements `spec_hypercohomologyMap_comp_resolutionClass` and
`spec_constantsToSingular_comp_cupLeft`; upstream `smallShiftedHomMkZero_comp`. -/
theorem spec_hypercohomologyMap_resolutionClass_cupLeft (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (K : Type) [CommRing K]
    (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1) :
    hypercohomologyMap X (constantsToSingularCochainComplexInt X K) ((1 : ℕ) : ℤ)
        ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
            (constantsIntToCoefficient X K)).comp
          (resolutionClass X (constantsToSingularCochainComplexInt X K)
            (constantsToSingularCochain_mem X K) (cupLeftComplexHom X a))
          (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num)) =
      singularToSheafHypercohomology X K 1
        (HodgeLean.Foundations.Singular.cohomologyClass _ 1 a) :=
  spec_hypercohomologyMap_resolutionClass_cupLeft_aux X K a

/-- Since `ℍ(q_S)` is bijective, the unit composed with `e_{C_a}` is the class of `[a]` pulled back
along it. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (a : Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1) :
    (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        (constantsIntToCoefficient X ℂ)).comp
      (resolutionClass X (constantsToSingularCochainComplexInt X ℂ)
        (constantsToSingularCochain_mem X ℂ) (cupLeftComplexHom X a))
      (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num) =
      (Localization.SmallShiftedHom.postcompEquiv (constantsToSingularCochainComplexInt X ℂ)
        (constantsToSingularCochain_mem X ℂ)).symm
        (singularToSheafHypercohomology X ℂ 1
          (HodgeLean.Foundations.Singular.cohomologyClass _ 1 a)) := by
  rw [Equiv.eq_symm_apply]
  exact spec_hypercohomologyMap_resolutionClass_cupLeft X ℂ a

end HodgeLean.Adapters

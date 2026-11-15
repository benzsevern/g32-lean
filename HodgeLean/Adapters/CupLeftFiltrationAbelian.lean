import HodgeLean.Adapters.CupLeftFiltrationAbelianProofs

/-! # `e_{L_θ} = e_{C_{a_θ}}` through the primitive complex, and `hL` for `cupProductOf X` on abelian `X`: frozen specification

Stage hl5 of the `hL` track, the final stage (`docs/specs/CupLeftFiltrationAbelian.md`). Stage hl3
(`ResolutionClassAction`) defined the class `e_L : ℂ[0] ⟶ ℂ[0][1]` of a degree-one morphism `L`
of a resolution of `ℂ[0]`. Stage hl4 (`CupLeftTransport`) read the action of the singular cup
morphism `C_a` on `bettiDeRhamHQ`. Stage 4k (`HolomorphicPeriodsDeRham`) built the two-term
resolution `q' : ℂ[0] ⟶ T' = [Ω^0 → Ω^0/ℂ]` with `p : T' ⟶ Ω•` and the integration map
`r : T' ⟶ S•`. This stage compares `e_{L_θ}` with `e_{C_{a_θ}}` at the level of morphisms of
complexes out of `ℂ[0]`, through `T'`, and assembles `hL`.

Claimed:
* for smooth integral `X`: every morphism `ℂ[0] ⟶ Ω•[1]` lifts along `p[1]` to `ℂ[0] ⟶ T'[1]`; if
  the lift `j` of `q_Ω ≫ L_θ` is taken, and `θ'` is a global primitive class of `θ` whose
  integration is the global section of the singular cocycle `Ψ`, then `j ≫ r[1] = q_S ≫ C_Ψ`;
* for every `X`, the formal cancellation: if `q' ≫ p = q` with `p ∈ W` and `j ≫ p[1] = q ≫ L`,
  then `e_L` composed with `q'` is the class of `j`;
* hence `e_{L_θ} = e_{C_Ψ}` for smooth integral `X` with such `θ'` and `Ψ`, and for abelian `X`
  with `Ψ` the integration cocycle of `θ`;
* the de Rham image `dR ∘ e` of `ℍ(S•_ℂ)` is `ℍ(q_Ω) ∘ ℍ(q_S)⁻¹`, and under it the action of
  `C_Ψ` is composition with `L_θ`; composition with any `L` raises the Hodge filtration by one;
* for abelian `X`: if `β_1 x` is the de Rham class of a closed holomorphic `1`-form `θ`, the complex
  singular class of `x` is `q` times the class of the integration cocycle of `θ`, with `q` the
  normalization scalar of `cupComparison` in degree one;
* `hL` for `cupProductOf X` on abelian `X`, with the binder of cupf1 and hlred as its type.

With hlred's `spec_cupFiltered_of_cupLeft_alone` and `spec_hodgeDecomposition_of_cupLeft_alone`
and the torus theorem `torusCohomology_cupProductOf` (available on `main`), the `example`s at the end
derive `CupFiltered X (cupProductOf X)` and `HodgeDecomposition X` for abelian `X` with no binder
left. That is an implication from the open statements of this stage and of stages hl3 and hl4,
with no geometric input beyond `[GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]`.

Not claimed: anything for non-abelian `X` beyond the smooth integral statements above; a left
factor of degree other than one; the value of the normalization scalar; any new hypothesis. No
statement assumes `BettiDeRhamIso`, `HodgeDecomposition` or `CupFiltered`.
HC no distance; AV milestone no distance.
-/

noncomputable section

-- Boundary conversions between HQ and upstream sheaf cohomology have deep instance terms.
set_option maxRecDepth 4000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

local instance cupLeftFiltrationHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- **The lift along `p`.** For smooth integral `X`, every morphism of complexes
`φ : ℂ[0] ⟶ Ω•[1]` factors through `p[1] : T'[1] ⟶ Ω•[1]`. Only degree `0` matters: `φ` in degree
`0` is a sheaf map `ℂ_X ⟶ Ω^1` killed by `d` (it is a chain map out of a complex concentrated in
degree `0`), so it lands in `Ω^1_cl`, and `Ω^0/ℂ ⟶ Ω^1_cl` is an isomorphism (stage 4k).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3; stage 4k
`spec_primitiveQuotientToClosedOneForm_isIso`. -/
theorem spec_exists_primitiveComplex_lift (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (φ : constantComplexSheafComplexInt X ⟶ Ω•(X)⟦(1 : ℤ)⟧) :
    ∃ j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧,
      j ≫ (primitiveComplexToDeRham X)⟦(1 : ℤ)⟧' = φ :=
  spec_exists_primitiveComplex_lift_aux X φ

/-- The lift of `q_Ω ≫ L` for any `L : Ω• ⟶ Ω•[1]`, in particular `L_θ`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) :
    ∃ j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧,
      j ≫ (primitiveComplexToDeRham X)⟦(1 : ℤ)⟧' = constantsToHolomorphicDeRhamComplexInt X ≫ L :=
  spec_exists_primitiveComplex_lift X _

/-- **The lift integrates to `C_Ψ`.** For smooth integral `X`, a global holomorphic `1`-form `θ`,
a global section `θ'` of `Ω^0/ℂ` with `dθ' = θ`, a complex singular `1`-cocycle `Ψ` whose global
section is the integration of `θ'`, `L` the wedge with `θ`, and any `j : ℂ[0] ⟶ T'[1]` with
`j ≫ p[1] = q_Ω ≫ L`: `j ≫ r[1] = q_S ≫ C_Ψ`. In degree `0`, `j` sends the constant `c` to the
unique global section of `Ω^0/ℂ` with derivative `cθ` (hl3's
`spec_constantsToHolomorphicDeRham_comp_wedgeTheta_value`), which is `cθ'` (locally `c f` for a
primitive `f` of `θ`); the integration map sends it to the germ of `cΨ`, which is `C_Ψ` applied
to the constant `c` (hl3's `spec_cupLeftPresheafHom_constants`). A morphism out of the constant
sheaf is determined by the images of the constant global sections (`constantSheafAdj`).
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15 (integration through local
primitives); Hatcher, *Algebraic Topology*, §3.2 (the unit of the cup product); hl3
`spec_constantsToHolomorphicDeRham_comp_wedgeTheta_value` and `spec_cupLeftPresheafHom_constants`;
stage 4k `spec_globalCochainSection_eq_toSheafify`. -/
theorem spec_primitiveComplex_lift_comp_toSingular (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (hθ' : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = θ)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : globalCochainSection X 1 Ψ.1 =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ')
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X θ L)
    (j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧)
    (hj : j ≫ (primitiveComplexToDeRham X)⟦(1 : ℤ)⟧' =
      constantsToHolomorphicDeRhamComplexInt X ≫ L) :
    j ≫ (primitiveComplexToSingular X)⟦(1 : ℤ)⟧' =
      constantsToSingularCochainComplexInt X ℂ ≫ cupLeftComplexHom X Ψ :=
  spec_primitiveComplex_lift_comp_toSingular_aux X θ θ' hθ' Ψ hΨ L hL j hj

/-- One `j` with both compatibilities. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (hθ' : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = θ)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : globalCochainSection X 1 Ψ.1 =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ')
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X θ L) :
    ∃ j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧,
      j ≫ (primitiveComplexToDeRham X)⟦(1 : ℤ)⟧' = constantsToHolomorphicDeRhamComplexInt X ≫ L ∧
      j ≫ (primitiveComplexToSingular X)⟦(1 : ℤ)⟧' =
        constantsToSingularCochainComplexInt X ℂ ≫ cupLeftComplexHom X Ψ := by
  obtain ⟨j, hj⟩ := spec_exists_primitiveComplex_lift X
    (constantsToHolomorphicDeRhamComplexInt X ≫ L)
  exact ⟨j, hj, spec_primitiveComplex_lift_comp_toSingular X θ θ' hθ' Ψ hΨ L hL j hj⟩

/-- **The cancellation.** For every `X`, quasi-isomorphisms `q : A ⟶ K` and `p : T ⟶ K`, a
morphism `q' : A ⟶ T` with `q' ≫ p = q`, `L : K ⟶ K[1]` and `j : A ⟶ T[1]` with
`j ≫ p[1] = q ≫ L`: `e_L` followed by `q'` is the class of `j`. Postcompose both sides with
`Q(p)`: the left side becomes `e_L` followed by `q`, which is `Q(q ≫ L)` (hl3's
`spec_resolutionClass_comp_mk₀`), and the right side is `Q(j ≫ p[1])`; postcomposition with
`Q(p)` is injective (`postcompEquiv p hp`). This is applied with `(K, p) = (Ω•, p)` and
`(S•, r)` (the two `example`s).
Source: Iversen, *Cohomology of Sheaves*, Springer Universitext 1986, Ch. I; Mathlib's
`Localization.SmallShiftedHom.comp_assoc`, `mk₀_comp_mk₀` and `postcompEquiv`; hl3
`spec_resolutionClass_comp_mk₀`. -/
theorem spec_resolutionClass_comp_mk₀_eq_mk_of_lift (X : Over (Spec ↧ℂ))
    {A K T : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (q' : A ⟶ T) (p : T ⟶ K)
    (hp : analyticQuasiIsomorphisms X p) (hqp : q' ≫ p = q) (L : K ⟶ K⟦(1 : ℤ)⟧)
    (j : A ⟶ T⟦(1 : ℤ)⟧) (hj : j ≫ p⟦(1 : ℤ)⟧' = q ≫ L) :
    (resolutionClass X q hq L).comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q')
        (zero_add 1) =
      Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom A T (1 : ℤ) from j) :=
  spec_resolutionClass_comp_mk₀_eq_mk_of_lift_aux X q hq q' p hp hqp L j hj

/-- The de Rham cancellation: `e_L` followed by `q'` is the class of the lift `j`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧)
    (j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧)
    (hj : j ≫ (primitiveComplexToDeRham X)⟦(1 : ℤ)⟧' =
      constantsToHolomorphicDeRhamComplexInt X ≫ L) :
    (resolutionClass X (constantsToHolomorphicDeRhamComplexInt X)
        (constantsToHolomorphicDeRham_mem X) L).comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
          (constantsToPrimitiveComplex X)) (zero_add 1) =
      Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom (constantComplexSheafComplexInt X) (primitiveComplex X) (1 : ℤ) from j) :=
  spec_resolutionClass_comp_mk₀_eq_mk_of_lift X _ _ _ _ (primitiveComplexToDeRham_mem X)
    (constantsToPrimitiveComplex_comp_toDeRham X) L j hj

/-- The singular cancellation: `e_{C_Ψ}` followed by `q'` is the class of `j`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧)
    (hj : j ≫ (primitiveComplexToSingular X)⟦(1 : ℤ)⟧' =
      constantsToSingularCochainComplexInt X ℂ ≫ cupLeftComplexHom X Ψ) :
    (resolutionClass X (constantsToSingularCochainComplexInt X ℂ)
        (constantsToSingularCochain_mem X ℂ) (cupLeftComplexHom X Ψ)).comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
          (constantsToPrimitiveComplex X)) (zero_add 1) =
      Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom (constantComplexSheafComplexInt X) (primitiveComplex X) (1 : ℤ) from j) :=
  spec_resolutionClass_comp_mk₀_eq_mk_of_lift X _ _ _ _ (primitiveComplexToSingular_mem X)
    (spec_constantsToPrimitiveComplex_comp_toSingular X) _ j hj

/-- **`e_{L_θ} = e_{C_Ψ}`, through a global primitive class.** For smooth integral `X`, a global
holomorphic `1`-form `θ` with a global primitive class `θ'` in `Ω^0/ℂ`, a complex singular
`1`-cocycle `Ψ` whose global section is the integration of `θ'`, and `L` the wedge with `θ`: the
classes of `L` on `q_Ω` and of `C_Ψ` on `q_S` agree in `Hom_D(ℂ[0], ℂ[0][1])`. Take the lift `j`
of `q_Ω ≫ L` (`spec_exists_primitiveComplex_lift`); it also lifts `q_S ≫ C_Ψ`
(`spec_primitiveComplex_lift_comp_toSingular`). By the cancellation both classes, followed by
`q'`, are the class of `j`, and postcomposition with `q'` is injective (`W q'`).
Source: Iversen, *Cohomology of Sheaves*, Ch. I; Bott–Tu, *Differential Forms in Algebraic
Topology*, §15; statements `spec_exists_primitiveComplex_lift`,
`spec_primitiveComplex_lift_comp_toSingular` and `spec_resolutionClass_comp_mk₀_eq_mk_of_lift`;
stage 4k `spec_constantsToPrimitiveComplex_quasiIso`. -/
theorem spec_resolutionClass_wedgeTheta_eq_cupLeft_of_primitive (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (hθ' : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = θ)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : globalCochainSection X 1 Ψ.1 =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ')
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X θ L) :
    resolutionClass X (constantsToHolomorphicDeRhamComplexInt X)
        (constantsToHolomorphicDeRham_mem X) L =
      resolutionClass X (constantsToSingularCochainComplexInt X ℂ)
        (constantsToSingularCochain_mem X ℂ) (cupLeftComplexHom X Ψ) :=
  spec_resolutionClass_wedgeTheta_eq_cupLeft_of_primitive_aux X θ θ' hθ' Ψ hΨ L hL

/-- The two degree-one computations of hl3 now agree: the unit class composed with `e_{C_Ψ}` is
also sent by `ℍ(q_Ω)` to the de Rham class of `z`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (hθ' : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = cycleOneForm X z)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : globalCochainSection X 1 Ψ.1 =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ')
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X (cycleOneForm X z) L) :
    hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) ((1 : ℕ) : ℤ)
        ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
            (constantsIntToCoefficient X ℂ)).comp
          (resolutionClass X (constantsToSingularCochainComplexInt X ℂ)
            (constantsToSingularCochain_mem X ℂ) (cupLeftComplexHom X Ψ))
          (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num)) =
      cycleDeRhamClass X z := by
  rw [← spec_resolutionClass_wedgeTheta_eq_cupLeft_of_primitive X _ θ' hθ' Ψ hΨ L hL]
  exact spec_hypercohomologyMap_resolutionClass_wedgeTheta X z L hL

/-- **`e_{L_θ} = e_{C_{a_θ}}` on abelian `X`.** For abelian `X`, a degree-one cycle `z` of
`Γ(F^1 Ω•)` with form `θ`, the integration cocycle `Ψ` of `θ` (`Ψ.1 = ∫ θ`) and `L` the wedge with
`θ`: `e_L = e_{C_Ψ}`. Stage 4k gives the global primitive class `θ'` of the closed form `θ`
(`spec_exists_globalPrimitive_of_closed`) and identifies the global section of `Ψ` with the
integration of `θ'` (`spec_globalCochainSection_singularIntegrationCochain`).
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15; stage 4k
`spec_exists_globalPrimitive_of_closed` and `spec_globalCochainSection_singularIntegrationCochain`;
statement `spec_resolutionClass_wedgeTheta_eq_cupLeft_of_primitive`. -/
theorem spec_resolutionClass_wedgeTheta_eq_cupLeft (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z))
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X (cycleOneForm X z) L) :
    resolutionClass X (constantsToHolomorphicDeRhamComplexInt X)
        (constantsToHolomorphicDeRham_mem X) L =
      resolutionClass X (constantsToSingularCochainComplexInt X ℂ)
        (constantsToSingularCochain_mem X ℂ) (cupLeftComplexHom X Ψ) :=
  spec_resolutionClass_wedgeTheta_eq_cupLeft_aux X z Ψ hΨ L hL

/-- With hl3's statement 12 the two unit classes are the same class of `H^1(X(ℂ); ℂ)`, read in
`ℍ^1(S•)`. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z))
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X (cycleOneForm X z) L) :
    hypercohomologyMap X (constantsToSingularCochainComplexInt X ℂ) ((1 : ℕ) : ℤ)
        ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
            (constantsIntToCoefficient X ℂ)).comp
          (resolutionClass X (constantsToHolomorphicDeRhamComplexInt X)
            (constantsToHolomorphicDeRham_mem X) L)
          (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num)) =
      singularToSheafHypercohomology X ℂ 1
        (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ) := by
  have he := spec_resolutionClass_wedgeTheta_eq_cupLeft X z Ψ hΨ L hL
  have h12 := spec_hypercohomologyMap_resolutionClass_cupLeft X ℂ Ψ
  rw [← he] at h12
  exact h12

/-- **The de Rham image of `ℍ(S•_ℂ)` is `ℍ(q_Ω) ∘ ℍ(q_S)⁻¹`.** For smooth integral `X`, `n` and
`β ∈ ℍ^n(S•_ℂ)`: hl4's de Rham image `dR(e_n β)` (`fieldToDeRhamCohomology ℂ X n` after
`sheafHypercohomologyFieldEquiv ℂ X n`) is `ℍ(q_Ω)` applied to the inverse of `ℍ(q_S)` at `β`.
Unfold: `e_n` is the inverse of postcomposition with `q_S` followed by upstream's
`ℍ^n(ℂ[0]) ≃ H^n(X; ℂ)`, and `dR` is the inverse of the latter followed by
`ℍ(ℂ[0] → ℂ[0] → Ω•)`, whose first map is the identity for `K = ℂ`.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1 (comparison of acyclic resolutions);
upstream `fieldToDeRhamCohomology`, `hypercohomologyAddEquivConstantCohomology` and
`fieldToHolomorphicDeRhamComplexInt`; hl4 `sheafHypercohomologyFieldEquiv`. -/
theorem spec_fieldToDeRham_sheafHypercohomologyFieldEquiv (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (β : Hypercohomology X (singularCochainSheafComplexInt X ℂ) n) :
    fieldToDeRhamCohomology ℂ X n (sheafHypercohomologyFieldEquiv ℂ X n β) =
      hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n
        ((Localization.SmallShiftedHom.postcompEquiv (constantsToSingularCochainComplexInt X ℂ)
          (constantsToSingularCochain_mem X ℂ)).symm β) :=
  spec_fieldToDeRham_sheafHypercohomologyFieldEquiv_aux X n β

/-- On the class of a singular class `y`, this is stage 4k's complex comparison. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (y : AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) n) :
    fieldToDeRhamCohomology ℂ X n (singularToFieldCohomology ℂ X n y) =
      hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n
        ((Localization.SmallShiftedHom.postcompEquiv (constantsToSingularCochainComplexInt X ℂ)
          (constantsToSingularCochain_mem X ℂ)).symm (singularToSheafHypercohomology X ℂ n y)) :=
  spec_fieldToDeRham_sheafHypercohomologyFieldEquiv X n _

/-- **The actions agree.** For smooth integral `X`, `L : Ω• ⟶ Ω•[1]` and a complex singular
`1`-cocycle `Ψ` with `e_L = e_{C_Ψ}`, every `k`, `m` with `1 + k = m` and `β ∈ ℍ^k(S•_ℂ)`: under
`ℍ(q_Ω) ∘ ℍ(q_S)⁻¹`, `ℍ(C_Ψ)` (hl2's `cupLeftHypercohomology`) becomes composition with `L`.
Write `α = ℍ(q_S)⁻¹ β`; hl3's transport (`spec_hypercohomologyMap_comp_resolutionClass`) on the
singular side gives `ℍ(q_S)⁻¹ (ℍ(C_Ψ) β) = α ∘ e_{C_Ψ} = α ∘ e_L`, and on the de Rham side
`ℍ(q_Ω)(α ∘ e_L) = ℍ(q_Ω) α ∘ L`.
Source: Iversen, *Cohomology of Sheaves*, Ch. I–II (Yoneda products act on Ext); hl3
`spec_hypercohomologyMap_comp_resolutionClass`; Mathlib's
`Localization.SmallShiftedHom.postcompEquiv`. -/
theorem spec_hypercohomologyMap_comp_wedgeTheta_eq_cupLeft (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧)
    (he : resolutionClass X (constantsToHolomorphicDeRhamComplexInt X)
        (constantsToHolomorphicDeRham_mem X) L =
      resolutionClass X (constantsToSingularCochainComplexInt X ℂ)
        (constantsToSingularCochain_mem X ℂ) (cupLeftComplexHom X Ψ))
    {k m : ℤ} (h : 1 + k = m) (β : Hypercohomology X (singularCochainSheafComplexInt X ℂ) k) :
    hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) m
        ((Localization.SmallShiftedHom.postcompEquiv (constantsToSingularCochainComplexInt X ℂ)
          (constantsToSingularCochain_mem X ℂ)).symm (cupLeftHypercohomology X Ψ h β)) =
      (hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) k
        ((Localization.SmallShiftedHom.postcompEquiv (constantsToSingularCochainComplexInt X ℂ)
          (constantsToSingularCochain_mem X ℂ)).symm β)).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom Ω•(X) Ω•(X) (1 : ℤ) from L)) h :=
  spec_hypercohomologyMap_comp_wedgeTheta_eq_cupLeft_aux X Ψ L he h β

/-- Through hl1's shift map: the action of `C_Ψ` is `shift ∘ ℍ(L)` on the de Rham side. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧)
    (he : resolutionClass X (constantsToHolomorphicDeRhamComplexInt X)
        (constantsToHolomorphicDeRham_mem X) L =
      resolutionClass X (constantsToSingularCochainComplexInt X ℂ)
        (constantsToSingularCochain_mem X ℂ) (cupLeftComplexHom X Ψ))
    (k : ℤ) (β : Hypercohomology X (singularCochainSheafComplexInt X ℂ) k) :
    hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) (k + 1)
        ((Localization.SmallShiftedHom.postcompEquiv (constantsToSingularCochainComplexInt X ℂ)
          (constantsToSingularCochain_mem X ℂ)).symm
          (cupLeftHypercohomology X Ψ (add_comm 1 k) β)) =
      hypercohomologyShift X Ω•(X) k (hypercohomologyMap X L k
        (hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) k
          ((Localization.SmallShiftedHom.postcompEquiv (constantsToSingularCochainComplexInt X ℂ)
            (constantsToSingularCochain_mem X ℂ)).symm β))) := by
  rw [spec_hypercohomologyShift_hypercohomologyMap_eq_comp]
  exact spec_hypercohomologyMap_comp_wedgeTheta_eq_cupLeft X Ψ L he (add_comm 1 k) β

/-- **The actions agree, through `dR ∘ e`, on abelian `X`.** For abelian `X`, a degree-one cycle
`z` of `Γ(F^1 Ω•)` with form `θ`, the integration cocycle `Ψ` of `θ`, `L` the wedge with `θ`, `k`
and `β ∈ ℍ^k(S•_ℂ)`: the de Rham image of `ℍ(C_Ψ) β` is the de Rham image of `β` composed with
`L`, in the form of hl4's `spec_bettiDeRhamHQ_cupC_eq_smul_deRham_cupLeft`.
Source: statements `spec_resolutionClass_wedgeTheta_eq_cupLeft`,
`spec_fieldToDeRham_sheafHypercohomologyFieldEquiv` and
`spec_hypercohomologyMap_comp_wedgeTheta_eq_cupLeft`. -/
theorem spec_deRham_cupLeftHypercohomology (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z))
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X (cycleOneForm X z) L)
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ))
    (β : Hypercohomology X (singularCochainSheafComplexInt X ℂ) k) :
    fieldToDeRhamCohomology ℂ X (1 + k)
        (sheafHypercohomologyFieldEquiv ℂ X (1 + k) (cupLeftHypercohomology X Ψ h β)) =
      (fieldToDeRhamCohomology ℂ X k (sheafHypercohomologyFieldEquiv ℂ X k β)).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom Ω•(X) Ω•(X) (1 : ℤ) from L)) h :=
  spec_deRham_cupLeftHypercohomology_aux X z Ψ hΨ L hL k h β

/-- **Composition with `L` raises the Hodge filtration by one.** For smooth integral `X`, every
`L : Ω• ⟶ Ω•[1]`, `q` and `1 + k = m`: `α ∈ F^q H^k_dR` gives `α ∘ L ∈ F^{1+q} H^m_dR`. This is
hl1's `spec_hypercohomologyShift_mem_hodgeFiltration` with `spec_hypercohomologyShift_hypercohomologyMap_eq_comp`,
re-indexed to an arbitrary `h : 1 + k = m` (the form in which hl4 and the statement above use
the degree; the degrees `k + 1` and `1 + k` are equal but not definitionally).
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.4; hl1
`spec_hypercohomologyShift_mem_hodgeFiltration` and
`spec_hypercohomologyShift_hypercohomologyMap_eq_comp`. -/
theorem spec_comp_mem_hodgeFiltration (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (q : ℤ) {k m : ℤ} (h : 1 + k = m)
    (α : H_dR^k(X)) (hα : α ∈ F^q H_dR^k(X)) :
    α.comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom Ω•(X) Ω•(X) (1 : ℤ) from L)) h ∈ F^(1 + q) H_dR^m(X) :=
  spec_comp_mem_hodgeFiltration_aux X L q h α hα

/-- With the statement above: `ℍ(C_Ψ)` raises the filtration of the de Rham image by one. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z))
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X (cycleOneForm X z) L)
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (q : ℤ)
    (β : Hypercohomology X (singularCochainSheafComplexInt X ℂ) k)
    (hβ : fieldToDeRhamCohomology ℂ X k (sheafHypercohomologyFieldEquiv ℂ X k β) ∈
      F^q H_dR^(k : ℤ)(X)) :
    fieldToDeRhamCohomology ℂ X (1 + k)
        (sheafHypercohomologyFieldEquiv ℂ X (1 + k) (cupLeftHypercohomology X Ψ h β)) ∈
      F^(1 + q) H_dR^((1 + k : ℕ) : ℤ)(X) := by
  rw [spec_deRham_cupLeftHypercohomology X z Ψ hΨ L hL k h β]
  exact spec_comp_mem_hodgeFiltration X L q h _ hβ

/-- **The degree-one input, with its exact scalar.** For abelian `X`, a rational `q` that is a
normalization scalar of `cupComparison` in degree one, `x ∈ ℂ ⊗[ℚ] HQ X 1` whose Betti–de Rham
image is the de Rham class of a degree-one cycle `z` of `Γ(F^1 Ω•)` (every `x` with
`β_1 x ∈ F^1`, by s4l's `spec_hodgeFiltration_one_eq_range_cycleDeRhamClass`), and the
integration cocycle `Ψ` of the form of `z`: the complex singular class of `x` is `q` times `[Ψ]`.
Both have complex comparison `q · β_1 x`: the left by stage 4j
(`fieldToDeRham_singularToFieldCohomology_cohomologyBaseChange_tmul`, with this `q`), the right by
stage 4k's `spec_deRham_singularIntegrationCochain` (constant `1`); the complex comparison is
injective (`spec_singularToFieldCohomology_bijective`, `spec_fieldToDeRhamCohomology_complex_bijective`).
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15; Bredon, *Sheaf Theory*, 2nd ed.,
GTM 170, III.1; stage 4j `spec_deRham_singularToFieldCohomology_cohomologyBaseChange`, stage 4k
`spec_deRham_singularIntegrationCochain`, stage 3c `spec_singularToFieldCohomology_bijective`. -/
theorem spec_complexSingularClass_eq_smul_integrationClass (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (q : ℚ)
    (hq : ∀ v : HQ X 1,
      singularToFieldCohomology ℚ X 1 (cupComparison X 1 v) = q • HQ.linearEquiv X 1 v)
    (x : ℂ ⊗[ℚ] HQ X 1) (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (hx : bettiDeRhamHQ X 1 x = cycleDeRhamClass X z)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z)) :
    complexSingularClass X 1 x =
      (q : ℂ) • Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ :=
  spec_complexSingularClass_eq_smul_integrationClass_aux X q hq x z hx Ψ hΨ

/-- With the normalization scalar of stage 4j: every `x` with `β_1 x ∈ F^1` has, after rescaling
by a nonzero rational, the class of an integration cocycle. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : ℂ ⊗[ℚ] HQ X 1) (hx : bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X)) :
    ∃ q : ℚ, q ≠ 0 ∧ ∃ z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ),
      ∃ Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
          (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1,
        Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) ∧
        complexSingularClass X 1 x =
          (q : ℂ) • Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨q, hq0, hq⟩ := spec_singularToFieldCohomology_cupComparison X 1
  have hr : bettiDeRhamHQ X 1 x ∈ (cycleDeRhamClass X).range := by
    rw [← spec_hodgeFiltration_one_eq_range_cycleDeRhamClass X]
    exact hx
  obtain ⟨z, hz⟩ := hr
  exact ⟨q, hq0, z, ⟨_, spec_coboundary_singularIntegrationCochain X (dim X.left)
    (cycleOneForm X z)⟩, rfl, spec_complexSingularClass_eq_smul_integrationClass X q hq x z
    hz.symm _ rfl⟩

/-- **`hL` for `cupProductOf X` on abelian `X`.** For abelian `X`: if `β_1 x ∈ F^1 H^1_dR` and
`β_k y ∈ F^q H^k_dR`, then `β_{1+k}(x ∪ y) ∈ F^{1+q} H^{1+k}_dR`, for the cup product
`cupProductOf X` and `β = bettiDeRhamHQ X`. The type is the binder `hL` of cupf1 and hlred,
verbatim, with `μ = cupProductOf X`. Assembly: write `β_1 x = [θ_z]`
(`spec_hodgeFiltration_one_eq_range_cycleDeRhamClass`) and `κ_1 x = q [Ψ]` with `q ≠ 0`
(`spec_complexSingularClass_eq_smul_integrationClass`), so `x' = q⁻¹ x` has `κ_1 x' = [Ψ]`. hl4's
`spec_bettiDeRhamHQ_cupC_eq_smul_deRham_cupLeft` gives `β(x' ∪ y) = c · dR(e(ℍ(C_Ψ)(ι(κ_k y))))`
with `c ≠ 0`; `spec_deRham_cupLeftHypercohomology` turns `ℍ(C_Ψ)` into composition with `L_θ`;
`dR(e(ι(κ_k y))) = q_k · β_k y ∈ F^q` (stage 4j); and `spec_comp_mem_hodgeFiltration` raises the
level by one. Nonzero scalars preserve membership in the `ℂ`-subspace `F^{1+q}`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§7.1 (cup product with a holomorphic form preserves the Hodge filtration) and §8.1;
Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.3; hl4
`spec_bettiDeRhamHQ_cupC_eq_smul_deRham_cupLeft`; statements
`spec_complexSingularClass_eq_smul_integrationClass`, `spec_deRham_cupLeftHypercohomology` and
`spec_comp_mem_hodgeFiltration`. -/
theorem spec_cupLeft_cupProductOf (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m ((cupProductOf X).cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X) :=
  spec_cupLeft_cupProductOf_aux X

/-- **`CupFiltered X (cupProductOf X)` for abelian `X`** (the ledger hypothesis O5), from hlred's
`spec_cupFiltered_of_cupLeft_alone` with the torus theorem `torusCohomology_cupProductOf` (available)
and `spec_cupLeft_cupProductOf`. No binder remains. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    CupFiltered X (cupProductOf X) :=
  spec_cupFiltered_of_cupLeft_alone X (torusCohomology_cupProductOf X)
    (spec_cupLeft_cupProductOf X)

/-- **`HodgeDecomposition X` for abelian `X`**, from hlred's
`spec_hodgeDecomposition_of_cupLeft_alone` with the torus theorem `torusCohomology_cupProductOf`
(available) and `spec_cupLeft_cupProductOf`. No binder remains. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    HodgeDecomposition X :=
  spec_hodgeDecomposition_of_cupLeft_alone X (torusCohomology_cupProductOf X)
    (spec_cupLeft_cupProductOf X)

end HodgeLean.Adapters

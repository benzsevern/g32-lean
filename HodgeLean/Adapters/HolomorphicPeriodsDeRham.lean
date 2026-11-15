import HodgeLean.Adapters.HolomorphicPeriodsDeRhamProofs

/-! # The de Rham theorem for the integration cocycle: frozen specification

Inputs stage 4k (`docs/specs/HolomorphicPeriodsDeRham.md`), the last stage of step 4 of the route
to `F^1_B ≤ complexHolomorphicH1 X`. Stage 4j reduced step 4 to one purely complex binder
`hderham`: the complex comparison `G = fieldToDeRhamCohomology ℂ X 1 ∘ singularToFieldCohomology ℂ X 1`
sends the class of the integration cocycle `σ ↦ ∫_σ θ` of a closed global holomorphic `1`-form `θ`
to `c'` times the de Rham class of `θ`, for some `c' ≠ 0`. This stage states `hderham` with
`c' = 1` (statement 12) and splits it into small statements along two-term resolutions of `ℂ`:
`T = [Ω^0 → Ω^1_cl]` (closed forms) and `T' = [Ω^0 → Ω^0/ℂ]` (local primitives), with
`ℂ[0] → T' → T → Ω•` and the integration map `T' → S•` to the singular cochain resolution.

Claimed:
* for smooth integral `X`: `ℂ[0] → T` and `T → Ω•` are quasi-isomorphisms and compose to upstream's
  `ℂ[0] → Ω•`; `Ω^0/ℂ → Ω^1_cl`, `[f] ↦ df`, is an isomorphism of sheaves; `ℂ[0] → T'` is a
  quasi-isomorphism and composes with `T' → T` to `ℂ[0] → T`; `ℂ[0] → T'` composed with the
  integration map `T' → S•` is upstream's `ℂ[0] → S•`;
* for smooth integral `X`: every closed global holomorphic `1`-form has a global primitive class in
  `Ω^0/ℂ`; the global section of the singular cochain sheaf of a cochain is its sheafification
  germ; and the complex comparison sends the class of a singular cocycle whose global section is
  the integration of a global primitive class `θ'` to the de Rham class of `dθ'`;
* for abelian `X`: the global section of the integration cocycle of `θ` is the integration of any
  global primitive class of `θ` (the sheaf-level form of stage 4j's local primitive statement);
  hence the complex comparison of the class of the integration cocycle of `θ` is the de Rham class
  of `θ`, which is stage 4j's binder `hderham` with `c' = 1`.

Not claimed: any statement in degrees above one; the integration map on `T` itself (it is the
integration map on `T'` through the inverse of `T' → T`, an isomorphism by the statements here);
path integrals of closed forms on non-abelian `X`; the values of stage 4j's constants `q` and `c`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped Simplicial

namespace HodgeLean.Adapters

/-- For smooth integral `X`, the map `ℂ[0] → T = [Ω^0 → Ω^1_cl]` is a quasi-isomorphism: the
holomorphic Poincaré lemma in degrees `0` (a holomorphic function with `df = 0` is locally
constant) and `1` (a closed holomorphic `1`-form is locally `df`).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3 (holomorphic Poincaré
lemma); upstream `constantsToHolomorphicDeRhamComplex_quasiIso`. -/
theorem spec_constantsToClosedFormComplex_quasiIso (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (constantsToClosedFormComplex X) :=
  spec_constantsToClosedFormComplex_quasiIso_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    QuasiIsoAt (constantsToClosedFormComplex X) 1 :=
  (spec_constantsToClosedFormComplex_quasiIso X).quasiIsoAt 1

/-- For smooth integral `X`, `ℂ[0] → T` followed by the inclusion `T → Ω•` is upstream's map
`ℂ[0] → Ω•`.
Source: upstream `constantsToHolomorphicDeRhamComplexInt`; Mathlib's
`HomologicalComplex.extendMap_comp` and `HomologicalComplex.mkHomFromDouble_f₀`. -/
theorem spec_constantsToClosedFormComplex_comp_toDeRham (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    constantsToClosedFormComplex X ≫ closedFormComplexToDeRham X =
      constantsToHolomorphicDeRhamComplexInt X :=
  spec_constantsToClosedFormComplex_comp_toDeRham_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : ComplexConstantCohomology X n) :
    hypercohomologyMap X (closedFormComplexToDeRham X) n
        (hypercohomologyMap X (constantsToClosedFormComplex X) n α) =
      hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n α := by
  rw [← hypercohomologyMap_comp_apply, spec_constantsToClosedFormComplex_comp_toDeRham]

/-- For smooth integral `X`, the inclusion `T = [Ω^0 → Ω^1_cl] → Ω•` is a quasi-isomorphism: both
complexes resolve `ℂ` (statement `spec_constantsToClosedFormComplex_quasiIso` and the holomorphic
Poincaré lemma), compatibly with the maps from `ℂ[0]`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3; Mathlib's
`quasiIso_of_comp_left` (two out of three). -/
theorem spec_closedFormComplexToDeRham_quasiIso (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (closedFormComplexToDeRham X) :=
  spec_closedFormComplexToDeRham_quasiIso_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    QuasiIsoAt (closedFormComplexToDeRham X) 2 :=
  (spec_closedFormComplexToDeRham_quasiIso X).quasiIsoAt 2

/-- For smooth integral `X`, the exterior derivative `Ω^0/ℂ → Ω^1_cl`, `[f] ↦ df`, is an isomorphism
of sheaves: injective because a holomorphic function with `df = 0` is locally constant, surjective
because a closed holomorphic `1`-form is locally exact.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3; upstream
`exists_local_holomorphicForm_eq_constant` and `exists_local_holomorphicForm_primitive`. -/
theorem spec_primitiveQuotientToClosedOneForm_isIso (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    IsIso (primitiveQuotientToClosedOneForm X) :=
  spec_primitiveQuotientToClosedOneForm_isIso_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    Mono (primitiveQuotientToClosedOneForm X) := by
  have := spec_primitiveQuotientToClosedOneForm_isIso X
  infer_instance

/-- For smooth integral `X`, `ℂ[0] → T' = [Ω^0 → Ω^0/ℂ]` followed by the comparison `T' → T` is
`ℂ[0] → T`.
Source: Mathlib's `HomologicalComplex.extendMap_comp` and `HomologicalComplex.mkHomFromDouble_f₀`. -/
theorem spec_constantsToPrimitiveComplex_comp (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    constantsToPrimitiveComplex X ≫ primitiveComplexToClosedFormComplex X =
      constantsToClosedFormComplex X :=
  spec_constantsToPrimitiveComplex_comp_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : ComplexConstantCohomology X n) :
    hypercohomologyMap X (primitiveComplexToClosedFormComplex X) n
        (hypercohomologyMap X (constantsToPrimitiveComplex X) n α) =
      hypercohomologyMap X (constantsToClosedFormComplex X) n α := by
  rw [← hypercohomologyMap_comp_apply, spec_constantsToPrimitiveComplex_comp]

/-- For smooth integral `X`, the map `ℂ[0] → T' = [Ω^0 → Ω^0/ℂ]` is a quasi-isomorphism: the
complex `T'` has `H^1 = 0` by construction and `H^0 = ` the image of `ℂ`, so this is injectivity of
`ℂ → Ω^0` (the holomorphic Poincaré lemma in degree `0`).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3; upstream
`constantsToHolomorphicDeRhamComplex_quasiIsoAt_zero`. -/
theorem spec_constantsToPrimitiveComplex_quasiIso (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (constantsToPrimitiveComplex X) :=
  spec_constantsToPrimitiveComplex_quasiIso_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    QuasiIsoAt (constantsToPrimitiveComplex X) 0 :=
  (spec_constantsToPrimitiveComplex_quasiIso X).quasiIsoAt 0

/-- For smooth integral `X`, `ℂ[0] → T'` followed by the integration map `T' → S•` is upstream's
map `ℂ[0] → S•` from constants to the singular cochain resolution: a constant, read as a
holomorphic function, has its constant value on every point.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15; upstream
`constantsToSingularCochainComplexInt` and `chartEvaluation_ofConstant`;
`constantsToHolomorphicDeRhamZeroSheaf_comp_functionValueSheafMap` (degree `0`, proved in
`HodgeLean.Adapters.HolomorphicPeriodsDeRhamDefs`). -/
theorem spec_constantsToPrimitiveComplex_comp_toSingular (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    constantsToPrimitiveComplex X ≫ primitiveComplexToSingular X =
      constantsToSingularCochainComplexInt X ℂ :=
  spec_constantsToPrimitiveComplex_comp_toSingular_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : ComplexConstantCohomology X n) :
    hypercohomologyMap X (primitiveComplexToSingular X) n
        (hypercohomologyMap X (constantsToPrimitiveComplex X) n α) =
      hypercohomologyMap X (constantsToSingularCochainComplexInt X ℂ) n α := by
  rw [← hypercohomologyMap_comp_apply, spec_constantsToPrimitiveComplex_comp_toSingular]
  rfl

/-- For smooth integral `X`, every closed global holomorphic `1`-form `θ` is `dθ'` for a global
section `θ'` of `Ω^0/ℂ` (a compatible family of local primitives modulo constants).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3;
`spec_primitiveQuotientToClosedOneForm_isIso` and left exactness of global sections (Hartshorne,
*Algebraic Geometry*, II.1.8). -/
theorem spec_exists_globalPrimitive_of_closed (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (hθ : globalHolomorphicDifferential X 1 θ = 0) :
    ∃ θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X),
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).map
        (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = θ :=
  spec_exists_globalPrimitive_of_closed_aux X θ hθ

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) :
    ∃ θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X),
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).map
        (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = cycleOneForm X z := by
  have h : cycleOneForm X z ∈ closedGlobalHolomorphicOneForms X := by
    rw [← spec_range_cycleOneForm X]
    exact ⟨z, rfl⟩
  exact spec_exists_globalPrimitive_of_closed X _ h

/-- For smooth integral `X`, the global section `globalCochainSection X n φ` of the singular cochain
sheaf `S^n` (built through upstream's double-plus construction, as in stage 3c) is the germ family
of `φ`: the sheafification unit applied to `φ` read on the top open.
Source: Mathlib's `toSheafify_plusPlusIsoSheafify_hom` (the double-plus construction and the chosen
sheafification agree compatibly with their units); upstream
`topOpenToGlobalSingularCochainSheafComplex`. -/
theorem spec_globalCochainSection_eq_toSheafify (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cochain ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) n) :
    globalCochainSection X n φ =
      ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (AlgebraicTopology.Singular.singularCochainPresheaf ℂ (TopCat.of (ComplexPoint X)) n)).app
          (op ⊤)).hom
        (((AlgebraicTopology.Singular.singularCochainComplexIsoTopOpen ℂ
          (TopCat.of (ComplexPoint X))).hom.f n).hom φ) :=
  spec_globalCochainSection_eq_toSheafify_aux X n φ

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cochain ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) n)
    (hφ : ((AlgebraicTopology.Singular.singularCochainComplexIsoTopOpen ℂ
      (TopCat.of (ComplexPoint X))).hom.f n).hom φ = 0) :
    globalCochainSection X n φ = 0 := by
  rw [spec_globalCochainSection_eq_toSheafify, hφ]
  exact map_zero _

/-- **The sheaf-level local primitive statement.** For abelian `X`, a global holomorphic `1`-form
`θ` and a global section `θ'` of `Ω^0/ℂ` with `dθ' = θ`: the global section of the singular cochain
sheaf `S^1` of the integration cocycle of `θ` is the integration of `θ'` (on a small open where
`θ'` is the class of a primitive `f`, both are the cochain `σ ↦ f(σ(1)) - f(σ(0))`).
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15; Rudin, *Real and Complex
Analysis*, 3rd ed., §10.38 (integrals of closed forms through local primitives); stage 4j
`spec_exists_local_integration_primitive` and stage 4f `spec_expPullback_eq_expPullback_zero`. -/
theorem spec_globalCochainSection_singularIntegrationCochain (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (θ : GlobalHolomorphicForm X 1)
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (h : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = θ) :
    globalCochainSection X 1 (singularIntegrationCochain X (dim X.left) θ) =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ' :=
  spec_globalCochainSection_singularIntegrationCochain_aux X θ θ' h

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (h : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = 0) :
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ' =
      globalCochainSection X 1 (singularIntegrationCochain X (dim X.left) 0) :=
  (spec_globalCochainSection_singularIntegrationCochain X 0 θ' h).symm

/-- **The comparison through `T'`.** For smooth integral `X`, a global section `θ'` of `Ω^0/ℂ` with
`dθ'` the form of a degree-one cycle `z` of `Γ(F^1 Ω•)`, and a complex singular cocycle `Ψ` whose
global section is the integration of `θ'`: the complex comparison sends `[Ψ]` to the de Rham class
of `z`. The proof is the naturality of the edge map along `T' → S•` and `T' → Ω•`, with
`ℂ[0] → T'` a quasi-isomorphism.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1–III.3 (comparison of acyclic resolutions);
Bott–Tu, *Differential Forms in Algebraic Topology*, §15; stage 3c
`globalSectionsToHypercohomology_naturality`; statements
`spec_constantsToPrimitiveComplex_quasiIso`, `spec_constantsToPrimitiveComplex_comp`,
`spec_constantsToClosedFormComplex_comp_toDeRham` and
`spec_constantsToPrimitiveComplex_comp_toSingular`. -/
theorem spec_deRham_singularToFieldCohomology_of_primitive (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (hz : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = cycleOneForm X z)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : globalCochainSection X 1 Ψ.1 =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ') :
    fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1
        (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ)) =
      cycleDeRhamClass X z :=
  spec_deRham_singularToFieldCohomology_of_primitive_aux X z θ' hz Ψ hΨ

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (hz : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = cycleOneForm X z)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : globalCochainSection X 1 Ψ.1 =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ') :
    fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1
        (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ)) ∈
      F^1 H_dR^((1 : ℕ) : ℤ)(X) := by
  rw [spec_deRham_singularToFieldCohomology_of_primitive X z θ' hz Ψ hΨ]
  exact ⟨_, rfl⟩

/-- **Stage 4j's `hderham`, with `c' = 1`.** For abelian `X` and a degree-one cycle `z` of
`Γ(F^1 Ω•)`: the complex comparison (singular to sheaf to de Rham) sends the class of the
integration cocycle `σ ↦ ∫_σ θ` of the closed global holomorphic `1`-form `θ` of `z` to the de Rham
class of `z`. This is the de Rham theorem for the integration cocycle.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15 (de Rham theorem); statements
`spec_exists_globalPrimitive_of_closed`, `spec_globalCochainSection_singularIntegrationCochain`
and `spec_deRham_singularToFieldCohomology_of_primitive`; `spec_range_cycleOneForm`. -/
theorem spec_deRham_singularIntegrationCochain (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z)) :
    fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1
        (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ)) =
      cycleDeRhamClass X z :=
  spec_deRham_singularIntegrationCochain_aux X z Ψ hΨ

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X := by
  obtain ⟨c, hsing⟩ := spec_hsing_of_deRham X 1 one_ne_zero fun z Ψ hΨ ↦ by
    rw [one_smul]
    exact spec_deRham_singularIntegrationCochain X z Ψ hΨ
  obtain ⟨s, -, hloop⟩ := spec_periods_of_cohomologyBaseChange X c hsing
  exact spec_comap_hodgeFiltration_one_le_of_periods X (s * c)
    (spec_periods_of_holomorphicPathIntegral X (s * c) hloop)

end HodgeLean.Adapters

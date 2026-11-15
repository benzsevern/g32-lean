import HodgeLean.Adapters.HolomorphicPeriodsComparisonProofs

/-! # The de Rham comparison for the integration cocycle: frozen specification

Inputs stage 4j (`docs/specs/HolomorphicPeriodsComparison.md`), the next stage of step 4 of the
route to `F^1_B ≤ complexHolomorphicH1 X`. Stage 4i reduced step 4 to one binder `hsing`: if the
Betti–de Rham comparison sends `ω` to the class of the closed global holomorphic `1`-form `θ`, the
base change to `ℂ` of the rational singular class of `ω` (through `cupComparison`) is `c` times the
class of the integration cocycle `σ ↦ ∫_σ θ`. This stage removes every rational structure from that
binder: it proves (as frozen statements) that the rational side of `hsing` is a nonzero multiple of
`bettiDeRhamHQ` after the complex comparison, and replaces `hsing` by the purely complex binder
`hderham`, the de Rham comparison of the class of the integration cocycle itself.

Claimed:
* for smooth integral `X`: the complex comparison `fieldToDeRhamCohomology ℂ X n` is bijective,
  and its composite with the coefficient change `H^n(X; ℚ) → H^n(X; ℂ)` is
  `fieldToDeRhamCohomology ℚ X n`;
* for every simplicial set: base change of rational cochains to complex cochains commutes with the
  coboundary; for every space: the universal-coefficient base change `cohomologyBaseChange` of
  `1 ⊗ [ψ]` is the class of the base-changed cocycle;
* for smooth integral `X`: the named comparison `singularToFieldCohomology` commutes with the
  coefficient change from `ℚ` to `ℂ`;
* for smooth projective integral `X`: `singularToFieldCohomology ℚ X n ∘ cupComparison X n` is a
  nonzero rational multiple of the identity, hence the complex comparison of the base change of
  the singular class of `ω` is that multiple of `bettiDeRhamHQ X n ω`;
* for abelian `X`: every point has an open neighbourhood with a continuous section `s` of `exp` on
  which the integration cocycle of `θ` is the singular coboundary of the local primitive
  `y ↦ exp^*θ(0) (s y)`, and two such sections differ by a locally constant function on the
  overlap;
* for abelian `X`: the implication from the complex binder `hderham` (the complex comparison of the
  class of the integration cocycle of `θ` is `c'` times the de Rham class of `θ`, `c' ≠ 0`) to
  stage 4i's `hsing`, and the converse implication from `hsing` with `c ≠ 0` to `hderham`.

Not claimed: `hderham` itself (the de Rham theorem for the integration cocycle, open stage 4k), the
values of the constants `q`, `c`, `c'` (sign and normalization conventions of upstream's
comparisons are not computed), any map of complexes of sheaves from holomorphic forms to singular
cochains, Čech cohomology, or any statement for non-abelian `X` beyond the coefficient changes.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped Simplicial TensorProduct Topology

namespace HodgeLean.Adapters

/-- For smooth integral `X`, upstream's comparison `fieldToDeRhamCohomology ℂ X n` from the sheaf
cohomology `H^n(X(ℂ); ℂ)` of the constant sheaf to holomorphic de Rham cohomology is bijective:
the map `ℂ[0] → Ω•` is a quasi-isomorphism (holomorphic Poincaré lemma), and the coefficient map
`ℂ → ℂ` it starts with is the identity.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3 (holomorphic Poincaré lemma)
and Ch. 3 §5 (hypercohomology of a resolution); upstream
`constantsToHolomorphicDeRhamComplexInt_quasiIso`. -/
theorem spec_fieldToDeRhamCohomology_complex_bijective (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    Function.Bijective (fieldToDeRhamCohomology ℂ X n) :=
  spec_fieldToDeRhamCohomology_complex_bijective_aux X n

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    Function.Injective (fieldToDeRhamCohomology ℂ X 1) :=
  (spec_fieldToDeRhamCohomology_complex_bijective X 1).injective

/-- For smooth integral `X`, the rational comparison `fieldToDeRhamCohomology ℚ X n` factors through
the coefficient change `H^n(X(ℂ); ℚ) → H^n(X(ℂ); ℂ)` followed by the complex comparison.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, II.4 (functoriality in the coefficients);
upstream `fieldToHolomorphicDeRhamComplexInt` (`ℚ[0] → ℂ[0] → Ω•`) and `hypercohomologyMap`. -/
theorem spec_fieldToDeRhamCohomology_fieldCohomologyToComplex (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) (v : H^n(X; ℚ)) :
    fieldToDeRhamCohomology ℂ X n (fieldCohomologyToComplex X n v) =
      fieldToDeRhamCohomology ℚ X n v :=
  spec_fieldToDeRhamCohomology_fieldCohomologyToComplex_aux X n v

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℕ) (v : H^n(X; ℚ))
    (hv : fieldToDeRhamCohomology ℚ X n v ≠ 0) : fieldCohomologyToComplex X n v ≠ 0 := by
  intro h
  apply hv
  rw [← spec_fieldToDeRhamCohomology_fieldCohomologyToComplex X n v, h, map_zero]

/-- Base change of rational singular cochains to complex coefficients commutes with the
coboundary.
Source: Hatcher, *Algebraic Topology*, §3.1 (the coboundary is `ψ ↦ ψ ∘ ∂`, and change of
coefficients is composition with `ℚ → ℂ`); stage 4i `spec_simplexCochain_chainOfSimplex`. -/
theorem spec_coboundary_cochainBaseChange (Y : SSet.{0}) (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cochain ℚ Y n) :
    AlgebraicTopology.Simplicial.coboundary ℂ n (cochainBaseChange Y n ψ) =
      cochainBaseChange Y (n + 1) (AlgebraicTopology.Simplicial.coboundary ℚ n ψ) :=
  spec_coboundary_cochainBaseChange_aux Y n ψ

example (Y : SSet.{0}) (n : ℕ) (ψ : AlgebraicTopology.Simplicial.Cochain ℚ Y n)
    (τ : Y _⦋n + 1⦌) :
    AlgebraicTopology.Simplicial.coboundary ℂ n (cochainBaseChange Y n ψ)
        (AlgebraicTopology.Simplicial.chainOfSimplex ℂ τ) =
      (AlgebraicTopology.Simplicial.coboundary ℚ n ψ
        (AlgebraicTopology.Simplicial.chainOfSimplex ℚ τ) : ℂ) := by
  rw [spec_coboundary_cochainBaseChange, cochainBaseChange, spec_simplexCochain_chainOfSimplex]

/-- For every space `Y`, the universal-coefficient base change `cohomologyBaseChange Y n` sends
`1 ⊗ [ψ]` to the class of any complex cocycle whose cochain is the base change of `ψ`.
Source: Hatcher, *Algebraic Topology*, §3.1 (universal coefficients, naturality in the
coefficients); upstream `cohomologyEquivDualHomology` and the port of `qToCHomology_isBaseChange`;
stage 4i `cohomologyBaseChange`. -/
theorem spec_cohomologyBaseChange_tmul_cohomologyClass (Y : TopCat.{0}) (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) n)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj Y) n)
    (h : Ψ.1 = cochainBaseChange _ n ψ.1) :
    cohomologyBaseChange Y n (1 ⊗ₜ Singular.cohomologyClass Y n ψ) =
      Singular.cohomologyClass Y n Ψ :=
  spec_cohomologyBaseChange_tmul_cohomologyClass_aux Y n ψ Ψ h

example (Y : TopCat.{0}) (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) n)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj Y) n)
    (h : Ψ.1 = cochainBaseChange _ n ψ.1) (a : ℂ) :
    cohomologyBaseChange Y n (a ⊗ₜ Singular.cohomologyClass Y n ψ) =
      a • Singular.cohomologyClass Y n Ψ := by
  rw [← spec_cohomologyBaseChange_tmul_cohomologyClass Y n ψ Ψ h, ← map_smul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- For smooth integral `X`, the named comparison `singularToFieldCohomology` commutes with the
coefficient change from `ℚ` to `ℂ`: on singular cohomology, base change of cocycles; on sheaf
cohomology, `fieldCohomologyToComplex`.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1 (the comparison is natural in the
coefficients); upstream `globalSectionsToHypercohomology_naturality` (stage 3c `EdgeMap.lean`) and
`hypercohomologyMap_comp_apply`. -/
theorem spec_singularToFieldCohomology_cochainBaseChange (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) n)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) n)
    (h : Ψ.1 = cochainBaseChange _ n ψ.1) :
    singularToFieldCohomology ℂ X n (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) n Ψ) =
      fieldCohomologyToComplex X n
        (singularToFieldCohomology ℚ X n
          (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) n ψ)) :=
  spec_singularToFieldCohomology_cochainBaseChange_aux X n ψ Ψ h

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) n)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) n)
    (h : Ψ.1 = cochainBaseChange _ n ψ.1)
    (hψ : singularToFieldCohomology ℚ X n
      (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) n ψ) = 0) :
    singularToFieldCohomology ℂ X n
      (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) n Ψ) = 0 := by
  rw [spec_singularToFieldCohomology_cochainBaseChange X n ψ Ψ h, hψ, map_zero]

/-- For smooth projective integral `X`, the named rational comparison
`singularToFieldCohomology ℚ X n` (singular to sheaf, through the edge map) inverts `cupComparison`
(sheaf to singular, upstream's comparison through an injective resolution, rescaled by
`normalizedEquiv`) up to a nonzero rational factor.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1 and II.4 (the comparison of sheaf and
singular cohomology does not depend on the acyclic resolution used to compute it); stage 3c
`singularToFieldCohomology`; `cupComparison` and `Foundations.Singular.normalizedEquiv`. -/
theorem spec_singularToFieldCohomology_cupComparison (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    ∃ q : ℚ, q ≠ 0 ∧ ∀ v : HQ X n,
      singularToFieldCohomology ℚ X n (cupComparison X n v) = q • HQ.linearEquiv X n v :=
  spec_singularToFieldCohomology_cupComparison_aux X n

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ)
    (v : HQ X n) (h : singularToFieldCohomology ℚ X n (cupComparison X n v) = 0) : v = 0 := by
  obtain ⟨q, hq0, hq⟩ := spec_singularToFieldCohomology_cupComparison X n
  rw [hq, smul_eq_zero, or_iff_right hq0] at h
  exact (HQ.linearEquiv X n).map_eq_zero_iff.mp h

/-- For smooth projective integral `X`, the complex comparison (singular to sheaf to de Rham) of
the base change to `ℂ` of the singular class of `ω` is a universal nonzero rational multiple of
`bettiDeRhamHQ X n ω`. This is the rational half of stage 4i's `hsing`, with no form or integral
in it.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1 (naturality in the coefficients);
`spec_cohomologyBaseChange_tmul_cohomologyClass`,
`spec_singularToFieldCohomology_cochainBaseChange`, `spec_singularToFieldCohomology_cupComparison`
and `spec_fieldToDeRhamCohomology_fieldCohomologyToComplex`. -/
theorem spec_deRham_singularToFieldCohomology_cohomologyBaseChange (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    ∃ q : ℚ, q ≠ 0 ∧ ∀ ω : ℂ ⊗[ℚ] HQ X n,
      fieldToDeRhamCohomology ℂ X n (singularToFieldCohomology ℂ X n
          (cohomologyBaseChange (TopCat.of (ComplexPoint X)) n
            (LinearMap.baseChange ℂ (cupComparison X n).toLinearMap ω))) =
        (q : ℂ) • bettiDeRhamHQ X n ω :=
  spec_deRham_singularToFieldCohomology_cohomologyBaseChange_aux X n

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ)
    (ω : ℂ ⊗[ℚ] HQ X n) :
    fieldToDeRhamCohomology ℂ X n (singularToFieldCohomology ℂ X n
        (cohomologyBaseChange (TopCat.of (ComplexPoint X)) n
          (LinearMap.baseChange ℂ (cupComparison X n).toLinearMap ω))) = 0 ↔
      bettiDeRhamHQ X n ω = 0 := by
  obtain ⟨q, hq0, hq⟩ := spec_deRham_singularToFieldCohomology_cohomologyBaseChange X n
  rw [hq, smul_eq_zero, or_iff_right (by exact_mod_cast hq0)]

/-- For abelian `X`, a global holomorphic `1`-form `θ` and a point `x` of `X(ℂ)`: there is an open
neighbourhood `U` of `x` with a continuous section `s` of `exp : ℂ^d → X(ℂ)` on `U`, and on every
singular `1`-simplex inside `U` the integration cocycle of `θ` is the singular coboundary of the
local primitive `y ↦ exp^*θ(0) (s y)` (its value at the end vertex minus its value at the start
vertex).
Source: Hatcher, *Algebraic Topology*, §1.3 (local sections of a covering map); Rudin, *Real and
Complex Analysis*, 3rd ed., §10.38 (local primitives of closed forms); stage 4h
`spec_isCoveringMap_complexExponential` and `spec_expLiftDisplacement_eq`. -/
theorem spec_exists_local_integration_primitive (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (x : ComplexPoint X) :
    ∃ (U : Set (ComplexPoint X)) (s : ComplexPoint X → Fin d → ℂ),
      IsOpen U ∧ x ∈ U ∧ ContinuousOn s U ∧
        (∀ y ∈ U, (complexExponential X d (s y)).toMul = y) ∧
        ∀ σ : (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) _⦋1⦌,
          (∀ t, simplexPath σ t ∈ U) →
            singularIntegrationCochain X d θ (AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ) =
              expPullback X d θ 0 (s (simplexPath σ 1)) -
                expPullback X d θ 0 (s (simplexPath σ 0)) :=
  spec_exists_local_integration_primitive_aux X d θ x

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (x : ComplexPoint X) :
    ∃ U : Set (ComplexPoint X), IsOpen U ∧ x ∈ U ∧
      ∀ σ : (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) _⦋1⦌,
        (∀ t, simplexPath σ t ∈ U) → simplexPath σ 1 = simplexPath σ 0 →
          singularIntegrationCochain X d θ
            (AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ) = 0 := by
  obtain ⟨U, s, hU, hx, -, -, h⟩ := spec_exists_local_integration_primitive X d θ x
  exact ⟨U, hU, hx, fun σ hσ hloop ↦ by rw [h σ hσ, hloop, sub_self]⟩

/-- For abelian `X`, two continuous sections `s`, `s'` of `exp : ℂ^d → X(ℂ)` on open sets `U`, `U'`
differ by a locally constant function on `U ∩ U'`: the difference takes values in the discrete
kernel `Λ` of `exp`. With statement `spec_exists_local_integration_primitive`, the local primitives
of `θ` differ on overlaps by the constants `exp^*θ(0)(λ)`, the Čech `1`-cocycle of `θ`.
Source: Hatcher, *Algebraic Topology*, §1.3 (lifts along a covering map); Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., §1.1 (`ker exp = Λ` is discrete); S12
`discrete_complexExponentialLattice`. -/
theorem spec_eventually_sub_eq_of_complexExponential (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (U U' : Set (ComplexPoint X)) (s s' : ComplexPoint X → Fin d → ℂ)
    (hU : IsOpen U) (hU' : IsOpen U') (hs : ContinuousOn s U) (hs' : ContinuousOn s' U')
    (he : ∀ y ∈ U, (complexExponential X d (s y)).toMul = y)
    (he' : ∀ y ∈ U', (complexExponential X d (s' y)).toMul = y)
    (y : ComplexPoint X) (hy : y ∈ U ∩ U') :
    ∀ᶠ y' in 𝓝 y, s y' - s' y' = s y - s' y :=
  spec_eventually_sub_eq_of_complexExponential_aux X d U U' s s' hU hU' hs hs' he he' y hy

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (U U' : Set (ComplexPoint X)) (s s' : ComplexPoint X → Fin d → ℂ)
    (hU : IsOpen U) (hU' : IsOpen U') (hs : ContinuousOn s U) (hs' : ContinuousOn s' U')
    (he : ∀ y ∈ U, (complexExponential X d (s y)).toMul = y)
    (he' : ∀ y ∈ U', (complexExponential X d (s' y)).toMul = y)
    (y : ComplexPoint X) (hy : y ∈ U ∩ U') :
    ∀ᶠ y' in 𝓝 y, expPullback X d θ 0 (s y') - expPullback X d θ 0 (s' y') =
      expPullback X d θ 0 (s y) - expPullback X d θ 0 (s' y) := by
  filter_upwards [spec_eventually_sub_eq_of_complexExponential X d U U' s s' hU hU' hs hs' he he'
    y hy] with y' h
  rw [← map_sub, ← map_sub, h]

/-- **Stage 4i's `hsing` from the complex binder `hderham`.** For abelian `X`, if for some `c' ≠ 0`
the complex comparison (singular to sheaf to de Rham) of the class of the integration cocycle of
every closed global holomorphic `1`-form `θ` is `c'` times the de Rham class of `θ`, then there is
a constant `c` for which stage 4i's binder `hsing` holds; the conclusion after `∃ c,` has exactly
the type of `hsing` in `spec_periods_of_cohomologyBaseChange`. `hderham` involves no rational
structure, no `cupComparison` and no `cohomologyBaseChange`.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15 (de Rham theorem);
`spec_deRham_singularToFieldCohomology_cohomologyBaseChange`,
`spec_fieldToDeRhamCohomology_complex_bijective` and stage 3c
`spec_singularToFieldCohomology_bijective`. -/
theorem spec_hsing_of_deRham (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (c' : ℂ) (hc' : c' ≠ 0)
    (hderham : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
        (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
          (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1),
      Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
        fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1
            (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ)) =
          c' • cycleDeRhamClass X z) :
    ∃ c : ℂ, ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z →
        ∀ Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
            (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1,
          Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
            cohomologyBaseChange (TopCat.of (ComplexPoint X)) 1
                (LinearMap.baseChange ℂ (cupComparison X 1).toLinearMap ω) =
              c • Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ :=
  spec_hsing_of_deRham_aux X c' hc' hderham

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (c' : ℂ) (hc' : c' ≠ 0)
    (hderham : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
        (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
          (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1),
      Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
        fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1
            (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ)) =
          c' • cycleDeRhamClass X z) :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X := by
  obtain ⟨c, hsing⟩ := spec_hsing_of_deRham X c' hc' hderham
  obtain ⟨s, -, hloop⟩ := spec_periods_of_cohomologyBaseChange X c hsing
  exact spec_comap_hodgeFiltration_one_le_of_periods X (s * c)
    (spec_periods_of_holomorphicPathIntegral X (s * c) hloop)

/-- **The converse: `hderham` from `hsing`.** For abelian `X`, if stage 4i's `hsing` holds with a
constant `c ≠ 0`, then `hderham` holds with some `c' ≠ 0`. So `hderham` is not stronger than
`hsing`; it is the same comparison with the rational structure removed.
Source: `spec_deRham_singularToFieldCohomology_cohomologyBaseChange`; stage 3c
`spec_bettiDeRhamIso_abelian` (surjectivity of `bettiDeRhamHQ X 1`). -/
theorem spec_deRham_of_hsing (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (c : ℂ) (hc : c ≠ 0)
    (hsing : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z →
        ∀ Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
            (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1,
          Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
            cohomologyBaseChange (TopCat.of (ComplexPoint X)) 1
                (LinearMap.baseChange ℂ (cupComparison X 1).toLinearMap ω) =
              c • Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ) :
    ∃ c' : ℂ, c' ≠ 0 ∧ ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
        (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
          (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1),
      Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
        fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1
            (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ)) =
          c' • cycleDeRhamClass X z :=
  spec_deRham_of_hsing_aux X c hc hsing

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (c : ℂ) (hc : c ≠ 0)
    (hsing : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z →
        ∀ Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
            (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1,
          Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
            cohomologyBaseChange (TopCat.of (ComplexPoint X)) 1
                (LinearMap.baseChange ℂ (cupComparison X 1).toLinearMap ω) =
              c • Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ) :
    ∃ c' : ℂ, c' ≠ 0 ∧ ∀ z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ),
      ∃ Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
          (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1,
        Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) ∧
        fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1
            (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ)) =
          c' • cycleDeRhamClass X z := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨c', hc', h⟩ := spec_deRham_of_hsing X c hc hsing
  exact ⟨c', hc', fun z ↦ ⟨⟨_, spec_coboundary_singularIntegrationCochain X (dim X.left)
    (cycleOneForm X z)⟩, rfl, h z _ rfl⟩⟩

end HodgeLean.Adapters

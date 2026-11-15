import HodgeLean.Adapters.HodgeDegreeOneAbelianProofs

/-! # The degree-one Hodge decomposition of an abelian `X`: frozen specification

Inputs stage 4l (`docs/specs/HodgeDegreeOneAbelian.md`). Stage 4k made
`F^1_B ≤ complexHolomorphicH1 X` a theorem for abelian `X`, where
`F^1_B = (F^1 H_dR^1).comap (bettiDeRhamHQ X 1)`. With stage 4b (`HodgeFilterLattice`) this gives
`F^1 ∩ conj F^1 = 0` and `dim F^1 H_dR^1 ≤ g`. The missing piece was the lower bound
`g ≤ dim F^1 H_dR^1`. This stage freezes it, through the invariant holomorphic `1`-forms: for every
covector `a` on `ℂ^g` there is a closed global holomorphic `1`-form `θ` with `exp^*θ = a`. Such a
`θ` is glued from the local forms `df`, where `f` is a local holomorphic function with
`d(f ∘ exp) = a`. Its class in `ℂ ⊗ HQ X 1` has the periods `c · a(λ)`, with the nonzero constant
`c` of the period formula of stages 4g–4k. So every class with complex-linear periods lies in
`F^1_B`.

Claimed:
* for abelian `X` (as the commutative group scheme of stages 4f–4j, of any relative dimension `d`):
  every point has an open neighbourhood `U` with a holomorphic `f` on `U` such that `f ∘ exp` has
  derivative `a` wherever `exp` lands in `U`; the local forms `df` of two such primitives agree on
  overlaps; they glue to a global holomorphic `1`-form restricting to each of them; and a global
  form restricting to such a `df` has `exp^*θ = a` over `U`;
* for smooth integral `X`: a global holomorphic `1`-form that is locally of the form `df` is closed;
* for abelian `X`: every covector `a` on `ℂ^g` is `exp^*θ(0)` for a closed global holomorphic
  `1`-form `θ`;
* for abelian `X`: the period formula of stage 4g holds with a nonzero constant; the implication
  from it, with a nonzero constant, to `complexHolomorphicH1 X ≤ F^1_B`;
* for abelian `X`: `F^1_B = complexHolomorphicH1 X`, `g ≤ dim F^1 H_dR^1`, and the Hodge
  decomposition in degree one, `DirectSum.IsInternal (deRhamHodgePiece X 1)`, with no hypothesis.

Not claimed: any degree above one, so not `HodgeDecomposition X`; any statement for non-abelian
`X`; a `ℂ`-module structure on global holomorphic `1`-forms or the value of the period constant.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- **Local invariant primitives.** For abelian `X`, a covector `a` on `ℂ^d` and a point `x` of
`X(ℂ)`: there are an open neighbourhood `U` of `x` and a holomorphic function `f` on `U` such that
`f ∘ exp` has derivative `a` at every `v` with `exp v ∈ U`. Take `U` the image of a small ball on
which `exp` is a biholomorphism, with holomorphic inverse `s`, and `f = a ∘ s`; then
`s (exp w) - w` is locally constant, with values in the discrete lattice `Λ`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.1
(`X(ℂ) = ℂ^g/Λ`); Hatcher, *Algebraic Topology*, §1.3 (local sections of a covering map);
`spec_complexExponential_localBiholomorph`, `spec_isCoveringMap_complexExponential` and
`spec_eventually_sub_eq_of_complexExponential`. -/
theorem spec_exists_local_expPrimitive (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (a : (Fin d → ℂ) →L[ℂ] ℂ) (x : ComplexPoint X) :
    ∃ (U : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ U)
      (f : OpenHolomorphicFunctions X d (op U)),
      ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U →
        HasFDerivAt (fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul) a v :=
  spec_exists_local_expPrimitive_aux X d a x

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (a : (Fin d → ℂ) →L[ℂ] ℂ) (v : Fin d → ℂ) :
    ∃ (U : Opens (TopCat.of (ComplexPoint X))) (f : OpenHolomorphicFunctions X d (op U)),
      HasFDerivAt (fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul) a v := by
  obtain ⟨U, hx, f, hf⟩ :=
    spec_exists_local_expPrimitive X d a (complexExponential X d v).toMul
  exact ⟨U, f, hf v hx⟩

/-- **Local primitives agree on overlaps.** For abelian `X` and a covector `a` on `ℂ^d`: if `f` on
`U` and `f'` on `U'` are local primitives of `a` (`f ∘ exp` and `f' ∘ exp` have derivative `a`
wherever `exp` lands in `U`, resp. `U'`), then `df` and `df'` agree on `U ⊓ U'`. The difference
`f - f'` has `(f - f') ∘ exp` with derivative `0`, so it is locally constant on `U ⊓ U'` (`exp`
has continuous local sections), and its chart derivatives vanish.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (`df = 0` for locally
constant `f`); upstream `chartEvaluationKernel` and `chartEvaluation_formRestriction`
(`HodgeConjecture/Definitions/AlgebraicGeometry/Hodge/AnalyticDifferentialForms.lean` at
`2ead713`); `spec_isCoveringMap_complexExponential`. -/
theorem spec_localExactOneForm_inf_eq (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (a : (Fin d → ℂ) →L[ℂ] ℂ) (U U' : Opens (TopCat.of (ComplexPoint X)))
    (f : OpenHolomorphicFunctions X d (op U)) (f' : OpenHolomorphicFunctions X d (op U'))
    (hf : ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U →
      HasFDerivAt (fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul) a v)
    (hf' : ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U' →
      HasFDerivAt (fun w ↦ extendedSection X d (op U') f' (complexExponential X d w).toMul) a v) :
    (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op
        (localExactOneForm X d U f) =
      (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op
        (localExactOneForm X d U' f') :=
  spec_localExactOneForm_inf_eq_aux X d a U U' f f' hf hf'

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (a : (Fin d → ℂ) →L[ℂ] ℂ) (U : Opens (TopCat.of (ComplexPoint X)))
    (f f' : OpenHolomorphicFunctions X d (op U))
    (hf : ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U →
      HasFDerivAt (fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul) a v)
    (hf' : ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U →
      HasFDerivAt (fun w ↦ extendedSection X d (op U) f' (complexExponential X d w).toMul) a v) :
    (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE (inf_le_left : U ⊓ U ≤ U)).op
        (localExactOneForm X d U f) =
      (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE (inf_le_right : U ⊓ U ≤ U)).op
        (localExactOneForm X d U f') :=
  spec_localExactOneForm_inf_eq X d a U U f f' hf hf'

/-- **Gluing.** For abelian `X` and a covector `a` on `ℂ^d`, there is a global holomorphic
`1`-form `θ` whose restriction to every open `U` carrying a local primitive `f` of `a` is `df`.
The local forms `df` of `spec_exists_local_expPrimitive` cover `X(ℂ)` and agree on overlaps by
`spec_localExactOneForm_inf_eq`, so they glue in the sheaf of holomorphic `1`-forms; the same
statement on `U ⊓ U_x` identifies the restriction to any other such `U`.
Source: Hartshorne, *Algebraic Geometry*, GTM 52, II.1 (the sheaf axiom); Mathlib's
`TopCat.Sheaf.existsUnique_gluing`; `spec_exists_local_expPrimitive` and
`spec_localExactOneForm_inf_eq`. -/
theorem spec_exists_globalForm_of_expPrimitive (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (a : (Fin d → ℂ) →L[ℂ] ℂ) :
    ∃ θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤),
      ∀ (U : Opens (TopCat.of (ComplexPoint X))) (f : OpenHolomorphicFunctions X d (op U)),
        (∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U →
          HasFDerivAt (fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul)
            a v) →
        (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
          localExactOneForm X d U f :=
  spec_exists_globalForm_of_expPrimitive_aux X d a

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (a : (Fin d → ℂ) →L[ℂ] ℂ) :
    ∃ θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤), ∀ x : ComplexPoint X,
      ∃ (U : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ U)
        (f : OpenHolomorphicFunctions X d (op U)),
        (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
          localExactOneForm X d U f := by
  obtain ⟨θ, hθ⟩ := spec_exists_globalForm_of_expPrimitive X d a
  refine ⟨θ, fun x ↦ ?_⟩
  obtain ⟨U, hx, f, hf⟩ := spec_exists_local_expPrimitive X d a x
  exact ⟨U, hx, f, hθ U f hf⟩

/-- **Locally exact forms are closed.** For smooth integral `X`, a global holomorphic `1`-form
that near every point is `df` for a local holomorphic function `f` is closed: `d` commutes with
restriction and with the sheafification unit, `d(df) = 0` already for Kähler forms, and a section
of a sheaf vanishing locally vanishes.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (`d ∘ d = 0`); Mathlib's
`Algebra.DeRham` and `toSheafify_naturality`; upstream `holomorphicDeRhamSheafDifferential`. -/
theorem spec_mem_closedGlobalHolomorphicOneForms_of_locallyExact (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (hθ : ∀ x : ComplexPoint X, ∃ (U : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ U)
      (f : OpenHolomorphicFunctions X (dim X.left) (op U)),
        (holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.map (homOfLE le_top).op θ =
          localExactOneForm X (dim X.left) U f) :
    θ ∈ closedGlobalHolomorphicOneForms X :=
  spec_mem_closedGlobalHolomorphicOneForms_of_locallyExact_aux X θ hθ

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (hθ : ∀ x : ComplexPoint X, ∃ (U : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ U)
      (f : OpenHolomorphicFunctions X (dim X.left) (op U)),
        (holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.map (homOfLE le_top).op θ =
          localExactOneForm X (dim X.left) U f) :
    ∃ z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ), cycleOneForm X z = θ := by
  have h : θ ∈ (cycleOneForm X).range := by
    rw [spec_range_cycleOneForm X]
    exact spec_mem_closedGlobalHolomorphicOneForms_of_locallyExact X θ hθ
  exact h

/-- **The value of a glued form.** For abelian `X`, a covector `a` on `ℂ^d`, and a global
holomorphic `1`-form `θ` whose restriction to `U` is `df` for a local primitive `f` of `a`:
`exp^*θ(v) = a` whenever `exp v ∈ U`. In the chart at `x = exp v`, the value of `df` is the
derivative of `f ∘ chart⁻¹`, and `exp^*θ(v)` composes it with the derivative of `chart ∘ exp`; by
the chain rule this is the derivative of `f ∘ exp`, which is `a`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (pullback of forms, chain
rule); `spec_globalFormValue_eq_chartEvaluation` and `expPullback`; upstream
`chartEvaluation_mk`. -/
theorem spec_expPullback_eq_of_localExactOneForm (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (a : (Fin d → ℂ) →L[ℂ] ℂ)
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (U : Opens (TopCat.of (ComplexPoint X))) (f : OpenHolomorphicFunctions X d (op U))
    (hf : ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U →
      HasFDerivAt (fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul) a v)
    (hθ : (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
      localExactOneForm X d U f)
    (v : Fin d → ℂ) (hv : (complexExponential X d v).toMul ∈ U) :
    expPullback X d θ v = a :=
  spec_expPullback_eq_of_localExactOneForm_aux X d a θ U f hf hθ v hv

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (a : (Fin d → ℂ) →L[ℂ] ℂ) (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (U : Opens (TopCat.of (ComplexPoint X))) (f : OpenHolomorphicFunctions X d (op U))
    (hf : ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U →
      HasFDerivAt (fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul) a v)
    (hθ : (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
      localExactOneForm X d U f)
    (v : Fin d → ℂ) (hv : (complexExponential X d v).toMul ∈ U) :
    expPullback X d θ 0 = a :=
  (spec_expPullback_eq_expPullback_zero X d θ v).symm.trans
    (spec_expPullback_eq_of_localExactOneForm X d a θ U f hf hθ v hv)

/-- **Invariant forms exist.** For abelian `X` of dimension `g`, every covector `a` on `ℂ^g` is
`exp^*θ(0)` for a closed global holomorphic `1`-form `θ` (the descent of the constant form `a`).
With stage 4f's `spec_eq_zero_of_expPullback_zero_eq_zero`, `θ ↦ exp^*θ(0)` is a bijection from
closed global holomorphic `1`-forms onto `Hom_ℂ(ℂ^g, ℂ)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.4
(`H^0(X, Ω^1)` is spanned by `dz_1, …, dz_g`); Mumford, *Abelian Varieties*, §4 (invariant
differentials); `spec_exists_globalForm_of_expPrimitive`,
`spec_mem_closedGlobalHolomorphicOneForms_of_locallyExact` and
`spec_expPullback_eq_of_localExactOneForm`, with `isCommMonObj_of_complexSelfProductIntegral`. -/
theorem spec_exists_closed_expPullback_eq (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (a : (Fin (dim X.left) → ℂ) →L[ℂ] ℂ) :
    ∃ θ ∈ closedGlobalHolomorphicOneForms X, expPullback X (dim X.left) θ 0 = a :=
  spec_exists_closed_expPullback_eq_aux X a

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    Function.Surjective
      (fun θ : closedGlobalHolomorphicOneForms X ↦ expPullback X (dim X.left) θ.1 0) := by
  intro a
  obtain ⟨θ, hθ, h⟩ := spec_exists_closed_expPullback_eq X a
  exact ⟨⟨θ, hθ⟩, h⟩

/-- **The period formula with a nonzero constant.** For abelian `X`, stage 4g's period formula
holds for some `c ≠ 0`. Stage 4k's chain (statement 12, stages 4j, 4i, 4h) gives it for some `c`.
If `g ≥ 1` and `c = 0`, a closed form `θ ≠ 0` (`spec_exists_closed_expPullback_eq`) has a nonzero
class (`spec_cycleDeRhamClass_injective_of_isProjective`), hence a nonzero Betti class, with all
periods `0`, which the injective period map rules out; if `g = 0`, every lattice vector is `0`
and the formula holds with `c = 1`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.1 and
§1.4; `spec_deRham_singularIntegrationCochain`, `spec_hsing_of_deRham`,
`spec_periods_of_cohomologyBaseChange`, `spec_periods_of_holomorphicPathIntegral` and
`spec_complexAbelianPeriod_restriction`. -/
theorem spec_exists_periods_ne_zero (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
        bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
          complexAbelianPeriod X ω l = c * ∫ᶜ x in Path.segment 0 (l : Fin (dim X.left) → ℂ),
            expPullback X (dim X.left) (cycleOneForm X z) x :=
  spec_exists_periods_ne_zero_aux X

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X := by
  obtain ⟨c, -, hper⟩ := spec_exists_periods_ne_zero X
  exact spec_comap_hodgeFiltration_one_le_of_periods X c hper

/-- **The reverse inclusion, from the period formula.** For abelian `X`, the implication from
stage 4g's period formula with a constant `c ≠ 0` to `complexHolomorphicH1 X ≤ F^1_B`. A class
`ω` with periods `f(λ)`, `f` complex linear, has the same periods as the Betti class of the form
`θ` with `exp^*θ(0) = c⁻¹ f` (`spec_exists_closed_expPullback_eq`, and
`spec_curveIntegral_segment_expPullback` for the integral), and the complexified period map is
injective.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.4 and
Theorem 1.4.1; `spec_exists_closed_expPullback_eq`, `spec_range_cycleOneForm`,
`spec_bettiDeRhamIso_abelian` and `spec_complexAbelianPeriod_restriction`. -/
theorem spec_le_comap_hodgeFiltration_one_of_periods (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (c : ℂ) (hc : c ≠ 0)
    (hper : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
        complexAbelianPeriod X ω l = c * ∫ᶜ x in Path.segment 0 (l : Fin (dim X.left) → ℂ),
          expPullback X (dim X.left) (cycleOneForm X z) x) :
    complexHolomorphicH1 X ≤ (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) :=
  spec_le_comap_hodgeFiltration_one_of_periods_aux X c hc hper

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    complexHolomorphicH1 X ≤ (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) := by
  obtain ⟨c, hc, hper⟩ := spec_exists_periods_ne_zero X
  exact spec_le_comap_hodgeFiltration_one_of_periods X c hc hper

/-- **`F^1_B` is the holomorphic summand.** For abelian `X`, the pullback of `F^1 H_dR^1` along
the Betti–de Rham map is `complexHolomorphicH1 X`, with no hypothesis: stage 4k's inclusion and
`spec_le_comap_hodgeFiltration_one_of_periods` with `spec_exists_periods_ne_zero`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Theorem 1.4.1
(`H^{1,0} = H^0(X, Ω^1)`); `spec_comap_hodgeFiltration_one_le_of_periods`,
`spec_exists_periods_ne_zero` and `spec_le_comap_hodgeFiltration_one_of_periods`. -/
theorem spec_comap_hodgeFiltration_one_eq (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X :=
  spec_comap_hodgeFiltration_one_eq_aux X

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)).comap (bettiDeRhamHQ X 1) =
      complexAntiholomorphicH1 X :=
  spec_comap_conjHodgeFiltration_one_eq_of_eq X (spec_comap_hodgeFiltration_one_eq X)

/-- **The lower bound `g ≤ dim F^1 H_dR^1`.** For abelian `X` of dimension `g`, with no
hypothesis; with stage 4b's upper bound, `dim F^1 H_dR^1 = g`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
Theorem 1.4.1; `spec_comap_hodgeFiltration_one_eq` and `spec_comap_hodgeFiltration_one_eq_iff`. -/
theorem spec_le_finrank_hodgeFiltration_one (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    dim X.left ≤ Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) :=
  spec_le_finrank_hodgeFiltration_one_aux X

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) = dim X.left :=
  le_antisymm
    (spec_finrank_hodgeFiltration_one_le_of_le X (spec_comap_hodgeFiltration_one_eq X).le)
    (spec_le_finrank_hodgeFiltration_one X)

/-- **The degree-one Hodge decomposition.** For abelian `X`, `H_dR^1 = F^1 ⊕ conj F^1`, as the
internal direct sum of `deRhamHodgePiece X 1`, with no hypothesis. This is the degree-one part of
the ledger hypothesis `HodgeDecomposition X` for abelian `X`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
Theorem 1.4.1 (`H^1(X, ℂ) = H^{1,0} ⊕ H^{0,1}`); `spec_comap_hodgeFiltration_one_eq` and
`spec_deRhamHodgePiece_one_isInternal_of_comap_eq`. -/
theorem spec_deRhamHodgePiece_one_isInternal (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    DirectSum.IsInternal (deRhamHodgePiece X 1) :=
  spec_deRhamHodgePiece_one_isInternal_aux X

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    IsCompl (F^1 H_dR^((1 : ℕ) : ℤ)(X))
      (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) :=
  (spec_deRhamHodgePiece_one_isInternal_iff X).mp (spec_deRhamHodgePiece_one_isInternal X)

end HodgeLean.Adapters

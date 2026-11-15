import HodgeLean.Adapters.HolomorphicFormValuesProofs

/-! # Pointwise values of holomorphic forms and their pullback along `exp`: frozen specification

Inputs stage 4f, step 2 (and step 3) of stage 4d's route to `F^1_B ≤ complexHolomorphicH1 X`.
Sections of upstream's sheaf `Ω^p` (`holomorphicDeRhamSheaf`, a sheafification) have no pointwise
values upstream; `HolomorphicFormValuesDefs` gives them one, `globalFormValue X d p x θ`, an
alternating `p`-form on the coordinate space of the chart at `x`, by descending upstream's
`chartEvaluation` to stalks. For `p = 1`, `expPullback X d θ v = θ(exp v) ∘ D exp(v)` is the
pullback of `θ` along the uniformization `exp : ℂ^d → X(ℂ)` of S12, with `D exp` the manifold
derivative `mfderiv`.

Claimed:
* for every smooth `X`: the value of the sheafification of a presheaf form `ω` on `U ∋ x` is
  upstream's chart evaluation of `ω` at `x` in the chart at `x`;
* for every smooth `X`: every global form is, near each point, the sheafification of a presheaf
  form, and its value at `x` is then the chart evaluation in any chart around `x`, transported by
  the derivative of the chart transition;
* for every smooth `X`, and the falsification check of the brief: a global holomorphic `p`-form
  whose value vanishes at every point is zero (a nonzero form has a nonzero value somewhere);
* for a smooth commutative group scheme `X`: the derivative of `exp` at `0` is the identity;
* for a smooth commutative group scheme `X`: the pullback `exp^*θ` of a global holomorphic
  `1`-form is complex differentiable on `ℂ^d`, and it is periodic (`exp v = exp w` implies
  `exp^*θ(v) = exp^*θ(w)`);
* for abelian `X` (commutative, integral, smooth, projective): `exp^*θ` is constant, so
  `exp^*θ = ∑ aᵢ dzᵢ`, the implication from stage 4d's Liouville statement
  `spec_eq_of_differentiable_comp_complexExponential`;
* for abelian `X`: a global holomorphic `1`-form whose pullback vanishes at `0` is zero, so the
  invariance statement is not vacuous.

Not claimed: the identification of the space of global holomorphic `1`-forms with `(ℂ^d)^*`
(surjectivity of `θ ↦ exp^*θ(0)`), the closedness of global holomorphic `1`-forms, periods or
integrals of forms along loops, the period condition, or `F^1_B ≤ complexHolomorphicH1 X`
(`docs/specs/HolomorphicFormValues.md`). HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations
open scoped Manifold CategoryTheory.MonObj

namespace HodgeLean.Adapters

/-- The value at `x` of the sheafification of a holomorphic `p`-form `ω` on an open `U ∋ x` is
upstream's evaluation of `ω` in the chart at `x`, at the coordinate of `x`: the inverse of the
stalk isomorphism of the sheafification undoes the sheafification unit on germs.

Source: Godement, *Topologie algébrique et théorie des faisceaux*, II.1.2; Mathlib's
`stalkFunctor_map_germ` and `stalkFunctor_map_unit_toSheafify_isIso`; upstream
`chartEvaluation` (`HodgeConjecture/Definitions/AlgebraicGeometry/Hodge/AnalyticDifferentialForms.lean`
at `2ead713`). -/
theorem spec_formStalkValue_germ_toSheafify (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (U : Opens (TopCat.of (ComplexPoint X)))
    (x : ComplexPoint X) (hx : x ∈ U)
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p) :
    formStalkValue X d x p ((holomorphicDeRhamSheaf X d p).presheaf.germ U x hx
      ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (op U) (Submodule.Quotient.mk ω))) =
      chartEvaluation X d (op U) x p ω (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) :=
  spec_formStalkValue_germ_toSheafify_aux X d p U x hx ω

example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (x : ComplexPoint X) (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op ⊤)) p) :
    globalFormValue X d p x
        ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d p)).app (op ⊤) (Submodule.Quotient.mk ω)) =
      chartEvaluation X d (op ⊤) x p ω (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) :=
  spec_formStalkValue_germ_toSheafify X d p ⊤ x trivial ω

/-- Every global holomorphic `p`-form is, near each point `x`, the sheafification of a holomorphic
form on an open `U ∋ x` (the sheafification unit is locally surjective, and upstream's
holomorphic forms on `U` are a quotient of Kähler forms).

Source: Godement, *Topologie algébrique et théorie des faisceaux*, II.1.2; Mathlib's
`CategoryTheory.isLocallySurjective_toSheafify'` (`Mathlib/CategoryTheory/Sites/LocallySurjective.lean`). -/
theorem spec_exists_local_representative (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤)) (x : ComplexPoint X) :
    ∃ (U : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ U)
      (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p),
      (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top).op θ =
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d p)).app (op U) (Submodule.Quotient.mk ω) :=
  spec_exists_local_representative_aux X d p θ x

example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤)) (x : ComplexPoint X) :
    ∃ (U : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ U)
      (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p),
      globalFormValue X d p x θ =
        chartEvaluation X d (op U) x p ω (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) := by
  obtain ⟨U, hx, ω, hω⟩ := spec_exists_local_representative X d p θ x
  refine ⟨U, hx, ω, ?_⟩
  rw [← spec_formStalkValue_germ_toSheafify X d p U x hx ω, ← hω]
  change formStalkValue X d x p ((holomorphicDeRhamSheaf X d p).presheaf.germ ⊤ x trivial θ) = _
  rw [TopCat.Presheaf.germ_res_apply]

/-- The value at `x` of a global holomorphic `p`-form, read in the chart at any `z` whose domain
contains `x`: if the form is the sheafification of `ω` on `U ∋ x`, its value is the evaluation of
`ω` in the chart at `z`, at the coordinate of `x`, transported along the derivative of the chart
transition (upstream's chain rule `chartEvaluation_fixedChartTransition`).

Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (a form in two systems of
coordinates); upstream `chartEvaluation_fixedChartTransition`
(`HodgeConjecture/Lemmas/AlgebraicGeometry/Hodge/HolomorphicPoincare.lean` at `2ead713`), through
`spec_formStalkValue_germ_toSheafify`. -/
theorem spec_globalFormValue_eq_chartEvaluation (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤))
    (U : Opens (TopCat.of (ComplexPoint X)))
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p)
    (hω : (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top).op θ =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (op U) (Submodule.Quotient.mk ω))
    (z x : ComplexPoint X) (hx : x ∈ U)
    (hxz : x ∈ (extChartAt 𝓘(ℂ, Fin d → ℂ) z).source) :
    globalFormValue X d p x θ =
      (chartEvaluation X d (op U) z p ω (extChartAt 𝓘(ℂ, Fin d → ℂ) z x)).compContinuousLinearMap
        (fderiv ℂ (fixedChartTransition X d z x) (extChartAt 𝓘(ℂ, Fin d → ℂ) x x)) :=
  spec_globalFormValue_eq_chartEvaluation_aux X d p θ U ω hω z x hx hxz

example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤))
    (U : Opens (TopCat.of (ComplexPoint X)))
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p)
    (hω : (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top).op θ =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (op U) (Submodule.Quotient.mk ω))
    (z x : ComplexPoint X) (hx : x ∈ U) (hxz : x ∈ (extChartAt 𝓘(ℂ, Fin d → ℂ) z).source)
    (h0 : chartEvaluation X d (op U) z p ω (extChartAt 𝓘(ℂ, Fin d → ℂ) z x) = 0) :
    globalFormValue X d p x θ = 0 := by
  rw [spec_globalFormValue_eq_chartEvaluation X d p θ U ω hω z x hx hxz, h0]
  exact ContinuousAlternatingMap.ext fun v ↦ rfl

/-- A global holomorphic `p`-form whose value vanishes at every point is zero. **Falsification
check** for the evaluation: a nonzero global form has a nonzero value somewhere, so
`globalFormValue` is not trivially zero. Near each `x`, the form is the sheafification of some `ω`
on `U ∋ x` (`spec_exists_local_representative`); on `U ∩ (chart at x).source` the evaluation of
`ω` in the chart at `x` vanishes (`spec_globalFormValue_eq_chartEvaluation`), so the restriction
of `ω` lies in upstream's `chartEvaluationKernel`
(`mem_chartEvaluationKernel_of_chartEvaluation_eq_zero`), and every germ of the form is zero.

Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2; upstream
`mem_chartEvaluationKernel_of_chartEvaluation_eq_zero`; Mathlib's `TopCat.Presheaf.section_ext`
(a section of a sheaf is determined by its germs). -/
theorem spec_eq_zero_of_globalFormValue_eq_zero (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤))
    (hθ : ∀ x, globalFormValue X d p x θ = 0) : θ = 0 :=
  spec_eq_zero_of_globalFormValue_eq_zero_aux X d p θ hθ

example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤)) (hθ : θ ≠ 0) :
    ∃ x, globalFormValue X d p x θ ≠ 0 := by
  by_contra h
  push Not at h
  exact hθ (spec_eq_zero_of_globalFormValue_eq_zero X d p θ h)

/-- For a smooth commutative group scheme, the derivative of `exp` at `0` is the identity: the
chart of `X(ℂ)` at `exp 0 = 1` is the identity chart up to a translation, in which `exp` has real
derivative the identity at `0` (S12) and is complex differentiable there (stage 4d).

Source: Mumford, *Abelian Varieties*, §1 (the differential of the exponential at `0`); S12's
`hasFDerivAt_complexExponential_chart`, stage 4d's
`spec_eventually_differentiableAt_complexExponential_chart` and stage 4e's
`spec_mdifferentiable_complexExponential`. -/
theorem spec_mfderiv_complexExponential_zero (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] (u : Fin d → ℂ) :
    mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) (fun w ↦ (complexExponential X d w).toMul) 0 u =
      u :=
  spec_mfderiv_complexExponential_zero_aux X d u

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (u : Fin d → ℂ) :
    expPullback X d θ 0 u = globalOneFormCovector X d θ (complexExponential X d 0).toMul u := by
  change globalOneFormCovector X d θ _ (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ)
    (fun w ↦ (complexExponential X d w).toMul) 0 u) = _
  rw [spec_mfderiv_complexExponential_zero X d u]

/-- For a smooth commutative group scheme, the pullback `exp^*θ` of a global holomorphic `1`-form
is complex differentiable on `ℂ^d`. Near `v₀`, with `θ` the sheafification of `ω` on `U ∋ exp v₀`,
`exp^*θ(v) = ω_{x₀}(φ(v)) ∘ Dφ(v)` in the fixed chart at `x₀ = exp v₀`, where `φ = chart ∘ exp`
(`spec_globalFormValue_eq_chartEvaluation` and the chain rule for `mfderiv`); the coefficient
`ω_{x₀}` is analytic (upstream `analyticOnNhd_chartEvaluation`) and `φ` is analytic (stage 4e's
`spec_contMDiff_complexExponential`).

Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the pullback of a
holomorphic form along a holomorphic map is holomorphic); upstream
`analyticOnNhd_chartEvaluation`; through `spec_globalFormValue_eq_chartEvaluation`,
`spec_exists_local_representative` and stage 4e's `spec_contMDiff_complexExponential`. -/
theorem spec_differentiable_expPullback (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) :
    Differentiable ℂ (expPullback X d θ) :=
  spec_differentiable_expPullback_aux X d θ

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) :
    Continuous (expPullback X d θ) :=
  (spec_differentiable_expPullback X d θ).continuous

/-- For a smooth commutative group scheme, the pullback `exp^*θ` is periodic: if
`exp v = exp w`, then `exp = exp ∘ (· + (w - v))` (`complexExponentialHom`), so the derivatives
of `exp` at `v` and `w` agree, and `θ` is evaluated at the same point.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.1 (forms on
`V/Λ` are `Λ`-invariant forms on `V`); S12's `complexExponentialHom`; Mathlib's `mfderiv_comp`. -/
theorem spec_expPullback_eq_of_complexExponential_eq (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (v w : Fin d → ℂ)
    (h : complexExponential X d v = complexExponential X d w) :
    expPullback X d θ v = expPullback X d θ w :=
  spec_expPullback_eq_of_complexExponential_eq_aux X d θ v w h

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (v w : Fin d → ℂ) (hw : complexExponential X d w = 0) :
    expPullback X d θ (v + w) = expPullback X d θ v := by
  refine spec_expPullback_eq_of_complexExponential_eq X d θ (v + w) v ?_
  change complexExponentialHom X d (v + w) = complexExponentialHom X d v
  rw [map_add]
  change complexExponential X d v + complexExponential X d w = _
  rw [hw, add_zero]
  rfl

/-- For abelian `X`, the pullback `exp^*θ` of a global holomorphic `1`-form is constant, so
`exp^*θ = ∑ aᵢ dzᵢ`: the implication from stage 4d's Liouville statement
`spec_eq_of_differentiable_comp_complexExponential` (through its frozen `example` for
`Λ`-periodic maps `ℂ^d → (ℂ^d →L[ℂ] ℂ)`), with `spec_differentiable_expPullback` and
`spec_expPullback_eq_of_complexExponential_eq`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.1 and
Lemma 1.3.1 (the holomorphic `1`-forms on `V/Λ` are the `dzᵢ`); Mumford, *Abelian Varieties*,
§1. -/
theorem spec_expPullback_eq_expPullback_zero (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (v : Fin d → ℂ) : expPullback X d θ v = expPullback X d θ 0 :=
  spec_expPullback_eq_expPullback_zero_aux X d θ v

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) :
    ∃ a : Fin d → ℂ, ∀ v u, expPullback X d θ v u = ∑ i, a i * u i := by
  refine ⟨fun i ↦ expPullback X d θ 0 (Pi.single i 1), fun v u ↦ ?_⟩
  rw [spec_expPullback_eq_expPullback_zero X d θ v]
  conv_lhs => rw [show u = ∑ i, u i • Pi.single i (1 : ℂ) by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, mul_comm]

/-- For abelian `X`, a global holomorphic `1`-form whose pullback along `exp` vanishes at `0` is
zero: by invariance the pullback vanishes everywhere, the derivative of `exp` is invertible at
every point (the identity at `0`, `spec_mfderiv_complexExponential_zero`, transported by
holomorphic translations), `exp` is onto, and a form with zero values is zero
(`spec_eq_zero_of_globalFormValue_eq_zero`). **Falsification check** for the invariance
statement: `exp^*θ` is not identically zero for `θ ≠ 0`, so `spec_expPullback_eq_expPullback_zero`
is not satisfied vacuously.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.1; S12's
`surjective_complexExponential`; stage 4e's `spec_contMDiff_mul_left`; through
`spec_expPullback_eq_expPullback_zero`, `spec_mfderiv_complexExponential_zero` and
`spec_eq_zero_of_globalFormValue_eq_zero`. -/
theorem spec_eq_zero_of_expPullback_zero_eq_zero (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (hθ : expPullback X d θ 0 = 0) : θ = 0 :=
  spec_eq_zero_of_expPullback_zero_eq_zero_aux X d θ hθ

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (hθ : θ ≠ 0) :
    ∃ u, expPullback X d θ 0 u ≠ 0 := by
  by_contra h
  push Not at h
  exact hθ (spec_eq_zero_of_expPullback_zero_eq_zero X d θ (ContinuousLinearMap.ext h))

end HodgeLean.Adapters

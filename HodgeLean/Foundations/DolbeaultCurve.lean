import HodgeLean.Foundations.DolbeaultCurveProofs

/-! # The Dolbeault sequence on `X(ℂ)`, stage 1: `0 → 𝒪 → 𝒜^{0,0} → 𝒜^{0,1}` (FROZEN SPEC)

Scope. The cch2 spec (`Adapters/CurveStructureSheafVanishing.lean`) proves `H^2(X(ℂ), 𝒪) = 0`, and
`CycleClassIsHodge X` for an integral smooth projective curve, as an implication from a short exact
sequence `0 → Ω•(X).X 0 → A → B → 0` of sheaves on `X(ℂ)` with `ℍ^2(A[0]) = 0` and `ℍ^1(B[0]) = 0`.
This stage builds the Dolbeault candidates for `A` and `B` (`DolbeaultCurveDefs.lean`: the real
`C^∞` structure on `X(ℂ)`, the sheaves `𝒜^{0,0} = smoothFunctionSheaf X d` and
`𝒜^{0,1} = zeroOneFormSheaf X d`, the inclusion `holomorphicToSmooth` and `∂̄ = dbar`), and freezes
what is provable now about the sequence `0 → 𝒪 → 𝒜^{0,0} → 𝒜^{0,1}`.

* `∂̄ ∘ (𝒪 ⟶ 𝒜^{0,0}) = 0` and the inclusion is a monomorphism, in every dimension
  (statements 1, 2).
* Exactness at `𝒜^{0,0}` on curves: a smooth function with `∂̄ f = 0` on an open set is holomorphic
  (statement 3), so the sequence is exact at `𝒜^{0,0}` when `d = 1` (statement 4).
* The degree-zero term `Ω•(X).X 0` of upstream's holomorphic de Rham complex is the sheaf `𝒪` of
  holomorphic functions (statements 5, 6).
* Assembly: for a curve, `H^2(X(ℂ), 𝒪) = 0` (statement 7) and `CycleClassIsHodge X` (statement 8)
  as implications from three explicit binders: `∂̄` is an epimorphism of sheaves (the
  `∂̄`-Poincaré lemma in one variable), `ℍ^2(𝒜^{0,0}[0]) = 0` and `ℍ^1(𝒜^{0,1}[0]) = 0` (fine
  sheaves are acyclic).
* Falsification check: `∂̄ ≠ 0` as soon as `d > 0` and `X(ℂ)` is nonempty (statement 9), so
  `𝒜^{0,1}` is not degenerate and `𝒪 ⟶ 𝒜^{0,0}` is not an epimorphism.

Claimed: statements 1, 2, 5, 6, 9 in their stated generality; statements 3, 4 for relative
dimension `1`; `H^2(X(ℂ), 𝒪) = 0` and `CycleClassIsHodge X` for every integral smooth (projective)
curve as an implication from the three binders of statements 7 and 8.

Not claimed: the `∂̄`-Poincaré lemma (surjectivity of `∂̄` on stalks); acyclicity of `𝒜^{0,0}` or
`𝒜^{0,1}`, or any notion of fine or soft sheaf; exactness at `𝒜^{0,0}` in dimension `d ≥ 2` (true,
but it needs analyticity of complex-differentiable functions of several variables, absent from
Mathlib); `(p, q)`-forms beyond `(0, 0)` and `(0, 1)`; `CycleClassIsHodge X` for curves
unconditionally. No new `@[hodge_hypothesis]`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicGeometry ComplexPoint
open scoped ContDiff Manifold
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations

/-- **`∂̄` kills holomorphic functions.** The composite `𝒪 ⟶ 𝒜^{0,0} ⟶ 𝒜^{0,1}` is zero: the real
differential of a holomorphic function is complex-linear in every chart, so its conjugate-linear
part vanishes.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (a function is holomorphic
if and only if `∂̄ f = 0`; the Cauchy–Riemann equations); Huybrechts, *Complex Geometry*, §1.1. -/
theorem spec_holomorphicToSmooth_comp_dbar (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    holomorphicToSmooth X d ≫ dbar X d = 0 :=
  spec_holomorphicToSmooth_comp_dbar_aux X d

/-- The `∂̄` of a holomorphic function, seen as a smooth function, is zero on sections. -/
example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (U : Opens (ComplexPoint X)) (f : C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯) :
    ((dbar X d).hom.app (Opposite.op U)) ((holomorphicToSmooth X d).hom.app (Opposite.op U) f) =
      0 := by
  have h := congrArg (fun φ => (φ.hom.app (Opposite.op U)) f)
    (spec_holomorphicToSmooth_comp_dbar X d)
  exact h

/-- **The inclusion `𝒪 ⟶ 𝒜^{0,0}` is a monomorphism** of sheaves on `X(ℂ)`: it is injective on
sections, a holomorphic function being sent to itself.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2–3 (the Dolbeault sequence
`0 → 𝒪 → 𝒜^{0,0}`). -/
theorem spec_mono_holomorphicToSmooth (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    Mono (holomorphicToSmooth X d) :=
  spec_mono_holomorphicToSmooth_aux X d

/-- Any isomorphic copy of `𝒪` maps monomorphically to `𝒜^{0,0}`. -/
example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    {F : AnalyticAdditiveSheaf X} (e : F ≅ holomorphicFunctionAddSheaf X d) :
    Mono (e.hom ≫ holomorphicToSmooth X d) :=
  have := spec_mono_holomorphicToSmooth X d
  mono_comp _ _

/-- **On a Riemann surface, `∂̄ f = 0` forces `f` holomorphic.** If `X` has relative dimension `1`
and `f` is a real-smooth function on an open `U ⊆ X(ℂ)` whose `∂̄` vanishes at every point, then
`f` is holomorphic on `U`: in each chart its real differential is complex-linear (the
Cauchy–Riemann equations), so it is complex-differentiable, hence analytic.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §1–2; Ahlfors, *Complex
Analysis*, 3rd ed., Ch. 2 §1 (the Cauchy–Riemann equations) and Ch. 5 §1 (Taylor series of
holomorphic functions); Mathlib's `hasFDerivAt_of_restrictScalars` and
`DifferentiableOn.analyticAt`. -/
theorem spec_contMDiff_of_dbarSection_eq_zero (X : Over (Spec ↧ℂ))
    [SmoothOfRelativeDimension 1 X.hom] {U : Opens (ComplexPoint X)}
    (f : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) (hf : dbarSection X 1 f = 0) :
    ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) ω (f : U → ℂ) :=
  spec_contMDiff_of_dbarSection_eq_zero_aux X f hf

/-- Such an `f` comes from a section of `𝒪`. -/
example (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom] {U : Opens (ComplexPoint X)}
    (f : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) (hf : dbarSection X 1 f = 0) :
    ∃ g : C^ω⟮𝓘(ℂ, Fin 1 → ℂ), U; ℂ⟯, (g : U → ℂ) = f :=
  ⟨⟨f, spec_contMDiff_of_dbarSection_eq_zero X f hf⟩, rfl⟩

/-- **Exactness at `𝒜^{0,0}` on curves.** For relative dimension `d = 1`, the sequence
`𝒪 ⟶ 𝒜^{0,0} ⟶ 𝒜^{0,1}` of sheaves on `X(ℂ)` is exact: the kernel of `∂̄` is `𝒪`
(statement 3 on every open set).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2–3 (exactness of the
Dolbeault sequence `0 → 𝒪 → 𝒜^{0,0} → 𝒜^{0,1} → 0` on a Riemann surface). -/
theorem spec_exact_holomorphicToSmooth_dbar (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (hd : d = 1) :
    (ShortComplex.mk (holomorphicToSmooth X d) (dbar X d)
      (spec_holomorphicToSmooth_comp_dbar X d)).Exact :=
  spec_exact_holomorphicToSmooth_dbar_aux X d hd

/-- For an integral smooth curve, in the dimension used by `Ω•(X)`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] :
    (ShortComplex.mk (holomorphicToSmooth X (dim X.left)) (dbar X (dim X.left))
      (spec_holomorphicToSmooth_comp_dbar X _)).Exact :=
  spec_exact_holomorphicToSmooth_dbar X _ (SmoothOfRelativeDimension.dim_eq X.hom 1)

/-- **Holomorphic zero-forms are holomorphic functions.** On an open `U ⊆ X(ℂ)`, upstream's
holomorphic `0`-forms are `⋀^0` of the Kähler differentials of `𝒪(U)` modulo forms whose chart
evaluations vanish; the map `𝒪(U) → HolomorphicForm X d U 0`, `a ↦ [a]`, is bijective. `⋀^0` is
`𝒪(U)` itself, and a function whose values vanish in every chart is zero.
Source: Bourbaki, *Algebra*, Ch. III §7.1 (`⋀^0 M = R`); upstream `HolomorphicForm`,
`chartEvaluation_mk` (`Hodge/AnalyticDifferentialForms.lean`). -/
theorem spec_bijective_holomorphicForm_zero (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    Function.Bijective ((chartEvaluationKernel X d U 0).mkQ ∘ₗ
      Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions X d U)) :=
  spec_bijective_holomorphicForm_zero_aux X d U

/-- In particular a holomorphic function whose zero-form is zero is zero. -/
example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (a : OpenHolomorphicFunctions X d U)
    (h : (chartEvaluationKernel X d U 0).mkQ (Algebra.DeRham.ofFunction ℂ _ a) = 0) :
    a = 0 :=
  (spec_bijective_holomorphicForm_zero X d U).1 (by simpa using h)

/-- **`Ω•(X).X 0 ≅ 𝒪`.** The degree-zero term of upstream's holomorphic de Rham complex (the
sheafification of holomorphic `0`-forms) is isomorphic to the sheaf of holomorphic functions:
statement 5 is natural in `U`, and the sheafification of a sheaf is itself.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
Ch. 8 §8.1 (the holomorphic de Rham complex, `Ω^0_X = 𝒪_X`); upstream `holomorphicDeRhamSheaf`. -/
theorem spec_nonempty_iso_holomorphicDeRham_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] :
    Nonempty (Ω•(X).X 0 ≅ holomorphicFunctionAddSheaf X (dim X.left)) :=
  spec_nonempty_iso_holomorphicDeRham_zero_aux X

/-- The complex in the cch binder is `𝒪[0]`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    Nonempty (holomorphicFormsShifted X 0 ≅
      (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj
        (holomorphicFunctionAddSheaf X (dim X.left))) :=
  (spec_nonempty_iso_holomorphicDeRham_zero X).map fun e =>
    (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).mapIso e

/-- **`H^2(X(ℂ), 𝒪) = 0` on a curve, from the Dolbeault binders.** For an integral smooth `X` of
dimension `1`, if `∂̄ : 𝒜^{0,0} ⟶ 𝒜^{0,1}` is an epimorphism of sheaves, `H^2(X(ℂ), 𝒜^{0,0}) = 0`
and `H^1(X(ℂ), 𝒜^{0,1}) = 0`, then `ℍ^2(X; holomorphicFormsShifted X 0) = H^2(X(ℂ), 𝒪)` vanishes.
Statements 2, 4 and the binder make `0 → 𝒪 → 𝒜^{0,0} → 𝒜^{0,1} → 0` short exact, statement 6
replaces `𝒪` by `Ω•(X).X 0`, and cch2 statement 2 concludes.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the `∂̄`-Poincaré lemma in
one variable) and §3 (fine resolutions, Dolbeault's theorem); Voisin, *Hodge Theory and Complex
Algebraic Geometry I*, §8.1.2 (Griffiths–Harris Ch. 0 §3: fine sheaves are acyclic); here cch2's
`spec_subsingleton_hypercohomology_two_of_shortExact`. -/
theorem spec_subsingleton_hypercohomology_two_of_dbar (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (hd : dim X.left = 1)
    (hε : Epi (dbar X (dim X.left)))
    (hA : Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))))
    (hB : Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left)))) :
    Subsingleton ℍ^2(X; holomorphicFormsShifted X 0) :=
  spec_subsingleton_hypercohomology_two_of_dbar_aux X hd hε hA hB

/-- With the cch spec, the same binders give `F^1 H_dR^2(X) = F^0 H_dR^2(X)`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (hd : dim X.left = 1)
    (hε : Epi (dbar X (dim X.left)))
    (hA : Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))))
    (hB : Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left)))) :
    F^(0 + 1) H_dR^2(X) = F^0 H_dR^2(X) :=
  spec_hodgeFiltration_succ_eq_of_subsingleton X 0 2
    (spec_subsingleton_hypercohomology_two_of_dbar X hd hε hA hB)

/-- **Assembly: `CycleClassIsHodge` for curves from the Dolbeault binders.** For an integral smooth
projective curve `X` over `ℂ`, if `∂̄` is an epimorphism of sheaves on `X(ℂ)`,
`H^2(X(ℂ), 𝒜^{0,0}) = 0` and `H^1(X(ℂ), 𝒜^{0,1}) = 0`, then `CycleClassIsHodge X`: statement 7,
then `spec_cycleClassIsHodge_of_curve` (cch spec).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2–3; Voisin, *Hodge Theory
and Complex Algebraic Geometry I*, §§11.1.2–11.1.3 (cycle classes are of type `(p, p)`). -/
theorem spec_cycleClassIsHodge_of_curve_of_dbar (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (hε : Epi (dbar X (dim X.left)))
    (hA : Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))))
    (hB : Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left)))) :
    CycleClassIsHodge X :=
  spec_cycleClassIsHodge_of_curve_of_dbar_aux X hε hA hB

/-- The codimension-one part, with the same binders. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (hε : Epi (dbar X (dim X.left)))
    (hA : Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))))
    (hB : Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left)))) :
    algebraicCycleClassSpan X 1 ≤ Hdg^1(X; ℚ) :=
  (spec_cycleClassIsHodge_of_curve_of_dbar X hε hA hB).le 1

/-- **Falsification check: `∂̄` is not zero.** If `d > 0` and `X(ℂ)` has a point `x`, then
`∂̄ : 𝒜^{0,0} ⟶ 𝒜^{0,1}` is not the zero morphism: on the chart domain at `x`, the conjugate of
the first chart coordinate is smooth, and its `∂̄` at `x` is `v ↦ conj (v 0)`, which is not zero.
So `𝒜^{0,1}` is not degenerate, statements 1 and 4 have content, and `𝒪 ⟶ 𝒜^{0,0}` is not an
epimorphism.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (`∂̄ z̄ = dz̄ ≠ 0`). -/
theorem spec_dbar_ne_zero (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (hd : 0 < d) (x : ComplexPoint X) :
    dbar X d ≠ 0 :=
  spec_dbar_ne_zero_aux X d hd x

/-- So `𝒪 ⟶ 𝒜^{0,0}` is not an epimorphism (with statement 1). -/
example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom] (hd : 0 < d)
    (x : ComplexPoint X) :
    ¬ Epi (holomorphicToSmooth X d) := fun _ =>
  spec_dbar_ne_zero X d hd x ((cancel_epi (holomorphicToSmooth X d)).1
    ((spec_holomorphicToSmooth_comp_dbar X d).trans Limits.comp_zero.symm))

end HodgeLean.Foundations

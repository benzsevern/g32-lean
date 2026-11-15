import HodgeLean.Adapters.ExpHolomorphicProofs

/-! # Holomorphic translations and the holomorphic exponential: frozen specification

Inputs stage 4e, step 1 of stage 4d's route to `F^1_B ≤ complexHolomorphicH1 X`: the uniformization
`exp : ℂ^d → X(ℂ)` of S12 (`complexExponential`) is holomorphic as a map of complex manifolds.
`X(ℂ)` carries upstream's analytic manifold structure (`isManifold_omega`, charts `localChart`).

Claimed:
* for smooth `X`, `Y` and a morphism `f : X ⟶ Y` over `Spec ℂ`: the induced map
  `X(ℂ) → Y(ℂ)` is holomorphic (`ContMDiff … ω`), from upstream's chart-level
  `analyticAt_localChart_symm_map`;
* for a smooth group scheme `X`: left translation by a ℂ-point is holomorphic, and `X(ℂ)` is a
  complex Lie group (multiplication jointly holomorphic, inversion holomorphic);
* for a smooth commutative group scheme `X`: `exp` is complex differentiable as a manifold map,
  the implication from the translations and stage 4d's identity-chart germ at `0`;
* for a smooth commutative group scheme `X`: `exp` is analytic at `0` in the identity chart, and
  `exp` is holomorphic (`ContMDiff … ω`) everywhere;
* falsification: complex conjugation on `ℂ` is additive and real analytic but not complex
  differentiable at `0`, so a continuous, even real-analytic, additive map need not satisfy the
  conclusion; the complex structure of the germ at `0` is what is used.

The additivity `exp (v + w) = exp v + exp w` is not restated: it is S12's `complexExponentialHom`.
Not claimed: pointwise values or pullbacks of holomorphic forms, the invariance of global
holomorphic `1`-forms, the period condition, or `F^1_B ≤ complexHolomorphicH1 X`
(`docs/specs/ExpHolomorphic.md`). HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint
open HodgeLean.Foundations
open Filter Topology
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace HodgeLean.Adapters

/-- The map on ℂ-points induced by a morphism of smooth complex schemes is holomorphic for
upstream's analytic manifold structures: it is continuous (`Point.continuous_map`), and in the
charts at `x` and `f x` it is analytic at the center (`analyticAt_localChart_symm_map`).

Source: Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956), §2
(the analytification of a morphism is holomorphic); upstream
`HodgeConjecture/Lemmas/AlgebraicGeometry/ComplexPoint/AnalyticMap.lean` at `2ead713`
(`analyticAt_localChart_symm_map`) and `ComplexPoint/Manifold.lean` (`isManifold_omega`). -/
theorem spec_contMDiff_pointMap (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom] (f : X ⟶ Y) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ω
      (Point.map f : ComplexPoint X → ComplexPoint Y) :=
  spec_contMDiff_pointMap_aux X Y d e f

example (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom] (f : X ⟶ Y) :
    MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ)
      (Point.map f : ComplexPoint X → ComplexPoint Y) :=
  (spec_contMDiff_pointMap X Y d e f).mdifferentiable (by simp)

/-- Left translation `x ↦ a * x` by a ℂ-point `a` of a smooth group scheme is holomorphic: it is
the map on ℂ-points of the scheme morphism `lift (toUnit X ≫ a) (𝟙 X) ≫ μ : X ⟶ X`.

Source: Mumford, *Abelian Varieties*, §1 (translations are morphisms of varieties); through
`spec_contMDiff_pointMap`. -/
theorem spec_contMDiff_mul_left (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] (a : ComplexPoint X) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (fun x : ComplexPoint X ↦ a * x) :=
  spec_contMDiff_mul_left_aux X d a

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [SmoothOfRelativeDimension d X.hom]
    (a b : ComplexPoint X) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (fun x : ComplexPoint X ↦ a * (b * x)) :=
  (spec_contMDiff_mul_left X d a).comp (spec_contMDiff_mul_left X d b)

/-- The ℂ-points of a smooth group scheme form a complex Lie group for upstream's analytic
manifold structure: inversion is the map on ℂ-points of `ι`, and multiplication is the map on
ℂ-points of `μ : X ⊗ X ⟶ X` composed with the product comparison
`X(ℂ) × X(ℂ) ≃ (X ⊗ X)(ℂ)`, which is analytic in charts
(`analyticAt_productChartComparison_symm`, at every point).

Source: Mumford, *Abelian Varieties*, §1 (a group variety over `ℂ` is a complex Lie group); Serre,
*Géométrie algébrique et géométrie analytique*, §2; through `spec_contMDiff_pointMap` and S10's
`analyticAt_productChartComparison_symm` (`HodgeLean/Foundations/ChartGroupLaw.lean`). -/
theorem spec_lieGroup_complexPoint (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] :
    LieGroup 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X) :=
  spec_lieGroup_complexPoint_aux X d

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [SmoothOfRelativeDimension d X.hom] :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (fun x : ComplexPoint X ↦ x⁻¹) :=
  have := spec_lieGroup_complexPoint X d
  contMDiff_inv 𝓘(ℂ, Fin d → ℂ) ω

/-- For a smooth commutative group scheme, the uniformization `exp` is complex differentiable as
a map of manifolds: near `v₀`, `exp (v₀ + w) = exp v₀ * exp w` (`complexExponentialHom`), so
`exp = (exp v₀ * ·) ∘ exp ∘ (· - v₀)`, and `exp` is complex differentiable at `0` in the identity
chart (stage 4d), the identity chart being a chart of upstream's atlas up to translation.

Source: Mumford, *Abelian Varieties*, §1 (the exponential of a complex Lie group is holomorphic);
through `spec_contMDiff_mul_left`, S12's `complexExponentialHom` and stage 4d's
`spec_eventually_differentiableAt_complexExponential_chart`. -/
theorem spec_mdifferentiable_complexExponential (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] :
    MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ)
      (fun v ↦ (complexExponential X d v).toMul) :=
  spec_mdifferentiable_complexExponential_aux X d

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] (a : ComplexPoint X) :
    MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ)
      (fun v ↦ a * (complexExponential X d v).toMul) :=
  ((spec_contMDiff_mul_left X d a).mdifferentiable (by simp)).comp
    (spec_mdifferentiable_complexExponential X d)

/-- For a smooth commutative group scheme, `exp` is complex analytic at `0` in the identity chart.
With `e₁, …, e_d` the standard basis, `exp (∑ zᵢ eᵢ) = ∏ exp (zᵢ eᵢ)`, so near `0` the chart
expression is an iterate of the analytic chart group law (`analyticAt_chartGroupLaw`) applied to
the one-variable maps `z ↦ identityChart (exp (z eᵢ))`; each of these is complex differentiable
near `0` (stage 4d), hence analytic by Cauchy's integral formula in one variable. No several
variables Hartogs or Osgood theorem is needed.

Source: Mumford, *Abelian Varieties*, §1; Mathlib's `DifferentiableOn.analyticAt` (one variable),
S10's `analyticAt_chartGroupLaw`, S12's `complexExponentialHom` and stage 4d's
`spec_eventually_differentiableAt_complexExponential_chart`. -/
theorem spec_analyticAt_complexExponential_chart (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] :
    AnalyticAt ℂ (fun w ↦ identityChart X d (complexExponential X d w).toMul) 0 :=
  spec_analyticAt_complexExponential_chart_aux X d

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] :
    ContDiffAt ℂ ω (fun w ↦ identityChart X d (complexExponential X d w).toMul) 0 :=
  (spec_analyticAt_complexExponential_chart X d).contDiffAt

/-- For a smooth commutative group scheme, the uniformization `exp` is holomorphic everywhere as a
map of complex manifolds: at `0` by the previous statement (the identity chart differs from
upstream's chart at `1` by a translation of `ℂ^d`), and at `v₀` through
`exp = (exp v₀ * ·) ∘ exp ∘ (· - v₀)` and holomorphic left translation.

Source: Mumford, *Abelian Varieties*, §1; through `spec_analyticAt_complexExponential_chart`,
`spec_contMDiff_mul_left` and S12's `complexExponentialHom`. -/
theorem spec_contMDiff_complexExponential (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      (fun v ↦ (complexExponential X d v).toMul) :=
  spec_contMDiff_complexExponential_aux X d

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] (Y : Over (Spec ↧ℂ)) (e : ℕ)
    [SmoothOfRelativeDimension e Y.hom] (f : X ⟶ Y) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ω
      (fun v ↦ Point.map f (complexExponential X d v).toMul) :=
  (spec_contMDiff_pointMap X Y d e f).comp (spec_contMDiff_complexExponential X d)

/-- Falsification check for the holomorphy statements: complex conjugation on `ℂ` is additive and
real analytic, but not complex differentiable at `0`. So the homomorphism property and real
regularity do not give the conclusion of `spec_mdifferentiable_complexExponential`; and
`MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)` is a genuine constraint.

Source: the Cauchy–Riemann equations (Ahlfors, *Complex Analysis*, 3rd ed., Ch. 2 §1.2); Mathlib's
`mdifferentiableAt_iff_differentiableAt` and `differentiableAt_star_conj_iff`. -/
theorem spec_conj_not_mdifferentiable :
    (∀ z w : ℂ, starRingEnd ℂ (z + w) = starRingEnd ℂ z + starRingEnd ℂ w) ∧
      ContDiff ℝ ω (starRingEnd ℂ : ℂ → ℂ) ∧
      ¬ MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (starRingEnd ℂ : ℂ → ℂ) 0 :=
  spec_conj_not_mdifferentiable_aux

example : ¬ ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (starRingEnd ℂ : ℂ → ℂ) := fun h ↦
  spec_conj_not_mdifferentiable.2.2 ((h.mdifferentiable (by simp)) 0)

end HodgeLean.Adapters

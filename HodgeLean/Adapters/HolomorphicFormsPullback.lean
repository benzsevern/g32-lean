import HodgeLean.Adapters.HolomorphicFormsPullbackProofs

/-! # Holomorphic functions along the uniformization: frozen specification

Inputs stage 4d, toward `F^1_B ≤ complexHolomorphicH1 X`. Stage 4c (`HolomorphicOneForms`)
identifies `F^1 H_dR^1(X)` with the de Rham classes of closed global holomorphic `1`-forms, and
proves injectivity of the class map only as an implication from a premise `hconst`: every global
section of upstream's sheaf `Ω^0` of holomorphic `0`-forms comes from the constant sheaf `ℂ_X`.
This stage discharges `hconst` for compact `X(ℂ)`, and takes the first analytic steps along the
uniformization `exp : ℂ^g → X(ℂ)` of S12 (`complexExponential`).

`globalHolomorphicFunctionToZeroForm X d` sends a global holomorphic function on `X(ℂ)` (a global
section of upstream's `holomorphicFunctionSheaf`) to the global section of `Ω^0` it defines.

Claimed:
* for abelian `X` (commutative, integral, smooth, projective): a map `g : X(ℂ) → F` into a complex
  normed space whose pullback `g ∘ exp` along the uniformization is complex differentiable on
  `ℂ^d` is constant (Liouville, through the lattice-periodicity of `g ∘ exp`);
* falsification: a lattice-periodic function need not be constant if it is only real smooth, or if
  the lattice does not have full rank;
* for commutative `X`: in the identity chart, `exp` is complex differentiable near `0`;
* for compact `X(ℂ)`: every global holomorphic function on `X(ℂ)` is locally constant;
* for every smooth `X`: holomorphic functions and global sections of `Ω^0` agree on `X(ℂ)`, and a
  locally constant global holomorphic function gives a section of `Ω^0` coming from `ℂ_X`;
* for smooth integral `X` with compact `X(ℂ)`: stage 4c's premise `hconst` holds;
* for smooth integral projective `X`: the de Rham class map on closed global holomorphic
  `1`-forms is injective, the implication from stage 4c's
  `spec_cycleDeRhamClass_injective_of_constant` with `hconst` discharged.

Not claimed: holomorphy of `exp` away from `0` or as a map of manifolds, holomorphy of
translations, the pullback of a holomorphic form along `exp` or along charts, the invariance of
global holomorphic `1`-forms, the period condition, or `F^1_B ≤ complexHolomorphicH1 X`
(`docs/specs/HolomorphicFormsPullback.md`). HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations
open Filter Topology

namespace HodgeLean.Adapters

/-- For abelian `X`, a map `g : X(ℂ) → F` whose pullback along the uniformization
`exp : ℂ^d → X(ℂ)` is complex differentiable is constant: `g ∘ exp` is periodic under the full
period lattice, hence bounded (its values are those on a compact fundamental domain), hence
constant by Liouville, and `exp` is onto.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.1 (holomorphic
functions on `V/Λ` are constant); Liouville's theorem, through `AppellHumbert.spec_trivial_sections`
(the scalar case, `HodgeLean/Foundations/AppellHumbertSections.lean`) and Hahn–Banach; S12's
`isZLattice_complexExponentialLattice` and `surjective_complexExponential`. -/
theorem spec_eq_of_differentiable_comp_complexExponential (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (g : ComplexPoint X → F)
    (hg : Differentiable ℂ (fun v ↦ g (complexExponential X d v).toMul))
    (x y : ComplexPoint X) : g x = g y :=
  spec_eq_of_differentiable_comp_complexExponential_aux X d g hg x y

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (h : (Fin d → ℂ) → ((Fin d → ℂ) →L[ℂ] ℂ)) (hh : Differentiable ℂ h)
    (hper : ∀ v w, complexExponential X d v = complexExponential X d w → h v = h w)
    (v w : Fin d → ℂ) : h v = h w := by
  classical
  let g : ComplexPoint X → ((Fin d → ℂ) →L[ℂ] ℂ) := fun x ↦
    if hx : ∃ u, (complexExponential X d u).toMul = x then h hx.choose else 0
  have hgh : (fun u ↦ g (complexExponential X d u).toMul) = h := by
    funext u
    have hx : ∃ u', (complexExponential X d u').toMul = (complexExponential X d u).toMul :=
      ⟨u, rfl⟩
    simp only [g, hx, ↓reduceDIte]
    exact hper _ _ (Additive.toMul.injective hx.choose_spec)
  have := spec_eq_of_differentiable_comp_complexExponential X d g (hgh ▸ hh)
    (complexExponential X d v).toMul (complexExponential X d w).toMul
  rwa [← congrFun hgh v, ← congrFun hgh w]

/-- Falsification check for the previous statement: a lattice-periodic function on `ℂ` need not
be constant if the lattice is not of full rank (`exp(2πiz)` is entire and `ℤ`-periodic), or if it
is only real smooth (`exp(2πi Re z)` is `ℤ[i]`-periodic). Complex differentiability and the
compactness of `V/Λ` are both used.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.1; Mathlib's
`Complex.exp_int_mul_two_pi_mul_I`. -/
theorem spec_exists_nonconstant_periodic :
    (∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∀ (n : ℤ) (z : ℂ), f (z + n) = f z) ∧
      f 0 ≠ f Complex.I) ∧
    (∃ f : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ (m n : ℤ) (z : ℂ), f (z + m + n * Complex.I) = f z) ∧ f 0 ≠ f (1 / 2)) :=
  spec_exists_nonconstant_periodic_aux

example : ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ¬ ∀ z w, f z = f w := by
  obtain ⟨f, hf, -, hne⟩ := spec_exists_nonconstant_periodic.1
  exact ⟨f, hf, fun h ↦ hne (h _ _)⟩

/-- For commutative `X`, the uniformization `exp` is complex differentiable near `0` in the
identity chart: its real derivative at `v` is `D₂μ(φ(v), 0)`, where `φ` is `exp` in the chart and
`μ` the chart group law (`exp(v + w) = exp(v) · exp(w)`), and `D₂μ` is complex linear because `μ`
is analytic (`analyticAt_chartGroupLaw`).

Source: Mumford, *Abelian Varieties*, §1 (the exponential of a complex Lie group is holomorphic);
S12's `contDiffAt_complexExponential_chart`, `hasFDerivAt_complexExponential_chart` and
`complexExponentialHom`, with `analyticAt_chartGroupLaw` (`ChartGroupLaw.lean`). -/
theorem spec_eventually_differentiableAt_complexExponential_chart (X : Over (Spec ↧ℂ))
    (d : ℕ) [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] :
    ∀ᶠ v in 𝓝 (0 : Fin d → ℂ),
      DifferentiableAt ℂ (fun w ↦ identityChart X d (complexExponential X d w).toMul) v :=
  spec_eventually_differentiableAt_complexExponential_chart_aux X d

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] :
    DifferentiableAt ℂ (fun w ↦ identityChart X d (complexExponential X d w).toMul) 0 :=
  (spec_eventually_differentiableAt_complexExponential_chart X d).self_of_nhds

/-- On compact `X(ℂ)`, every global holomorphic function is locally constant (maximum modulus on
a compact complex manifold).

Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §1; Mathlib's
`MDifferentiable.isLocallyConstant` (`Mathlib/Geometry/Manifold/Complex.lean`), with upstream's
`holomorphicFunctionSheaf_section_analytic`. -/
theorem spec_isLocallyConstant_globalHolomorphicFunction (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [CompactSpace (ComplexPoint X)]
    (f : (holomorphicFunctionSheaf X d).presheaf.obj (op ⊤)) :
    IsLocallyConstant f.1 :=
  spec_isLocallyConstant_globalHolomorphicFunction_aux X d f

example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom] [IsProjective X.hom]
    (f : (holomorphicFunctionSheaf X d).presheaf.obj (op ⊤)) :
    IsLocallyConstant f.1 :=
  spec_isLocallyConstant_globalHolomorphicFunction X d f

/-- Global holomorphic functions on `X(ℂ)` and global sections of the sheaf `Ω^0` of holomorphic
`0`-forms agree: on each open, `⋀^0 Ω_{𝒪(U)/ℂ} = 𝒪(U)` and a function vanishing in every chart is
zero, so `holomorphicFunctionsToZeroForms` is an isomorphism of presheaves, and the presheaf of
holomorphic functions is already a sheaf.

Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §6 (`Ω^0 = 𝒪`); Mathlib's
`exteriorPower` in degree `0` and `isIso_toSheafify`. -/
theorem spec_globalHolomorphicFunctionToZeroForm_bijective (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    Function.Bijective (globalHolomorphicFunctionToZeroForm X d) :=
  spec_globalHolomorphicFunctionToZeroForm_bijective_aux X d

example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (s : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (holomorphicDeRhamSheaf X d 0)) :
    ∃ f, globalHolomorphicFunctionToZeroForm X d f = s :=
  (spec_globalHolomorphicFunctionToZeroForm_bijective X d).2 s

/-- A locally constant global holomorphic function on `X(ℂ)` gives a global section of `Ω^0` that
comes from the constant sheaf `ℂ_X`: locally it is the image of a constant, and these constants
glue to a locally constant section of `ℂ_X`.

Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §1; upstream
`constantsToHolomorphicDeRhamZeroSheaf` and `Algebra.DeRham.ofConstant_apply`. -/
theorem spec_globalHolomorphicFunctionToZeroForm_mem_range (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (f : (holomorphicFunctionSheaf X d).presheaf.obj (op ⊤)) (hf : IsLocallyConstant f.1) :
    globalHolomorphicFunctionToZeroForm X d f ∈ Set.range
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (constantsToHolomorphicDeRhamZeroSheaf X d)).hom :=
  spec_globalHolomorphicFunctionToZeroForm_mem_range_aux X d f hf

example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (f : (holomorphicFunctionSheaf X d).presheaf.obj (op ⊤)) (hf : IsLocallyConstant f.1) :
    ∃ c, ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (constantsToHolomorphicDeRhamZeroSheaf X d)).hom c =
      globalHolomorphicFunctionToZeroForm X d f :=
  spec_globalHolomorphicFunctionToZeroForm_mem_range X d f hf

/-- For smooth integral `X` with compact `X(ℂ)`, stage 4c's premise `hconst` holds: every global
section of `Ω^0` comes from the constant sheaf `ℂ_X`. This assembles the previous three statements.

Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §1, through
`spec_globalHolomorphicFunctionToZeroForm_bijective`,
`spec_isLocallyConstant_globalHolomorphicFunction` and
`spec_globalHolomorphicFunctionToZeroForm_mem_range`. -/
theorem spec_zeroForms_mem_range_constants_of_compactSpace (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [CompactSpace (ComplexPoint X)] :
    ∀ f : GlobalHolomorphicForm X 0, f ∈ Set.range
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
          (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))).hom :=
  spec_zeroForms_mem_range_constants_of_compactSpace_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (hz : cycleDeRhamClass X z = 0) :
    z = 0 :=
  spec_cycleDeRhamClass_injective_of_constant X
    (spec_zeroForms_mem_range_constants_of_compactSpace X) (hz.trans (map_zero _).symm)

/-- For smooth integral projective `X` (for instance abelian `X`), the de Rham class map on closed
global holomorphic `1`-forms is injective: the implication from stage 4c's
`spec_cycleDeRhamClass_injective_of_constant`, with its premise discharged by compactness of
`X(ℂ)` (upstream `IsProjective.complexPoint_compactSpace`).

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.3; Griffiths–Harris,
*Principles of Algebraic Geometry*, Ch. 0 §1; through
`spec_zeroForms_mem_range_constants_of_compactSpace`. -/
theorem spec_cycleDeRhamClass_injective_of_isProjective (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Function.Injective (cycleDeRhamClass X) :=
  spec_cycleDeRhamClass_injective_of_isProjective_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (hz : cycleDeRhamClass X z = 0) :
    cycleOneForm X z = 0 := by
  rw [spec_cycleDeRhamClass_injective_of_isProjective X (hz.trans (map_zero _).symm), map_zero]

end HodgeLean.Adapters

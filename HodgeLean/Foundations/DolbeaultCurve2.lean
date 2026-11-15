import HodgeLean.Foundations.DolbeaultCurve2Proofs
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # The Dolbeault sequence on `X(ℂ)`, stage 2: the `∂̄`-Poincaré lemma on curves (FROZEN SPEC)

Scope. The dolb spec (`DolbeaultCurve.lean`) proves `H^2(X(ℂ), 𝒪) = 0` and `CycleClassIsHodge X`
for an integral smooth (projective) curve as an implication from three binders: `∂̄` is an
epimorphism of sheaves (`hε`), `ℍ^2(𝒜^{0,0}[0]) = 0` (`hA`) and `ℍ^1(𝒜^{0,1}[0]) = 0` (`hB`).
This stage discharges `hε`.

* The `∂̄`-Poincaré lemma in one variable (statements 1–6): `1/z` is locally integrable on `ℂ`; the
  Cauchy–Pompeiu formula for a compactly supported `C^1` function `g`,
  `∫ (∂g/∂w̄)(w) / (z − w) dA(w) = π g(z)`; the Cauchy transform
  `T g (z) = (1/π) ∫ g(w) / (z − w) dA(w)` of a compactly supported `C^n` function is `C^n`, and
  `∂(T g)/∂z̄ = g` for `g` compactly supported and `C^1`. Two falsification checks pin the
  normalization (`∂z̄/∂z̄ = 1`) and the role of compact support (`T 1 = 0`).
* Transport to a Riemann surface (statements 7, 8): on `X(ℂ)` of relative dimension `1`, every
  smooth `(0,1)`-form is locally `∂̄` of a smooth function, so `∂̄ : 𝒜^{0,0} ⟶ 𝒜^{0,1}` is an
  epimorphism of sheaves.
* A first step toward fineness (statement 9): smooth `(0,1)`-forms are stable under multiplication
  by smooth functions, pointwise.
* Assembly (statements 10, 11): `H^2(X(ℂ), 𝒪) = 0` and `CycleClassIsHodge X` for a curve as an
  implication from the two acyclicity binders `hA` and `hB` only.

Claimed: statements 1–6 on `ℂ` as stated; statements 7, 8 for relative dimension `1`; statement 9 in
every dimension; `H^2(X(ℂ), 𝒪) = 0` and `CycleClassIsHodge X` for every integral smooth
(projective) curve as an implication from `hA` and `hB`.

Not claimed: acyclicity of `𝒜^{0,0}` or `𝒜^{0,1}`, or any notion of fine or soft sheaf; a sheaf of
`𝒜^{0,0}`-modules structure on `𝒜^{0,1}` (only the pointwise statement 9); the `∂̄`-Poincaré lemma
in several variables or `Epi ∂̄` for `d ≥ 2` (false there); `CycleClassIsHodge X` for curves
unconditionally. No new `@[hodge_hypothesis]`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open MeasureTheory CategoryTheory TopologicalSpace AlgebraicGeometry ComplexPoint
open scoped ContDiff Manifold
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations

/-- **`1/z` is locally integrable on `ℂ`.** In real dimension two, `‖z‖⁻¹` is integrable near `0`
(`∫_0^R r⁻¹ · r dr < ∞` in polar coordinates).
Source: Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., proof of
Theorem 1.2.2; Mathlib's `locallyIntegrable_of_norm_le_rpow` (`‖x‖^(-α)` with `α < dim`). -/
theorem spec_locallyIntegrable_inv : LocallyIntegrable (fun z : ℂ => z⁻¹) volume :=
  spec_locallyIntegrable_inv_aux

/-- In particular `1/z` is integrable on the closed unit disc. -/
example : IntegrableOn (fun z : ℂ => z⁻¹) (Metric.closedBall 0 1) volume :=
  spec_locallyIntegrable_inv.integrableOn_isCompact (isCompact_closedBall 0 1)

/-- **Cauchy–Pompeiu formula, compactly supported case.** For a `C^1` function `g : ℂ → ℂ` with
compact support and any `z`, `∫ (∂g/∂w̄)(w) / (z − w) dA(w) = π g(z)`. In polar coordinates
`w = z + r e^{iθ}` the integrand times `r` is `−(∂_r + (i/r) ∂_θ) g / 2`; the angular term
integrates to zero by periodicity and the radial one to `−g(z)`.
Source: Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
Theorem 1.2.1 (the generalized Cauchy integral formula) applied on a disc containing the support;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2. -/
theorem spec_integral_wirtingerDbar_div {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (z : ℂ) :
    ∫ w, wirtingerDbar g w / (z - w) = Real.pi * g z :=
  spec_integral_wirtingerDbar_div_aux hg hc z

/-- A compactly supported `C^1` function with vanishing `∂/∂z̄` everywhere is zero. -/
example {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (h : ∀ w, wirtingerDbar g w = 0) (z : ℂ) : g z = 0 := by
  have e := spec_integral_wirtingerDbar_div hg hc z
  simp only [h, zero_div, integral_zero] at e
  exact (mul_eq_zero.1 e.symm).resolve_left (by exact_mod_cast Real.pi_ne_zero)

/-- **The Cauchy transform is as smooth as its compactly supported argument.** For `g` of class
`C^n` with compact support, `T g = (1/π) g ⋆ (1/z)` is `C^n`: a convolution of a compactly
supported `C^n` function with a locally integrable kernel.
Source: Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
Theorem 1.2.2; Mathlib's `HasCompactSupport.contDiff_convolution_left`. -/
theorem spec_contDiff_cauchyTransform {n : ℕ∞} {g : ℂ → ℂ} (hg : ContDiff ℝ n g)
    (hc : HasCompactSupport g) :
    ContDiff ℝ n (cauchyTransform g) :=
  spec_contDiff_cauchyTransform_aux hg hc

/-- The smooth case. -/
example {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ContDiff ℝ ∞ (cauchyTransform g) :=
  spec_contDiff_cauchyTransform (n := ⊤) hg hc

/-- **The `∂̄`-Poincaré lemma in one variable.** For `g : ℂ → ℂ` of class `C^1` with compact support,
the Cauchy transform solves `∂f/∂z̄ = g` on all of `ℂ`: differentiating under the convolution gives
`∂(T g)/∂z̄ = (1/π) ∫ (∂g/∂w̄)(w) / (z − w) dA(w)`, which is `g(z)` by statement 2.
Source: Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
Theorem 1.2.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the `∂̄`-Poincaré
lemma in one variable). -/
theorem spec_wirtingerDbar_cauchyTransform {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (z : ℂ) :
    wirtingerDbar (cauchyTransform g) z = g z :=
  spec_wirtingerDbar_cauchyTransform_aux hg hc z

/-- Every smooth compactly supported function on `ℂ` is `∂/∂z̄` of a smooth function. -/
example {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧ ∀ z, wirtingerDbar f z = g z :=
  ⟨cauchyTransform g, spec_contDiff_cauchyTransform (n := ⊤) hg hc,
    spec_wirtingerDbar_cauchyTransform (hg.of_le (by simp)) hc⟩

/-- **Falsification check: the normalization of `∂/∂z̄`.** `∂z̄/∂z̄ = 1`: the real derivative of
`conj` is `conj`, which is conjugate-linear, so its conjugate-linear part at `1` is `conj 1 = 1`. A
factor `2` or a sign in `antiLinearPart` or in `cauchyTransform` would break statement 4 against
this one.
Source: Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., §1.1
(`∂z̄/∂z̄ = 1`, `∂z/∂z̄ = 0`). -/
theorem spec_wirtingerDbar_conj (z : ℂ) :
    wirtingerDbar (starRingEnd ℂ) z = 1 :=
  spec_wirtingerDbar_conj_aux z

/-- So `conj` is not holomorphic in the sense of `∂/∂z̄`. -/
example : wirtingerDbar (starRingEnd ℂ) 0 ≠ 0 := by
  rw [spec_wirtingerDbar_conj]
  exact one_ne_zero

/-- **Falsification check: compact support is needed in statement 4.** The function
`w ↦ 1 / (z − w)` is not integrable on `ℂ` (it decays like `‖w‖⁻¹` in real dimension two), so the
Bochner integral defining `T 1` is `0`. Hence `∂(T 1)/∂z̄ = 0 ≠ 1`, and statement 4 fails without
`HasCompactSupport`.
Source: Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.2.2
(stated for compactly supported data); Mathlib's `integral_undef`. -/
theorem spec_cauchyTransform_one (z : ℂ) :
    cauchyTransform (fun _ => 1) z = 0 :=
  spec_cauchyTransform_one_aux z

/-- Statement 4 without compact support fails for the constant `1`. -/
example : ¬ ∀ z, wirtingerDbar (cauchyTransform fun _ => 1) z = 1 := by
  intro h
  have e : cauchyTransform (fun _ => 1) = fun _ => 0 := funext spec_cauchyTransform_one
  have h0 := h 0
  rw [e] at h0
  simp [wirtingerDbar] at h0

/-- **Local solvability of `∂̄` on a Riemann surface.** If `X` has relative dimension `1`, every
smooth `(0,1)`-form `σ` on an open `U ⊆ X(ℂ)` is, near each point `x ∈ U`, the `∂̄` of a smooth
function: in the chart at `x`, `σ = h dz̄` with `h` smooth; cut `h` off by a bump function, apply
statements 3 and 4 in the chart, and pull back.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the `∂̄`-Poincaré lemma in
one variable) and §3 (exactness of `0 → 𝒪 → 𝒜^{0,0} → 𝒜^{0,1} → 0`); Hörmander, *An Introduction
to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.2.2. -/
theorem spec_exists_dbarSection_eq (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    {U : Opens (ComplexPoint X)} (σ : zeroOneFormSubgroup X 1 U) (x : U) :
    ∃ (V : Opens (ComplexPoint X)) (i : V ≤ U), (x : ComplexPoint X) ∈ V ∧
      ∃ f : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), V; 𝓘(ℝ, ℂ), ℂ⟯,
        ∀ y : V, dbarSection X 1 f y = (σ : ∀ _ : U, (Fin 1 → ℂ) →L[ℝ] ℂ) ⟨y, i y.2⟩ :=
  spec_exists_dbarSection_eq_aux X σ x

/-- A global smooth `(0,1)`-form is locally `∂̄` of a smooth function. -/
example (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (σ : zeroOneFormSubgroup X 1 ⊤) (x : ComplexPoint X) :
    ∃ (V : Opens (ComplexPoint X)), x ∈ V ∧
      ∃ f : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), V; 𝓘(ℝ, ℂ), ℂ⟯,
        ∀ y : V, dbarSection X 1 f y =
          (σ : ∀ _ : (⊤ : Opens (ComplexPoint X)), (Fin 1 → ℂ) →L[ℝ] ℂ) ⟨y, trivial⟩ := by
  obtain ⟨V, _, hx, f, hf⟩ := spec_exists_dbarSection_eq X σ ⟨x, trivial⟩
  exact ⟨V, hx, f, hf⟩

/-- **`∂̄` is an epimorphism of sheaves on a Riemann surface.** For relative dimension `d = 1`,
`∂̄ : 𝒜^{0,0} ⟶ 𝒜^{0,1}` is an epimorphism in the category of sheaves of abelian groups on
`X(ℂ)`: by statement 7 it is locally surjective. This is the binder `hε` of the dolb assemblies.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2–3 (the Dolbeault sequence
`0 → 𝒪 → 𝒜^{0,0} → 𝒜^{0,1} → 0` on a Riemann surface is exact); Mathlib's
`isLocallySurjective_iff_epi'`. -/
theorem spec_epi_dbar (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (hd : d = 1) :
    Epi (dbar X d) :=
  spec_epi_dbar_aux X d hd

/-- For an integral smooth curve, in the dimension used by `Ω•(X)`: the binder `hε` of
`spec_subsingleton_hypercohomology_two_of_dbar`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] :
    Epi (dbar X (dim X.left)) :=
  spec_epi_dbar X _ (SmoothOfRelativeDimension.dim_eq X.hom 1)

/-- **Smooth `(0,1)`-forms are a module over smooth functions, pointwise.** If `f` is smooth at `x`
and `σ` is a smooth `(0,1)`-form at `x`, so is `f σ`: multiplying by a complex scalar keeps a
real-linear map conjugate-linear, and the product of smooth maps is smooth. This is the module
structure that makes `𝒜^{0,1}` fine once partitions of unity are available.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (`𝒜^{p,q}` is a module over
`𝒜^{0,0}`) and §3 (fine sheaves); Huybrechts, *Complex Geometry*, §2.6. -/
theorem spec_isZeroOneFormAt_smul {X : Over (Spec ↧ℂ)} {d : ℕ}
    [SmoothOfRelativeDimension d X.hom] {f : ComplexPoint X → ℂ}
    {σ : ComplexPoint X → (Fin d → ℂ) →L[ℝ] ℂ} {x : ComplexPoint X}
    (hf : ContMDiffAt 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) ∞ f x) (hσ : IsZeroOneFormAt X d σ x) :
    IsZeroOneFormAt X d (fun y => f y • σ y) x :=
  spec_isZeroOneFormAt_smul_aux hf hσ

/-- Constant multiples of smooth `(0,1)`-forms. -/
example {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom] (c : ℂ)
    {σ : ComplexPoint X → (Fin d → ℂ) →L[ℝ] ℂ} {x : ComplexPoint X}
    (hσ : IsZeroOneFormAt X d σ x) :
    IsZeroOneFormAt X d (fun y => c • σ y) x :=
  spec_isZeroOneFormAt_smul contMDiffAt_const hσ

/-- The other input of fineness is already available: smooth partitions of unity subordinate to any
open cover of `X(ℂ)` exist for projective `X` (upstream's `T2Space` and `CompactSpace`). -/
example (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    {ι : Type} (U : ι → Set (ComplexPoint X)) (hU : ∀ i, IsOpen (U i))
    (hc : ⋃ i, U i = Set.univ) :
    ∃ ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin 1 → ℂ) (ComplexPoint X) Set.univ, ρ.IsSubordinate U :=
  SmoothPartitionOfUnity.exists_isSubordinate _ isClosed_univ U hU (by simp [hc])

/-- **`H^2(X(ℂ), 𝒪) = 0` on a curve from the acyclicity binders alone.** For an integral smooth `X`
of dimension `1`, if `H^2(X(ℂ), 𝒜^{0,0}) = 0` and `H^1(X(ℂ), 𝒜^{0,1}) = 0`, then
`ℍ^2(X; holomorphicFormsShifted X 0) = H^2(X(ℂ), 𝒪)` vanishes: dolb's
`spec_subsingleton_hypercohomology_two_of_dbar` with its binder `hε` supplied by statement 8.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2–3 (Dolbeault's theorem on a
Riemann surface); Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.2. -/
theorem spec_subsingleton_hypercohomology_two_of_acyclic (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (hd : dim X.left = 1)
    (hA : Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))))
    (hB : Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left)))) :
    Subsingleton ℍ^2(X; holomorphicFormsShifted X 0) :=
  spec_subsingleton_hypercohomology_two_of_acyclic_aux X hd hA hB

/-- With the cch spec, the same binders give `F^1 H_dR^2(X) = F^0 H_dR^2(X)`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (hd : dim X.left = 1)
    (hA : Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))))
    (hB : Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left)))) :
    F^(0 + 1) H_dR^2(X) = F^0 H_dR^2(X) :=
  spec_hodgeFiltration_succ_eq_of_subsingleton X 0 2
    (spec_subsingleton_hypercohomology_two_of_acyclic X hd hA hB)

/-- **Assembly: `CycleClassIsHodge` for curves from the acyclicity binders alone.** For an integral
smooth projective curve `X` over `ℂ`, if `H^2(X(ℂ), 𝒜^{0,0}) = 0` and `H^1(X(ℂ), 𝒜^{0,1}) = 0`,
then `CycleClassIsHodge X`: dolb's `spec_cycleClassIsHodge_of_curve_of_dbar` with its binder `hε`
supplied by statement 8.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2–3; Voisin, *Hodge Theory
and Complex Algebraic Geometry I*, §§11.1.2–11.1.3 (cycle classes are of type `(p, p)`). -/
theorem spec_cycleClassIsHodge_of_curve_of_acyclic (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (hA : Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))))
    (hB : Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left)))) :
    CycleClassIsHodge X :=
  spec_cycleClassIsHodge_of_curve_of_acyclic_aux X hA hB

/-- The codimension-one part, with the same binders. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (hA : Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))))
    (hB : Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left)))) :
    algebraicCycleClassSpan X 1 ≤ Hdg^1(X; ℚ) :=
  (spec_cycleClassIsHodge_of_curve_of_acyclic X hA hB).le 1

end HodgeLean.Foundations

import HodgeLean.Foundations.AppellHumbertSectionsProofs

/-! # Appell--Humbert sections and the degree-two class (FROZEN SPEC)

Scope. This module specifies, on the analytic and lattice side only:
* theta functions for an Appell--Humbert datum, as the `ℂ`-submodule `sections D` of entire
  functions satisfying `θ (v + l) = holFactor D l v * θ v`; the cocycle of `holFactor`, reduction to
  generators, translation (twist by `exp(2πi E(·, w))`), products (tensor of data), the trivial datum
  (sections are the constants), and in genus one a nonzero theta function built from Mathlib's
  `jacobiTheta₂`;
* a convention check: the frozen `AppellHumbert.factor` (conjugate-linear in `v` under this
  repository's Hermitian convention) has no nonzero holomorphic solution once `H ≠ 0`;
* the implication from an integral alternating form on the lattice to a class in
  `⋀² (Λ →+ ℚ)`, additive and injective on alternating forms, and the implication from positive
  definiteness of `H` to nondegeneracy and nonvanishing `g`-th exterior power of that class.

Not claimed: that `sections D` is the space of global sections of a holomorphic line bundle, that
the degree-two class is the first Chern class of any line bundle, its transport to `HQ X 2`
(which needs the degree-one lattice bridge and `abelianTorusComparison`), the dimension
`det(E)^{1/2}` of the section space (Riemann--Roch for abelian varieties), the analytic Picard
group, the exponential sequence, or GAGA. HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.AppellHumbert

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The holomorphic Appell--Humbert factor satisfies the translation cocycle identity. Unlike the
frozen `factor`, no integrality is used: the semicharacter multiplier `exp(iπE(l,m))` and
`(π/2)(H(l,m) + H(m,l))` add up to `π H(l,m)` exactly.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 and Theorem 2.2.3. -/
theorem spec_holFactor_cocycle (D : Datum (V := V)) (l m : D.lattice) (v : V) :
    holFactor D (l + m) v = holFactor D l (v + m) * holFactor D m v :=
  spec_holFactor_cocycle_aux D l m v

example (D : Datum (V := V)) (l m : D.lattice) (v : V) :
    holFactor D (l + m) v = holFactor D l (v + m) * holFactor D m v :=
  spec_holFactor_cocycle D l m v

/-- The holomorphic factor is `1` at the origin of the lattice: `χ(0) = 1` follows from the
semicharacter identity at `(0,0)`, and `H(0,0) = 0`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.2. -/
theorem spec_holFactor_zero (D : Datum (V := V)) (v : V) : holFactor D 0 v = 1 :=
  spec_holFactor_zero_aux D v

example (D : Datum (V := V)) (v : V) : holFactor D 0 v = 1 :=
  spec_holFactor_zero D v

/-- The functional equation on a generating set of the lattice implies it on the whole lattice,
so an entire function satisfying it on generators is a theta function. The cocycle identity and
`holFactor D 0 = 1` are the reason (negatives use that the factor never vanishes).
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 and §3.1. -/
theorem spec_sections_of_generators (D : Datum (V := V)) (S : Set D.lattice)
    (hS : AddSubgroup.closure S = ⊤) (θ : V → ℂ) (hθ : Differentiable ℂ θ)
    (hgen : ∀ l ∈ S, ∀ v : V, θ (v + l) = holFactor D l v * θ v) :
    θ ∈ sections D :=
  spec_sections_of_generators_aux D S hS θ hθ hgen

example (D : Datum (V := V)) (S : Set D.lattice)
    (hS : AddSubgroup.closure S = ⊤) (θ : V → ℂ) (hθ : Differentiable ℂ θ)
    (hgen : ∀ l ∈ S, ∀ v : V, θ (v + l) = holFactor D l v * θ v) :
    θ ∈ sections D :=
  spec_sections_of_generators D S hS θ hθ hgen

/-- Translation by an arbitrary `w ∈ V`, corrected by the exponential `exp(-π H(w, v))`, maps theta
functions of `D` to theta functions of the twist `D.twist w`, whose semicharacter is multiplied by
`exp(2πi E(·, w))`. This is the functional-equation form of `t_w^* L(H, χ) = L(H, χ · e(E(·, w)))`;
the line-bundle form is not claimed.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 2.3.2. -/
theorem spec_sections_translate (D : Datum (V := V)) (w : V) (θ : V → ℂ)
    (hθ : θ ∈ sections D) :
    (fun v ↦ Complex.exp (-(Real.pi * D.hermitian.toFun w v)) * θ (v + w)) ∈
      sections (D.twist w) :=
  spec_sections_translate_aux D w θ hθ

example (D : Datum (V := V)) (w : V) (θ : V → ℂ)
    (hθ : θ ∈ sections D) :
    (fun v ↦ Complex.exp (-(Real.pi * D.hermitian.toFun w v)) * θ (v + w)) ∈
      sections (D.twist w) :=
  spec_sections_translate D w θ hθ

/-- For a lattice point `m`, the twist is trivial on the semicharacter, since `E(l, m)` is an
integer; combined with `spec_sections_translate`, translation by a lattice point preserves the
functional equation of `D` itself.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 2.3.2 and Theorem 2.2.3. -/
theorem spec_twist_lattice (D : Datum (V := V)) (m : D.lattice) :
    (D.twist m).semicharacter = D.semicharacter :=
  spec_twist_lattice_aux D m

example (D : Datum (V := V)) (m : D.lattice) :
    (D.twist m).semicharacter = D.semicharacter :=
  spec_twist_lattice D m

/-- The product of theta functions of two data is a theta function of their tensor product: the
holomorphic factor is multiplicative in the datum.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3 and §3.1. -/
theorem spec_sections_mul (D₁ D₂ : Datum (V := V)) (h : D₁.lattice ≤ D₂.lattice)
    (θ₁ θ₂ : V → ℂ) (h₁ : θ₁ ∈ sections D₁) (h₂ : θ₂ ∈ sections D₂) :
    θ₁ * θ₂ ∈ sections (D₁.tensor D₂ h) :=
  spec_sections_mul_aux D₁ D₂ h θ₁ θ₂ h₁ h₂

example (D₁ D₂ : Datum (V := V)) (h : D₁.lattice ≤ D₂.lattice)
    (θ₁ θ₂ : V → ℂ) (h₁ : θ₁ ∈ sections D₁) (h₂ : θ₂ ∈ sections D₂) :
    θ₁ * θ₂ ∈ sections (D₁.tensor D₂ h) :=
  spec_sections_mul D₁ D₂ h θ₁ θ₂ h₁ h₂

/-- For the trivial datum (`H = 0`, `χ = 1`) the theta functions are exactly the constants:
they are lattice-periodic entire functions, hence bounded, hence constant by Liouville.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §3.1; Liouville's theorem
(`Differentiable.apply_eq_apply_of_bounded`). -/
theorem spec_trivial_sections (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (θ : V → ℂ) : θ ∈ sections (Datum.trivial L) ↔ ∃ c : ℂ, θ = fun _ ↦ c :=
  spec_trivial_sections_aux L θ

example (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (θ : V → ℂ) : θ ∈ sections (Datum.trivial L) ↔ ∃ c : ℂ, θ = fun _ ↦ c :=
  spec_trivial_sections L θ

/-- Convention check for the frozen core: the frozen `factor` evaluates `H v l`, which is
conjugate-linear in `v`, so as soon as `H(l, ·) ≠ 0` for some lattice point `l` its only
holomorphic solution is `0`. Theta functions must therefore be built on `holFactor`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 (factors of automorphy are
holomorphic in `v`); the Cauchy--Riemann equations. -/
theorem spec_factor_no_holomorphic_solutions (D : Datum (V := V))
    (hH : ∃ (l : D.lattice) (w : V), D.hermitian.toFun l w ≠ 0) (θ : V → ℂ)
    (hθ : Differentiable ℂ θ) (hfe : ∀ (l : D.lattice) (v : V), θ (v + l) = factor D l v * θ v) :
    θ = 0 :=
  spec_factor_no_holomorphic_solutions_aux D hH θ hθ hfe

example (D : Datum (V := V))
    (hH : ∃ (l : D.lattice) (w : V), D.hermitian.toFun l w ≠ 0) (θ : V → ℂ)
    (hθ : Differentiable ℂ θ) (hfe : ∀ (l : D.lattice) (v : V), θ (v + l) = factor D l v * θ v) :
    θ = 0 :=
  spec_factor_no_holomorphic_solutions D hH θ hθ hfe

/-- For a positive-definite datum, the degree-two class of `E = Im H` in `⋀² Hom(Λ, ℚ)` is a
nondegenerate 2-vector. Positive definite gives `E` nondegenerate on `V`
(`spec_positive_imaginary_nondegenerate`), and a `ℤ`-basis of `Λ` is an `ℝ`-basis of `V`, so the
Gram matrix of `E` on it is invertible.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 and Lemma 1.3.1. -/
theorem spec_latticeClass_positive_nondegenerate (D : Datum (V := V))
    [Module.Free ℤ D.lattice] [Module.Finite ℤ D.lattice]
    (hH : D.hermitian.IsPositiveDefinite) :
    Symplectic.IsNondegenerate (latticeClass D.imForm) :=
  spec_latticeClass_positive_nondegenerate_aux D hH

example (D : Datum (V := V))
    [Module.Free ℤ D.lattice] [Module.Finite ℤ D.lattice]
    (hH : D.hermitian.IsPositiveDefinite) :
    Symplectic.IsNondegenerate (latticeClass D.imForm) :=
  spec_latticeClass_positive_nondegenerate D hH

/-- For a positive-definite datum on `V` of complex dimension `g`, the `g`-th exterior power of the
degree-two class is nonzero in `⋀^{2g} Hom(Λ, ℚ)`. It follows from
`spec_latticeClass_positive_nondegenerate`, `rank Λ = 2g` and
`Symplectic.wedgePow_ne_zero_of_isNondegenerate`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 and Lemma 1.3.1; Bourbaki,
*Algèbre*, ch. IX, §5. -/
theorem spec_latticeClass_wedgePow_ne_zero (D : Datum (V := V))
    [Module.Free ℤ D.lattice] [Module.Finite ℤ D.lattice]
    (hH : D.hermitian.IsPositiveDefinite) :
    Symplectic.wedgePow (latticeClass D.imForm) (Module.finrank ℂ V) ≠ 0 :=
  spec_latticeClass_wedgePow_ne_zero_aux D hH

example (D : Datum (V := V))
    [Module.Free ℤ D.lattice] [Module.Finite ℤ D.lattice]
    (hH : D.hermitian.IsPositiveDefinite) :
    Symplectic.wedgePow (latticeClass D.imForm) (Module.finrank ℂ V) ≠ 0 :=
  spec_latticeClass_wedgePow_ne_zero D hH

/-- Falsification: the trivial datum (`H = 0`) has all constants as theta functions, while its
degree-two class and all its positive exterior powers vanish. This separates the trivial bundle
from a polarization.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3 and §4.1. -/
theorem spec_trivial_datum_falsification (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] [Module.Free ℤ (Datum.trivial L).lattice]
    [Module.Finite ℤ (Datum.trivial L).lattice] :
    (∀ c : ℂ, (fun _ : V ↦ c) ∈ sections (Datum.trivial L)) ∧
      latticeClass (Datum.trivial L).imForm = 0 ∧
      ∀ g : ℕ, 0 < g → Symplectic.wedgePow (latticeClass (Datum.trivial L).imForm) g = 0 :=
  spec_trivial_datum_falsification_aux L

example (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] [Module.Free ℤ (Datum.trivial L).lattice]
    [Module.Finite ℤ (Datum.trivial L).lattice] :
    (∀ c : ℂ, (fun _ : V ↦ c) ∈ sections (Datum.trivial L)) ∧
      latticeClass (Datum.trivial L).imForm = 0 ∧
      ∀ g : ℕ, 0 < g → Symplectic.wedgePow (latticeClass (Datum.trivial L).imForm) g = 0 :=
  spec_trivial_datum_falsification L

end Lattice

/-- Genus one: for `Im τ > 0`, on `Λ = ℤ + τℤ` with `H(z, w) = conj(z) w / Im τ` (positive, of
degree one) there is a semicharacter (namely `χ(a + bτ) = (-1)^{ab}`) for which
`exp(π z² / (2 Im τ)) · ϑ(z, τ)` is a nonzero theta function. The transformation formulas used
are Mathlib's `jacobiTheta₂_add_left` (`ϑ(z + 1, τ) = ϑ(z, τ)`) and `jacobiTheta₂_add_left'`
(`ϑ(z + τ, τ) = exp(-πi(τ + 2z)) ϑ(z, τ)`), with `differentiableAt_jacobiTheta₂_fst`.
Source: Mathlib `NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:385`, `:391`, `:328`;
Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §3.1 and §8.5 (classical factor vs
canonical factor). -/
theorem spec_jacobiTheta₂_section (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ D : Datum (V := ℂ), D.lattice = Submodule.span ℤ {1, τ} ∧
      (∀ z w : ℂ, D.hermitian.toFun z w = star z * w / τ.im) ∧
      D.hermitian.IsPositiveDefinite ∧
      (fun z ↦ Complex.exp (Real.pi * z ^ 2 / (2 * τ.im)) * jacobiTheta₂ z τ) ∈ sections D ∧
      (fun z ↦ Complex.exp (Real.pi * z ^ 2 / (2 * τ.im)) * jacobiTheta₂ z τ) ≠ 0 :=
  spec_jacobiTheta₂_section_aux τ hτ

example (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ D : Datum (V := ℂ), D.lattice = Submodule.span ℤ {1, τ} ∧
      (∀ z w : ℂ, D.hermitian.toFun z w = star z * w / τ.im) ∧
      D.hermitian.IsPositiveDefinite ∧
      (fun z ↦ Complex.exp (Real.pi * z ^ 2 / (2 * τ.im)) * jacobiTheta₂ z τ) ∈ sections D ∧
      (fun z ↦ Complex.exp (Real.pi * z ^ 2 / (2 * τ.im)) * jacobiTheta₂ z τ) ≠ 0 :=
  spec_jacobiTheta₂_section τ hτ

section LatticeClass

variable {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]

/-- The degree-two class is additive in the integral form.
Source: Bourbaki, *Algèbre*, ch. III, §11. -/
theorem spec_latticeClass_add (E₁ E₂ : Λ →+ Λ →+ ℤ) :
    latticeClass (E₁ + E₂) = latticeClass E₁ + latticeClass E₂ :=
  spec_latticeClass_add_aux E₁ E₂

example (E₁ E₂ : Λ →+ Λ →+ ℤ) :
    latticeClass (E₁ + E₂) = latticeClass E₁ + latticeClass E₂ :=
  spec_latticeClass_add E₁ E₂

/-- On alternating integral forms the degree-two class is injective: the coefficient of
`eᵢ* ∧ eⱼ*` (`i < j`) in the class is `E(eᵢ, eⱼ)`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1; Bourbaki, *Algèbre*,
ch. III, §11. -/
theorem spec_latticeClass_injective (E₁ E₂ : Λ →+ Λ →+ ℤ)
    (h₁ : ∀ x, E₁ x x = 0) (h₂ : ∀ x, E₂ x x = 0)
    (h : latticeClass E₁ = latticeClass E₂) : E₁ = E₂ :=
  spec_latticeClass_injective_aux E₁ E₂ h₁ h₂ h

example (E₁ E₂ : Λ →+ Λ →+ ℤ)
    (h₁ : ∀ x, E₁ x x = 0) (h₂ : ∀ x, E₂ x x = 0)
    (h : latticeClass E₁ = latticeClass E₂) : E₁ = E₂ :=
  spec_latticeClass_injective E₁ E₂ h₁ h₂ h

end LatticeClass

end HodgeLean.Foundations.AppellHumbert

import HodgeLean.Adapters.ThetaExistenceProofs

/-! # Theta functions exist for positive `H` (BL §3.2): frozen specification

Scope (Appell–Humbert stage 5b, the existence item deferred by stage 5a,
`docs/specs/AutomorphyLineBundleOnX.md`). For an Appell–Humbert datum `D` on a full lattice `Λ` in a
finite-dimensional complex normed space `V` (any dimension), with factor `a = holFactor D`, the
Poincaré theta series `P_D(v) = Σ_{l ∈ Λ} a(l, v)⁻¹` (`poincareTheta`) is used. Claimed:
* for every `D`, the series obeys the functional equation of `D` (cocycle and reindexing; when the
  series diverges, Lean's `tsum` is `0` and the identity holds trivially);
* for positive definite `H`, the series converges absolutely, is entire, and is a theta function of
  `D`;
* Fourier uniqueness on `V` for a full lattice and a nondegenerate `E = Im H`: a summable family
  `c` on `Λ` with `c 0 ≠ 0` gives a function `w ↦ Σ_l c(l) exp(2πi E(l, w))` that is not
  identically zero;
* for positive definite `H`, some twist `D.twist w` has a nonzero Poincaré series;
* as an implication from these, for positive definite `H`: `sections D ≠ ⊥`, in every dimension,
  for every semicharacter, with no decomposition of `Λ`; on an abelian `X`, for
  `D = datumOfX X H E hE χ hχ`, the bundle `L(H, χ)` on `X(ℂ)` has a nonzero global section.

Not claimed: that `P_D` itself is nonzero (it vanishes for odd characteristics); the dimension
`√det E` of `sections D` (BL Thm 3.2.7) or its finiteness; that `sections D ≠ ⊥` forces `H ≥ 0`;
a basis of classical theta functions with characteristics, a Frobenius decomposition of `E`, or
Riemann's theta function in `g` variables (bypassed); the divisor of a section with multiplicities;
any algebraicity, projective embedding (Lefschetz) or `LefschetzOneOneHyp`
(`docs/specs/ThetaExistence.md`).
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open scoped Manifold CategoryTheory.MonObj

namespace HodgeLean.Adapters

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- For positive definite `H` the Poincaré series converges absolutely at every point:
`|a(l, v)⁻¹| = exp(-π Re H(l, v) - (π/2) H(l, l))`, and `H(l, l) ≥ c ‖l‖²` with `c > 0` (positive
definite on a finite-dimensional space) beats the linear term; a full lattice has polynomially
many points in each ball.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §3.2 (convergence of the classical
theta series); Mumford, *Tata Lectures on Theta I*, Ch. II, §1. -/
theorem spec_summable_inv_holFactor (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) (v : V) :
    Summable (fun l : D.lattice ↦ (holFactor D l v)⁻¹) :=
  spec_summable_inv_holFactor_aux D hH v

example (D : Datum (V := V)) (hH : D.hermitian.IsPositiveDefinite) (v : V) :
    HasSum (fun l : D.lattice ↦ (holFactor D l v)⁻¹) (poincareTheta D v) :=
  (spec_summable_inv_holFactor D hH v).hasSum

/-- The Poincaré series satisfies the functional equation of `D`: by the cocycle identity
`a(k + l, v) = a(k, v + l) a(l, v)` (`spec_holFactor_cocycle`), `a(k, v + l)⁻¹ = a(l, v) a(k + l, v)⁻¹`,
and `k ↦ k + l` is a bijection of `Λ`. No hypothesis on `H` is needed: reindexing and pulling out a
constant factor are valid for `tsum` whether or not the series converges (when it diverges both
sides are `0`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 and §3.2;
`spec_holFactor_cocycle`. -/
theorem spec_poincareTheta_add (D : Datum (V := V)) (l : D.lattice) (v : V) :
    poincareTheta D (v + l) = holFactor D l v * poincareTheta D v :=
  spec_poincareTheta_add_aux D l v

example (D : Datum (V := V)) (l : D.lattice) :
    poincareTheta D l = holFactor D l 0 * poincareTheta D 0 := by
  simpa using spec_poincareTheta_add D l 0

/-- For positive definite `H` the Poincaré series is entire: each term
`χ(l)⁻¹ exp(-π H(l, v) - (π/2) H(l, l))` is complex-linear-exponential in `v`, and on every ball the
terms and their derivatives `-π H(l, ·)` times the term are bounded by a summable family
(`hasFDerivAt_tsum_of_isPreconnected`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §3.2; Mathlib
`hasFDerivAt_tsum_of_isPreconnected`. -/
theorem spec_differentiable_poincareTheta (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) :
    Differentiable ℂ (poincareTheta D) :=
  spec_differentiable_poincareTheta_aux D hH

example (D : Datum (V := V)) (hH : D.hermitian.IsPositiveDefinite) :
    Continuous (poincareTheta D) :=
  (spec_differentiable_poincareTheta D hH).continuous

/-- For positive definite `H` the Poincaré series is a theta function of `D`: it is entire
(`spec_differentiable_poincareTheta`) and satisfies the functional equation
(`spec_poincareTheta_add`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §3.1 and §3.2;
`spec_differentiable_poincareTheta`, `spec_poincareTheta_add`. -/
theorem spec_poincareTheta_mem_sections (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) :
    poincareTheta D ∈ sections D :=
  spec_poincareTheta_mem_sections_aux D hH

example (D : Datum (V := V)) (hH : D.hermitian.IsPositiveDefinite) (l : D.lattice) (v : V) :
    poincareTheta D (v + l) = holFactor D l v * poincareTheta D v :=
  (spec_poincareTheta_mem_sections D hH).2 l v

/-- Fourier uniqueness on `V`: for a full lattice `L` and a nondegenerate `E = Im H`, a summable
family `c` on `L` with `c 0 ≠ 0` gives a function `F(w) = Σ_l c(l) exp(2πi E(l, w))` on `V` that is
not identically zero. With a `ℤ`-basis `eⱼ` of `L` and the `E`-dual `ℝ`-basis `fₖ`
(`E(eⱼ, fₖ) = δⱼₖ`, by nondegeneracy), `F(Σ tₖ fₖ) = Σ_n c(n) exp(2πi n · t)` is an absolutely
convergent Fourier series on `ℝ^{2g} / ℤ^{2g}`, whose integral over `[0, 1]^{2g}` is `c 0`.
Source: Katznelson, *An Introduction to Harmonic Analysis*, Ch. I, §2 (uniqueness of Fourier
coefficients), in several variables; Mathlib `mFourierCoeff`. -/
theorem spec_exists_fourier_ne_zero (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (H : HermitianForm (V := V)) (hE : IsNondegenerate H.imaginary)
    (c : L → ℂ) (hc : Summable c) (h0 : c 0 ≠ 0) :
    ∃ w : V, ∑' l : L, c l * (Circle.exp (2 * Real.pi * H.imaginary l w) : ℂ) ≠ 0 :=
  spec_exists_fourier_ne_zero_aux L H hE c hc h0

open Classical in
example (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (H : HermitianForm (V := V))
    (hE : IsNondegenerate H.imaginary) :
    ∃ w : V, ∑' l : L, (if l = 0 then (1 : ℂ) else 0) *
      (Circle.exp (2 * Real.pi * H.imaginary l w) : ℂ) ≠ 0 :=
  spec_exists_fourier_ne_zero L H hE _
    (summable_of_ne_finset_zero (s := {0}) (fun l hl ↦ by simp_all)) (by simp)

/-- For positive definite `H`, some twist `D.twist w` has a nonzero Poincaré series. Its value at
`0` is `Σ_l c(l) exp(2πi E(l, -w))` with `c(l) = χ(l)⁻¹ exp(-(π/2) H(l, l))`, summable
(`spec_summable_inv_holFactor` at `0`) with `c 0 = 1`; apply `spec_exists_fourier_ne_zero` (positive
definite gives `E` nondegenerate: `E(v, iv) = Re H(v, v)`). The twist is needed: for an odd
characteristic `P_D` itself vanishes identically.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 2.3.2 and §3.2;
`spec_exists_fourier_ne_zero`. -/
theorem spec_exists_twist_poincareTheta_ne_zero (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) :
    ∃ w : V, poincareTheta (D.twist w) ≠ 0 :=
  spec_exists_twist_poincareTheta_ne_zero_aux D hH

example (D : Datum (V := V)) (hH : D.hermitian.IsPositiveDefinite) :
    ∃ w : V, ∃ v : V, poincareTheta (D.twist w) v ≠ 0 := by
  obtain ⟨w, hw⟩ := spec_exists_twist_poincareTheta_ne_zero D hH
  exact ⟨w, by simpa [funext_iff] using hw⟩

/-- Theta functions exist for positive `H`, in every dimension and for every semicharacter
(BL §3.2): `sections D ≠ ⊥`. Take `w` from `spec_exists_twist_poincareTheta_ne_zero`; `P_{D.twist w}`
is a nonzero theta function of `D.twist w` (`spec_poincareTheta_mem_sections`, same `H`); its
translate by `-w` (`spec_sections_translate`) is a nonzero theta function of
`(D.twist w).twist (-w)`, whose semicharacter is `χ(l) e(E(l, w)) e(E(l, -w)) = χ(l)`, so this datum
is `D`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §3.2 (existence of theta functions
for positive `H`) and Lemma 2.3.2; Mumford, *Abelian Varieties*, §3;
`spec_exists_twist_poincareTheta_ne_zero`, `spec_poincareTheta_mem_sections`,
`spec_sections_translate`. -/
theorem spec_sections_ne_bot (D : Datum (V := V)) (hH : D.hermitian.IsPositiveDefinite) :
    sections D ≠ ⊥ :=
  spec_sections_ne_bot_aux D hH

example (D : Datum (V := V)) (hH : D.hermitian.IsPositiveDefinite) :
    ∃ θ ∈ sections D, θ ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot (spec_sections_ne_bot D hH)

end General

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- On an abelian `X`, for positive definite `H` the bundle `L(H, χ)` on `X(ℂ)` has a nonzero global
section: `spec_sections_ne_bot` for `datumOfX X H E hE χ hχ`, and a theta function `θ` gives the
global section `x ↦ θ x` on `exp⁻¹(X(ℂ)) = ℂ^g` (this identification is stage 5a's
`spec_globalSectionsX`; it is the identity on values).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.2, §3.1 and §3.2;
`spec_sections_ne_bot`, `sectionsOnX`. -/
theorem spec_sectionsOnX_ne_bot (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (hH : H.IsPositiveDefinite) :
    sectionsOnX X (holFactor (datumOfX X H E hE χ hχ)) Set.univ ≠ ⊥ :=
  spec_sectionsOnX_ne_bot_aux X H E hE χ hχ hH

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (hH : H.IsPositiveDefinite) :
    ∃ f ∈ sectionsOnX X (holFactor (datumOfX X H E hE χ hχ)) Set.univ, f ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot (spec_sectionsOnX_ne_bot X H E hE χ hχ hH)

end HodgeLean.Adapters

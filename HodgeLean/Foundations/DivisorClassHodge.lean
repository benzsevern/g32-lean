import HodgeLean.Foundations.DivisorClassHodgeProofs
import HodgeLean.Foundations.ChowProjective

/-! # Divisor classes on abelian varieties are Hodge classes (DC1, FROZEN SPEC)

Track DC1, first stage. On a complex abelian variety `X` (smooth projective integral commutative
group scheme over `ℂ`) the span of the classes of prime divisors lies in `Hdg¹(X; ℚ)`:
`dc1_divisorClass_le_hodge`, the statement of `pwf_divisorClasses_le_hodge`. With
`chowG_lefschetzOneOne_abelian` (the other inclusion, on `main`) it gives
`Hdg¹(X; ℚ) = algebraicCycleClassSpan X 1`.

Route (Appell–Humbert). For a prime divisor `x`:
1. its pullback `dc1_coverDivisor X x` to `ℂ^g` has a reduced entire equation `f`
   (statements `dc1_componentSupport_interior` … `dc1_cover_equation`; the last step is the
   existing Cousin II theorem `spec_bh5_reduced_principalization`);
2. `f (z + l) = e_l(z) f(z)` for the constructed holomorphic factor `e = dc1_factor f Λ`, the line
   bundle `𝒪(D)` (`dc1_translate_associated`, `dc1_factor_spec`, `dc1_factor_cocycle`);
3. the upstream class `cycleComponentSheafClass X x` is `dc1_chernClass X f`, the class of the
   Chern form of `e`, by the existing period evaluation `spec_bh4_supported_square_evaluation`
   (`dc1_factorLog_spec`, `dc1_chernBihom_apply`, `dc1_periodPair_latticeClassHQ`,
   `dc1_boundary_chern`, `dc1_period_cycleClass`, `dc1_cycleClass_eq_chernClass`);
4. the Chern form of every holomorphic factor satisfies the Riemann relation
   `B(iv, iw) = B(v, w)` (`dc1_periodic_entire_const` … `dc1_chernForm_typeOneOne`, through
   the vanishing of `H¹(Λ, 𝒪(ℂ^g))` modulo constants and the normal form of the factor), so
   there is an Appell–Humbert datum with that form (`dc1_appellHumbert_datum`), and the existing
   `spec_latticeClassHQ_mem_hdg_of_riemann` puts the class in `Hdg¹`
   (`dc1_chernClass_mem_hdg`, `dc1_cycleComponentSheafClass_mem_hdg`).

Every statement is an implication from its displayed binders; there is no literature premise and
no new `@[hodge_hypothesis]`. The objects (cover divisor, factor, logarithm, Chern form, Chern
class) are definitions in `DivisorClassHodgeDefs.lean`; the bodies are the open `_aux` theorems
of `DivisorClassHodgeProofs.lean`.

Not claimed: that the factor of `f` is equivalent to the Appell–Humbert factor of the datum
(only the Hermitian form is identified, which is all the class sees); `CycleClassIsHodge` in
codimension above one; a statement on `ℂ^g / Λ` as a complex manifold isomorphic to `X(ℂ)`.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass HodgeLean.Adapters
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.Curves
open Filter Set Topology
open scoped ContDiff

namespace HodgeLean.Foundations

/-! ## The Riemann relation for holomorphic factors, on any full lattice of `ℂ^n` -/

section Lattice

variable {n : ℕ} (L : Submodule ℤ (Fin n → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **A periodic entire function is constant.** It is bounded, being determined by its values on
the compact closure of a fundamental domain, so Liouville's theorem applies.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`ℂ^n / L` is compact);
Mathlib `Differentiable.apply_eq_apply_of_bounded` (Liouville). -/
theorem dc1_periodic_entire_const (h : (Fin n → ℂ) → ℂ) (hh : Differentiable ℂ h)
    (hper : ∀ (l : L) z, h (z + l) = h z) (z w : Fin n → ℂ) : h z = h w :=
  dc1_periodic_entire_const_aux L h hh hper z w

/-- Constants are periodic and entire. -/
example (c : ℂ) (z w : Fin n → ℂ) : (fun _ ↦ c) z = (fun _ : Fin n → ℂ ↦ c) w :=
  dc1_periodic_entire_const L (fun _ ↦ c) (differentiable_const c) (fun _ _ ↦ rfl) z w

/-- **Smooth additive cocycles of the lattice are coboundaries.** With `ρ` a smooth function with
`∑_l ρ(z + l) = 1` (a locally finite sum), `φ(z) = -∑_l ρ(z + l) a_l(z)` has
`φ(z + l) - φ(z) = a_l(z)`.
Source: Mumford, *Abelian Varieties*, Ch. I, §2 (cohomology of `Λ` with coefficients in the
global functions of a sheaf that is acyclic on `V`; the partition-of-unity argument for smooth
functions); Birkenhake–Lange, 2nd ed., Appendix B. -/
theorem dc1_smooth_coboundary (a : L → (Fin n → ℂ) → ℂ) (ha : ∀ l, ContDiff ℝ ∞ (a l))
    (hcoc : ∀ (l m : L) z, a (l + m) z = a l (z + m) + a m z) :
    ∃ φ : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ φ ∧ ∀ (l : L) z, φ (z + l) - φ z = a l z :=
  dc1_smooth_coboundary_aux L a ha hcoc

/-- The zero cocycle. -/
example : ∃ φ : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ φ ∧ ∀ (l : L) z, φ (z + l) - φ z = 0 :=
  dc1_smooth_coboundary L (fun _ _ ↦ 0) (fun _ ↦ contDiff_const) (fun _ _ _ ↦ by simp)

/-- **Degenerate case ruled out: the cocycle identity is needed.** The constant family `a_l = 1`
violates it at `l = m = 0`, and no `φ` has `φ(z + l) - φ(z) = 1` for all `l` (take `l = 0`). -/
example : ¬ ∃ φ : (Fin n → ℂ) → ℂ, ∀ (l : L) z, φ (z + l) - φ z = 1 := by
  rintro ⟨φ, hφ⟩
  have h := hφ 0 0
  simp at h

/-- **Dolbeault cohomology of the torus in degree `(0, 1)`.** A smooth periodic `(0, 1)`-form `w`
on `ℂ^n` with `∂̄_k w_j = ∂̄_j w_k` is a constant form plus `∂̄ψ` for a smooth periodic `ψ`:
expand in Fourier series on `ℂ^n / L`; the constant term is `c`, and every other coefficient is
divided by the nonvanishing symbol of `∂̄`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.4 (the cohomology of the
structure sheaf of a complex torus, by Dolbeault); Mumford, *Abelian Varieties*, Ch. I, §1
(`H^q(X, 𝒪_X)` by Fourier series); `dbar_coord`. -/
theorem dc1_torus_dbar (w : Fin n → (Fin n → ℂ) → ℂ) (hw : ∀ j, ContDiff ℝ ∞ (w j))
    (hper : ∀ j (l : L) z, w j (z + l) = w j z)
    (hclosed : ∀ j k z, dbar_coord n k (w j) z = dbar_coord n j (w k) z) :
    ∃ (c : Fin n → ℂ) (ψ : (Fin n → ℂ) → ℂ), ContDiff ℝ ∞ ψ ∧
      (∀ (l : L) z, ψ (z + l) = ψ z) ∧ ∀ j z, w j z = c j + dbar_coord n j ψ z :=
  dc1_torus_dbar_aux L w hw hper hclosed

/-- The zero form. -/
example : ∃ (c : Fin n → ℂ) (ψ : (Fin n → ℂ) → ℂ), ContDiff ℝ ∞ ψ ∧
    (∀ (l : L) z, ψ (z + l) = ψ z) ∧ ∀ j z, (0 : ℂ) = c j + dbar_coord n j ψ z :=
  dc1_torus_dbar L (fun _ _ ↦ 0) (fun _ ↦ contDiff_const) (fun _ _ _ ↦ rfl)
    (fun _ _ _ ↦ by simp [dbar_coord])

/-- **`H¹(L, 𝒪(ℂ^n))` is spanned by constant cocycles.** An additive cocycle of entire functions
is a coboundary `h(z + l) - h(z)` of an entire `h` plus a homomorphism `A : L → ℂ`. Take a smooth
`φ` with `δφ = a` (`dc1_smooth_coboundary`); `∂̄φ` is periodic with symmetric derivatives, so
`∂̄φ = c + ∂̄ψ` (`dc1_torus_dbar`); then `h = φ - ψ - ∑ c_j z̄_j` is entire (`dbar_holomorphic`)
and `A(l) = ∑ c_j l̄_j`.
Source: Mumford, *Abelian Varieties*, Ch. I, §2 (`H^1(Λ, H^0(𝒪_V)) ≅ H^1(X, 𝒪_X) ≅ V̄^*`);
Birkenhake–Lange, 2nd ed., §1.4 and Appendix B. -/
theorem dc1_additiveCocycle (a : L → (Fin n → ℂ) → ℂ) (ha : ∀ l, Differentiable ℂ (a l))
    (hcoc : ∀ (l m : L) z, a (l + m) z = a l (z + m) + a m z) :
    ∃ (h : (Fin n → ℂ) → ℂ) (A : L →+ ℂ), Differentiable ℂ h ∧
      ∀ (l : L) z, a l z = h (z + l) - h z + A l :=
  dc1_additiveCocycle_aux L a ha hcoc

/-- A constant cocycle `a_l = A l` for an additive `A`. -/
example (A : L →+ ℂ) : ∃ (h : (Fin n → ℂ) → ℂ) (A' : L →+ ℂ), Differentiable ℂ h ∧
    ∀ (l : L) z, A l = h (z + l) - h z + A' l :=
  dc1_additiveCocycle L (fun l _ ↦ A l) (fun _ ↦ differentiable_const _)
    (fun l m _ ↦ by simp)

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- **Holomorphic Poincaré lemma on `ℂ^n`.** Entire functions `u_j` with
`∂_k u_j = ∂_j u_k` are the partial derivatives of one entire function, namely
`h(z) = ∫₀¹ ∑_j u_j(t z) z_j dt`.
Source: Huybrechts, *Complex Geometry*, §1.3 (Poincaré lemmas on polydiscs and on `ℂ^n`). -/
theorem dc1_holomorphic_poincare (u : Fin n → (Fin n → ℂ) → ℂ)
    (hu : ∀ j, Differentiable ℂ (u j))
    (hclosed : ∀ j k z, fderiv ℂ (u j) z (Pi.single k 1) = fderiv ℂ (u k) z (Pi.single j 1)) :
    ∃ h : (Fin n → ℂ) → ℂ, Differentiable ℂ h ∧
      ∀ j z, fderiv ℂ h z (Pi.single j 1) = u j z :=
  dc1_holomorphic_poincare_aux u hu hclosed

/-- The zero family. -/
example : ∃ h : (Fin n → ℂ) → ℂ, Differentiable ℂ h ∧
    ∀ j z, fderiv ℂ h z (Pi.single j 1) = (0 : ℂ) :=
  dc1_holomorphic_poincare (fun _ _ ↦ 0) (fun _ ↦ differentiable_const _) (fun _ _ _ ↦ by simp)

/-- **Normal form of a holomorphic factor.** For a holomorphic logarithm `F` of a factor `a`,
after a coboundary `h(z + l) - h(z)` with `h` entire, `F_l` is affine in `z` with linear part
additive in `l`. The derivatives `∂_k F_l` are additive cocycles (the integer defect of `F` is
constant); `dc1_additiveCocycle` writes them as `δh_k + A_k`; `∂_j h_k - ∂_k h_j` is periodic and
entire, hence constant (`dc1_periodic_entire_const`), and is removed by a linear change of the
`h_k`; `dc1_holomorphic_poincare` integrates the `h_k`.
Source: Mumford, *Abelian Varieties*, Ch. I, §2 (proof of the Appell–Humbert theorem: every
factor is equivalent to one of the form `e^{2πi(L_l(z) + b_l)}`); Birkenhake–Lange, 2nd ed.,
§2.2 (Appell–Humbert). -/
theorem dc1_linearization (a F : L → (Fin n → ℂ) → ℂ)
    (hcoc : ∀ (l m : L) v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Differentiable ℂ (F l)) :
    ∃ (h : (Fin n → ℂ) → ℂ) (lin : L →+ ((Fin n → ℂ) →ₗ[ℂ] ℂ)) (b : L → ℂ),
      Differentiable ℂ h ∧ ∀ (l : L) z, F l z + h (z + l) - h z = lin l z + b l :=
  dc1_linearization_aux L a F hcoc hlog hF

/-- The trivial factor `1` with logarithm `0`. -/
example : ∃ (h : (Fin n → ℂ) → ℂ) (lin : L →+ ((Fin n → ℂ) →ₗ[ℂ] ℂ)) (b : L → ℂ),
    Differentiable ℂ h ∧ ∀ (l : L) z, (0 : ℂ) + h (z + l) - h z = lin l z + b l :=
  dc1_linearization L (fun _ _ ↦ 1) (fun _ _ ↦ 0) (fun _ _ _ ↦ by simp) (fun _ _ ↦ by simp)
    (fun _ ↦ differentiable_const _)

/-- **The Riemann relation for an affine factor.** If the real form `B` is
`lin_m(l) - lin_l(m)` on `L`, with `lin` additive and each `lin_l` complex-linear, then
`B(iv, iw) = B(v, w)`. Extend `lin` real-linearly to `V`; the difference
`B(v, w) - B(iv, iw)` is `2 (P_w(v) - P_v(w))` for the complex-linear part `P` of the extension,
a complex-bilinear form with real values, hence `0`.
Source: Mumford, *Abelian Varieties*, Ch. I, §2 (the form `E` of a normalized factor is the
imaginary part of a Hermitian form); Birkenhake–Lange, 2nd ed., Lemma 1.3.1 and §2.1. -/
theorem dc1_typeOneOne_of_affine (lin : L →+ ((Fin n → ℂ) →ₗ[ℂ] ℂ))
    (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ)
    (hB : ∀ l m : L, (B l m : ℂ) = lin m l - lin l m) :
    IsTypeOneOne (fun v w ↦ B v w) :=
  dc1_typeOneOne_of_affine_aux L lin B hB

/-- `lin = 0` and `B = 0`. -/
example : IsTypeOneOne (fun v w : Fin n → ℂ ↦ (0 : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ) v w) :=
  dc1_typeOneOne_of_affine L 0 0 (fun _ _ ↦ by simp)

/-- **The Chern form of a holomorphic factor satisfies the Riemann relation.** For a factor `a`
of entire nowhere-vanishing functions with a continuous logarithm `F`, the real extension `B` of
`chernForm F` has `B(iv, iw) = B(v, w)`. `F` is entire; `dc1_linearization` and the telescoping
of `logForm` under coboundaries reduce to `dc1_typeOneOne_of_affine`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2 and §2.2
(the first Chern class of a line bundle on a complex torus is `Im H` for a Hermitian `H`);
Mumford, *Abelian Varieties*, Ch. I, §2. -/
theorem dc1_chernForm_typeOneOne (a F : L → (Fin n → ℂ) → ℂ)
    (ha : ∀ l, Differentiable ℂ (a l))
    (hcoc : ∀ (l m : L) v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Continuous (F l))
    (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ) (hB : ∀ l m : L, B l m = chernForm F l m) :
    IsTypeOneOne (fun v w ↦ B v w) :=
  dc1_chernForm_typeOneOne_aux L a F ha hcoc hlog hF B hB

/-- The trivial factor: logarithm `0`, form `0`. -/
example : IsTypeOneOne (fun v w : Fin n → ℂ ↦ (0 : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ) v w) :=
  dc1_chernForm_typeOneOne L (fun _ _ ↦ 1) (fun _ _ ↦ 0) (fun _ ↦ differentiable_const _)
    (fun _ _ _ ↦ by simp) (fun _ _ ↦ by simp) (fun _ ↦ continuous_const) 0
    (fun _ _ ↦ by simp [chernForm, logForm])

end Lattice

/-! ## Reduced equations and their factors, on `ℂ^n` -/

section Factor

variable {n : ℕ} (L : Submodule ℤ (Fin n → ℂ))

omit L in
/-- **Squarefree part of a germ.** A holomorphic germ that is not zero has a squarefree germ with
the same zero germ: the product of its distinct prime factors in the factorial ring of germs.
Source: Gunning–Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B
(Weierstrass preparation; the ring of germs is factorial) and Ch. III, §A. -/
theorem dc1_squarefree_reduction (p : Fin n → ℂ) (g : (Fin n → ℂ) → ℂ)
    (hg : AnalyticAt ℂ g p) (hne : ¬ ∀ᶠ z in 𝓝 p, g z = 0) :
    ∃ (g' : (Fin n → ℂ) → ℂ) (hg' : AnalyticAt ℂ g' p),
      Squarefree (⟨Filter.Germ.ofFun g', g', hg', rfl⟩ : AnalyticGermAt n p) ∧
        ∀ᶠ z in 𝓝 p, (g' z = 0 ↔ g z = 0) :=
  dc1_squarefree_reduction_aux p g hg hne

omit L in
/-- A unit germ: its squarefree part has no zeros near `p`. -/
example (p : Fin n → ℂ) :
    ∃ (g' : (Fin n → ℂ) → ℂ) (hg' : AnalyticAt ℂ g' p),
      Squarefree (⟨Filter.Germ.ofFun g', g', hg', rfl⟩ : AnalyticGermAt n p) ∧
        ∀ᶠ z in 𝓝 p, (g' z = 0 ↔ (1 : ℂ) = 0) :=
  dc1_squarefree_reduction p (fun _ ↦ 1) analyticAt_const
    (fun h ↦ one_ne_zero h.self_of_nhds)

/-- **Translates of a reduced equation of an invariant divisor are associated.** `f` and
`z ↦ f (z + l)` are reduced equations with the same zero set, so they differ by a unit germ at
every point (`spec_bh5_reduced_associated`).
Source: Gunning–Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B and
Ch. III, §A (local Nullstellensatz for principal ideals); `spec_bh5_reduced_associated`. -/
theorem dc1_translate_associated (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p))
    (hper : ∀ (l : L) p, f (p + l) = 0 ↔ f p = 0) (l : L) (p : Fin n → ℂ) :
    AreAssociatedAt f (fun z ↦ f (z + l)) p :=
  dc1_translate_associated_aux L f hf hred hper l p

example (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p))
    (hper : ∀ (l : L) p, f (p + l) = 0 ↔ f p = 0) (p : Fin n → ℂ) :
    AreAssociatedAt f (fun z ↦ f (z + (0 : L))) p :=
  dc1_translate_associated L f hf hred hper 0 p

/-- **The factor of a reduced equation is a holomorphic factor of automorphy.** For a reduced
entire `f` with `L`-invariant zero set, `dc1_factor f L l` is entire, nowhere zero and satisfies
`f (z + l) = e_l(z) f(z)`: near each point it is the unit of `dc1_translate_associated`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 and §3.1 (the factor of a
theta function); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem dc1_factor_spec (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p))
    (hper : ∀ (l : L) p, f (p + l) = 0 ↔ f p = 0) (l : L) :
    Differentiable ℂ (dc1_factor f L l) ∧ (∀ z, dc1_factor f L l z ≠ 0) ∧
      ∀ z, f (z + l) = dc1_factor f L l z * f z :=
  dc1_factor_spec_aux L f hf hred hper l

example (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p))
    (hper : ∀ (l : L) p, f (p + l) = 0 ↔ f p = 0) (l : L) (z : Fin n → ℂ) :
    f (z + l) = dc1_factor f L l z * f z :=
  (dc1_factor_spec L f hf hred hper l).2.2 z

/-- **The factor is a cocycle.** `e_{l+m}(z) = e_l(z + m) e_m(z)`: both sides times `f(z)` are
`f(z + l + m)`, and the zeros of `f` have empty interior.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 (cocycle relation of a factor
of automorphy) and Appendix B. -/
theorem dc1_factor_cocycle (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p))
    (hper : ∀ (l : L) p, f (p + l) = 0 ↔ f p = 0) (l m : L) (z : Fin n → ℂ) :
    dc1_factor f L (l + m) z = dc1_factor f L l (z + m) * dc1_factor f L m z :=
  dc1_factor_cocycle_aux L f hf hred hper l m z

example (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p))
    (hper : ∀ (l : L) p, f (p + l) = 0 ↔ f p = 0) (l : L) (z : Fin n → ℂ) :
    dc1_factor f L (l + 0) z = dc1_factor f L l (z + (0 : L)) * dc1_factor f L 0 z :=
  dc1_factor_cocycle L f hf hred hper l 0 z

/-- **The constructed logarithm.** For entire nowhere-vanishing `a_l`, `dc1_factorLog a l` is
entire and `a_l = exp(2πi · dc1_factorLog a l)`: the integral of the logarithmic derivative along
`t ↦ t z` is a primitive of `da/a` on the star-shaped `ℂ^n`.
Source: Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §3.4; Birkenhake–Lange, 2nd ed., §2.1. -/
theorem dc1_factorLog_spec (a : L → (Fin n → ℂ) → ℂ) (ha : ∀ l, Differentiable ℂ (a l))
    (ha₀ : ∀ l z, a l z ≠ 0) (l : L) :
    Differentiable ℂ (dc1_factorLog a l) ∧
      ∀ z, a l z = Complex.exp (2 * Real.pi * Complex.I * dc1_factorLog a l z) :=
  dc1_factorLog_spec_aux L a ha ha₀ l

example (l : L) (z : Fin n → ℂ) :
    (fun (_ : L) (_ : Fin n → ℂ) ↦ (2 : ℂ)) l z = Complex.exp (2 * Real.pi * Complex.I *
      dc1_factorLog (fun (_ : L) (_ : Fin n → ℂ) ↦ (2 : ℂ)) l z) :=
  (dc1_factorLog_spec L _ (fun _ ↦ differentiable_const _) (fun _ _ ↦ two_ne_zero) l).2 z

/-- **The constructed form is the Chern form.** Under the cocycle and logarithm hypotheses
`chernForm F` is biadditive (`spec_chernForm_biadditive`), so it agrees everywhere with the form
built from its basis values: `dc1_chernBihom F = -chernForm F`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2;
`spec_chernForm_biadditive`, `Basis.constr`. -/
theorem dc1_chernBihom_apply [Module.Free ℤ L] [Module.Finite ℤ L]
    (a F : L → (Fin n → ℂ) → ℂ)
    (hcoc : ∀ (l m : L) v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Continuous (F l)) (l m : L) :
    dc1_chernBihom F l m = -chernForm F l m :=
  dc1_chernBihom_apply_aux L a F hcoc hlog hF l m

example [Module.Free ℤ L] [Module.Finite ℤ L] (l m : L) :
    dc1_chernBihom (fun (_ : L) (_ : Fin n → ℂ) ↦ (0 : ℂ)) l m =
      -chernForm (fun (_ : L) (_ : Fin n → ℂ) ↦ (0 : ℂ)) l m :=
  dc1_chernBihom_apply L (fun _ _ ↦ 1) _ (fun _ _ _ ↦ by simp) (fun _ _ ↦ by simp)
    (fun _ ↦ continuous_const) l m

end Factor

/-! ## The divisor on `X` -/

section Abelian

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

/-- **A prime divisor has no interior in `X(ℂ)`.** For `x` of coheight one, `closure {x}` is a
proper Zariski-closed subset of the integral `X`; its complement is a nonempty Zariski-open set,
whose complex points are dense in the classical topology.
Source: Mumford, *The Red Book of Varieties and Schemes*, Ch. I, §10, Theorem 1 (a nonempty
Zariski-open subset is dense in the complex topology). -/
theorem dc1_componentSupport_interior (x : X.left) (hx : Order.coheight x = 1) :
    interior (bh4_componentSupport X x) = ∅ :=
  dc1_componentSupport_interior_aux X x hx

example (x : X.left) (hx : Order.coheight x = 1) (U : Set (ComplexPoint X)) (hU : IsOpen U)
    (hsub : U ⊆ bh4_componentSupport X x) : U = ∅ := by
  have h := interior_maximal hsub hU
  rw [dc1_componentSupport_interior X x hx] at h
  exact Set.subset_empty_iff.mp h

/-- **A prime divisor of the smooth `X` is locally principal.** Every complex point has a Zariski
neighbourhood `V` and a regular function `s` on `V` whose zeros among the complex points of `V`
are exactly the points of `closure {x}`: the local rings of `X` are regular, hence factorial,
so the height-one prime of `closure {x}` is principal near each point.
Source: Hartshorne, *Algebraic Geometry*, Ch. II, Proposition 6.11 and Remark 6.11.1A (a
nonsingular variety is locally factorial; prime divisors are locally principal); Matsumura,
*Commutative Ring Theory*, Theorem 20.3 (regular local rings are factorial). -/
theorem dc1_locallyPrincipal (x : X.left) (hx : Order.coheight x = 1) (z : ComplexPoint X) :
    ∃ (V : X.left.Opens) (s : Γ(X.left, V)), z ∈ Point.overOpen V ∧
      ∀ w ∈ Point.overOpen V, (w ∈ bh4_componentSupport X x ↔ Point.evaluate V s w = 0) :=
  dc1_locallyPrincipal_aux X x hx z

example (x : X.left) (hx : Order.coheight x = 1) (z : ComplexPoint X) :
    ∃ (V : X.left.Opens) (s : Γ(X.left, V)), z ∈ Point.overOpen V ∧
      (z ∈ bh4_componentSupport X x ↔ Point.evaluate V s z = 0) := by
  obtain ⟨V, s, hz, h⟩ := dc1_locallyPrincipal X x hx z
  exact ⟨V, s, hz, h z hz⟩

/-- **Local equations on the cover.** Near every point of `ℂ^g` the divisor
`dc1_coverDivisor X x` is the zero set of one holomorphic function that does not vanish
identically: `s ∘ abelianExp` for the `s` of `dc1_locallyPrincipal` (holomorphic by
`bh8_analyticAt_evaluate_abelianExp`), not locally zero by `dc1_componentSupport_interior` and
openness of `abelianExp`.
Source: Serre, *Géométrie algébrique et géométrie analytique*, §2 (regular functions are
holomorphic); `bh8_analyticAt_evaluate_abelianExp`, `dc1_locallyPrincipal`. -/
theorem dc1_local_equation (x : X.left) (hx : Order.coheight x = 1)
    (p : Fin (dim X.left) → ℂ) :
    ∃ g : (Fin (dim X.left) → ℂ) → ℂ, AnalyticAt ℂ g p ∧ (¬ ∀ᶠ z in 𝓝 p, g z = 0) ∧
      ∀ᶠ z in 𝓝 p, (g z = 0 ↔ z ∈ dc1_coverDivisor X x) :=
  dc1_local_equation_aux X x hx p

example (x : X.left) (hx : Order.coheight x = 1) (p : Fin (dim X.left) → ℂ) :
    ∃ g : (Fin (dim X.left) → ℂ) → ℂ, AnalyticAt ℂ g p ∧ ¬ ∀ᶠ z in 𝓝 p, g z = 0 := by
  obtain ⟨g, hg, hne, -⟩ := dc1_local_equation X x hx p
  exact ⟨g, hg, hne⟩

/-- **A reduced entire equation of the divisor on the cover.** Squarefree local equations from
`dc1_local_equation` and `dc1_squarefree_reduction`, glued by Cousin II on `ℂ^g`
(`spec_bh5_reduced_principalization`).
Source: Gunning–Rossi, *Analytic Functions of Several Complex Variables*, Ch. VIII (Cousin II on
`ℂ^n`); `spec_bh5_reduced_principalization`. -/
theorem dc1_cover_equation (x : X.left) (hx : Order.coheight x = 1) :
    ∃ (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ),
      (∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
        AnalyticGermAt (dim X.left) p)) ∧ ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x :=
  dc1_cover_equation_aux X x hx

example (x : X.left) (hx : Order.coheight x = 1) :
    ∃ f : (Fin (dim X.left) → ℂ) → ℂ, ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x := by
  obtain ⟨f, -, -, h⟩ := dc1_cover_equation X x hx
  exact ⟨f, h⟩

/-- **Period-pair evaluation of a lattice class.** For an alternating integral form `E`,
`bh4_periodPair X l m (latticeClassHQ X E) = E l m`; this is `spec_bh4_periodPair_lattice`
without the Hermitian form (the proof there uses only that `E` is alternating).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.3 and Lemma 1.3.1;
`latticeClassHQ`, `bh4_periodPair`. -/
theorem dc1_periodPair_latticeClassHQ
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l : abelianPeriodLattice X, E l l = 0) (l m : abelianPeriodLattice X) :
    bh4_periodPair X l m (latticeClassHQ X E) = (E l m : ℚ) :=
  dc1_periodPair_latticeClassHQ_aux X E hE l m

example (l m : abelianPeriodLattice X) :
    bh4_periodPair X l m (latticeClassHQ X 0) = ((0 : abelianPeriodLattice X →+
      abelianPeriodLattice X →+ ℤ) l m : ℚ) :=
  dc1_periodPair_latticeClassHQ X 0 (fun _ ↦ rfl) l m

/-- **Boundary increment of a section of any factor.** If `θ (z + l) = a_l(z) θ(z)` for a cocycle
`a` with continuous logarithm `F`, the increments of continuous logarithms of `θ` along the four
edges of the period square sum to `-chernForm F l m`. Opposite edges differ by a translate, so
their increments differ by values of `F`; this is `spec_bh4_boundary_chern` for an arbitrary
factor in place of an Appell–Humbert one.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 and Theorem 2.1.2;
`spec_bh4_opposite_edge_increments`, `spec_logForm_eq_chernForm`. -/
theorem dc1_boundary_chern (a F : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hcoc : ∀ (l m : abelianPeriodLattice X) v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Continuous (F l)) (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : ∀ (l : abelianPeriodLattice X) z, θ (z + l) = a l z * θ z)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    bh4_boundaryIncrement g = -(chernForm F l m : ℂ) :=
  dc1_boundary_chern_aux X a F hcoc hlog hF θ hθ l m z g hg hexp

/-- The constant section `1` of the trivial factor, with the zero lifts. -/
example (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ) :
    bh4_boundaryIncrement (fun _ _ ↦ 0) =
      -(chernForm (fun (_ : abelianPeriodLattice X) (_ : Fin (dim X.left) → ℂ) ↦ (0 : ℂ)) l m :
        ℂ) :=
  dc1_boundary_chern X (fun _ _ ↦ 1) (fun _ _ ↦ 0) (fun _ _ _ ↦ by simp) (fun _ _ ↦ by simp)
    (fun _ ↦ continuous_const) (fun _ ↦ 1) (fun _ _ ↦ by simp) l m z (fun _ _ ↦ 0)
    (fun _ ↦ continuousOn_const) (fun _ _ _ ↦ by simp)

/-- **Periods of the class of a prime divisor.** With a reduced entire equation `f` of the divisor
on the cover and a continuous logarithm `F` of its factor, the period pair of
`cycleComponentSheafClass X x` at `(l, m)` is `-chernForm F l m`. Choose a square avoiding the
zeros of `f`, evaluate the supported class by the boundary winding of `f`
(`spec_bh4_supported_square_evaluation`, `spec_bh4_winding_orientation`) and apply
`dc1_boundary_chern` to the factor of `f`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §1 (the class of a divisor
and the Chern class of its line bundle); Birkenhake–Lange, 2nd ed., Theorem 2.1.2;
`spec_bh4_supported_square_evaluation`. -/
theorem dc1_period_cycleClass (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x)
    (F : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hlog : ∀ l v, dc1_factor f (abelianPeriodLattice X) l v =
      Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Continuous (F l)) (l m : abelianPeriodLattice X) :
    bh4_periodPair X l m (cycleComponentSheafClass X x hx) = -(chernForm F l m : ℚ) :=
  dc1_period_cycleClass_aux X x hx f hf hred hzero F hlog hF l m

example (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x)
    (F : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hlog : ∀ l v, dc1_factor f (abelianPeriodLattice X) l v =
      Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Continuous (F l)) (l : abelianPeriodLattice X) :
    bh4_periodPair X l l (cycleComponentSheafClass X x hx) = -(chernForm F l l : ℚ) :=
  dc1_period_cycleClass X x hx f hf hred hzero F hlog hF l l

/-- **The class of a prime divisor is the first Chern class of its line bundle.**
`cycleComponentSheafClass X x = dc1_chernClass X f` for every reduced entire equation `f` of the
divisor on the cover: the two classes have the same period pairs (`dc1_period_cycleClass`,
`dc1_chernBihom_apply`, `dc1_periodPair_latticeClassHQ`), which detect a class
(`spec_bh4_periodPair_ext`).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §1; Voisin, *Hodge Theory
and Complex Algebraic Geometry I*, Proposition 11.21 and Theorem 11.30 (`[D] = c₁(𝒪(D))`);
Birkenhake–Lange, 2nd ed., Theorem 2.1.2. -/
theorem dc1_cycleClass_eq_chernClass (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x) :
    cycleComponentSheafClass X x hx = dc1_chernClass X f :=
  dc1_cycleClass_eq_chernClass_aux X x hx f hf hred hzero

/-- The class does not depend on the chosen equation. -/
example (x : X.left) (hx : Order.coheight x = 1)
    (f f' : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hf' : AnalyticOnNhd ℂ f' univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hred' : ∀ p, Squarefree (⟨Filter.Germ.ofFun f', f', hf' p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x)
    (hzero' : ∀ p, f' p = 0 ↔ p ∈ dc1_coverDivisor X x) :
    dc1_chernClass X f = dc1_chernClass X f' :=
  (dc1_cycleClass_eq_chernClass X x hx f hf hred hzero).symm.trans
    (dc1_cycleClass_eq_chernClass X x hx f' hf' hred' hzero')

/-- **An Appell–Humbert datum with the Chern form of `𝒪(D)`.** There is `A : bh4_AHData X`
(a Hermitian `H` with `Im H = A.E` on `Λ` and a semicharacter) whose integral form is the Chern
form of the factor of `f`, and the class of the divisor is `latticeClassHQ X A.E`. The Riemann
relation is `dc1_chernForm_typeOneOne`; `H` and `χ` come from
`spec_exists_datumOfX_of_riemann`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 (Appell–Humbert),
Lemma 1.3.1; `spec_exists_datumOfX_of_riemann`. -/
theorem dc1_appellHumbert_datum (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x) :
    ∃ A : bh4_AHData X,
      A.E = dc1_chernBihom (dc1_factorLog (dc1_factor f (abelianPeriodLattice X))) ∧
        cycleComponentSheafClass X x hx = latticeClassHQ X A.E :=
  dc1_appellHumbert_datum_aux X x hx f hf hred hzero

example (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x) :
    ∃ H : HermitianForm (V := Fin (dim X.left) → ℂ),
      ∀ l m : abelianPeriodLattice X,
        ((dc1_chernBihom (dc1_factorLog (dc1_factor f (abelianPeriodLattice X))) l m : ℤ) :
          ℝ) = H.imaginary l m := by
  obtain ⟨A, hA, -⟩ := dc1_appellHumbert_datum X x hx f hf hred hzero
  exact ⟨A.H, fun l m ↦ hA ▸ A.integral l m⟩

/-- **The Chern class of the line bundle of a divisor is a Hodge class.** The real extension of
the Chern form satisfies the Riemann relation (`dc1_chernForm_typeOneOne`, with
`dc1_factor_spec`, `dc1_factor_cocycle`, `dc1_factorLog_spec`, `dc1_chernBihom_apply`), so
`spec_latticeClassHQ_mem_hdg_of_riemann` applies, with `finiteBetti_abelian` and
`spec_bettiDeRhamIso_abelian`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §1 (`c₁` of a holomorphic line
bundle is of type `(1,1)`); Birkenhake–Lange, 2nd ed., §2.2;
`spec_latticeClassHQ_mem_hdg_of_riemann`. -/
theorem dc1_chernClass_mem_hdg (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x) :
    (dc1_chernClass X f : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ) :=
  dc1_chernClass_mem_hdg_aux X x hx f hf hred hzero

example (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x) :
    (dc1_chernClass X f : H^(2 * 1)(X; ℚ)) ∈ algebraicCycleClassSpan X 1 ⊓ Hdg^1(X; ℚ) := by
  refine ⟨?_, dc1_chernClass_mem_hdg X x hx f hf hred hzero⟩
  rw [← dc1_cycleClass_eq_chernClass X x hx f hf hred hzero]
  exact spec_bh4_cycleComponentSheafClass_mem_span X x hx

/-- **The class of a prime divisor is a Hodge class.** `dc1_cover_equation`,
`dc1_cycleClass_eq_chernClass` and `dc1_chernClass_mem_hdg`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §11.1.2–11.1.3 and
Proposition 11.21 with Theorem 11.30; Birkenhake–Lange, 2nd ed., §2.2. -/
theorem dc1_cycleComponentSheafClass_mem_hdg (x : X.left) (hx : Order.coheight x = 1) :
    cycleComponentSheafClass X x hx ∈ Hdg^1(X; ℚ) :=
  dc1_cycleComponentSheafClass_mem_hdg_aux X x hx

example (x : X.left) (hx : Order.coheight x = 1) (q : ℚ) :
    q • cycleComponentSheafClass X x hx ∈ Hdg^1(X; ℚ) :=
  Submodule.smul_mem _ q (dc1_cycleComponentSheafClass_mem_hdg X x hx)

end Abelian

/-- **Divisor classes on a complex abelian variety are Hodge classes.** The span of the classes
of prime divisors lies in `Hdg¹(X; ℚ)`: each generator does, by
`dc1_cycleComponentSheafClass_mem_hdg`. The statement is that of
`pwf_divisorClasses_le_hodge` (`cloud/spec-pwfin`), binder for binder.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§11.1.2–11.1.3 and Proposition 11.21 with Theorem 11.30; Griffiths–Harris, *Principles of
Algebraic Geometry*, Ch. 1 §1; Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.2. -/
theorem dc1_divisorClass_le_hodge (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    algebraicCycleClassSpan X 1 ≤ Hdg^1(X; ℚ) :=
  dc1_divisorClass_le_hodge_aux X

/-- With the inclusion `chowG_lefschetzOneOne_abelian` on `main`, the divisor classes span exactly
the rational `(1,1)` classes. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : algebraicCycleClassSpan X 1 = Hdg^1(X; ℚ) :=
  le_antisymm (dc1_divisorClass_le_hodge X) (chowG_lefschetzOneOne_abelian X)

/-- On every power of the cubic curve `E`, with no binder. -/
example (r : ℕ) : algebraicCycleClassSpan (g3_power E r) 1 ≤ Hdg^1(g3_power E r; ℚ) :=
  dc1_divisorClass_le_hodge (g3_power E r)

/-- On the cubic curve itself the statement agrees with the curve case already on `main`. -/
example : algebraicCycleClassSpan E 1 ≤ Hdg^1(E; ℚ) :=
  dc1_divisorClass_le_hodge E

end HodgeLean.Foundations

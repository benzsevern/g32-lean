import HodgeLean.Foundations.AnalyticDivisorAlgebraicProofs
import HodgeLean.Foundations.AppellHumbertSections

/-! # Analytic divisors of theta functions: frozen specification (Chow/GAGA, first stage)

Toward `LefschetzOneOneHyp` for abelian `X` through the Appell--Humbert line bundle `L(H, χ)`:
(a) the line bundle with theta-function sections, (b) the analytic divisor of a section,
(c) Chow/GAGA (an analytic hypersurface of `X(ℂ)` for projective `X` is algebraic), (d) the cycle
class of that divisor is `c₁`. This stage freezes the first honest pieces of (b), on the analytic
side, and the falsification check for (c).

Claimed:
* on a complex normed space `E`: the zero set of a function analytic on all of `E` is closed
  analytic (`IsClosedAnalytic E`); on a connected open `U`, the zero set of a function analytic on
  `U` and not identically zero on `U` has empty interior; the zero set of a nonzero entire
  (complex-differentiable) function has empty interior;
* for a theta function `θ ∈ sections D` of an Appell--Humbert datum `D` on `V`, `dim V < ∞`: its
  zero set is invariant under the lattice; the divisor `thetaDivisor D θ ⊆ V ⧸ Λ` is closed, its
  preimage in `V` is the zero set of `θ`, and for `θ ≠ 0` it has empty interior;
* in genus one (`V = ℂ`): the zero set of a theta function is closed analytic in `ℂ`;
* falsification for (c) without compactness: `ℤ ⊆ ℂ` is closed analytic but is not the common zero
  set of any family of polynomials (not Zariski closed in `𝔸¹(ℂ)`).

Not claimed: closed analyticity of the zero set of a theta function for `dim V ≥ 2` (Mathlib has no
several-variable "holomorphic implies analytic"), any analytic structure on `V ⧸ Λ` or on `X(ℂ)`,
that `thetaDivisor D θ` is the divisor of a section of a line bundle on `X(ℂ)`, the transport of
the divisor to `X(ℂ)` along the uniformization, Chow's theorem or GAGA, algebraicity of any
divisor, membership in `algebraicCycleClassSpan X 1`, or any cycle class. The route and stage
estimates are in `docs/specs/AnalyticDivisorAlgebraic.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic

open AppellHumbert AutomorphyLineBundle

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The zero set of a function analytic on all of a complex normed space `E` is closed analytic
in `E` (charted on itself): it is closed, and near each of its points it is cut out by the single
equation `f = 0`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §E,
Definition 1 (analytic subvarieties); Christian Schnell, *Complex Manifolds* (lecture notes),
Definition 3.2. -/
theorem spec_isClosedAnalytic_zeroSet (f : E → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    IsClosedAnalytic E {x | f x = 0} :=
  spec_isClosedAnalytic_zeroSet_aux f hf

example : IsClosedAnalytic ℂ {z : ℂ | z ^ 2 - 1 = 0} :=
  spec_isClosedAnalytic_zeroSet _ fun _ _ => ((analyticAt_id.pow 2).sub analyticAt_const)

/-- **Proper analytic subsets.**  On a connected open set `U` of a complex normed space, the zero
set of a function analytic on `U` and nonzero at some point of `U` has empty interior; in
particular it is a proper subset of `U`.

Source: Christian Schnell, *Complex Manifolds* (lecture notes), Theorem 1.8 (identity theorem);
Mathlib's `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`. -/
theorem spec_interior_inter_zeroSet_eq_empty {U : Set E} (hU : IsOpen U)
    (hUc : IsPreconnected U) {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hfx₀ : f x₀ ≠ 0) : interior (U ∩ {x | f x = 0}) = ∅ :=
  spec_interior_inter_zeroSet_eq_empty_aux hU hUc hf hx₀ hfx₀

example {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U) {f : E → ℂ}
    (hf : AnalyticOnNhd ℂ f U) {x₀ : E} (hx₀ : x₀ ∈ U) (hfx₀ : f x₀ ≠ 0) :
    U ∩ {x | f x = 0} ≠ U := fun h => by
  have := spec_interior_inter_zeroSet_eq_empty hU hUc hf hx₀ hfx₀
  rw [h, hU.interior_eq] at this
  exact this.subset hx₀

/-- The zero set of a nonzero entire function on a complex normed space has empty interior. Only
complex differentiability is assumed: restricted to each complex line through an interior point,
the function is an entire function of one variable vanishing on an open set.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §A, Theorem 6
(identity theorem), via Mathlib's one-variable `Differentiable.analyticAt`. -/
theorem spec_interior_zeroSet_eq_empty_of_differentiable {f : E → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) : interior {x | f x = 0} = ∅ :=
  spec_interior_zeroSet_eq_empty_of_differentiable_aux hf hne

example {f : E → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0) (x : E) :
    x ∉ interior {x | f x = 0} := by
  rw [spec_interior_zeroSet_eq_empty_of_differentiable hf hne]
  exact notMem_empty x

end NormedSpace

section Theta

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The zero set of a theta function is invariant under the lattice: the factor of automorphy
`holFactor D l v` never vanishes.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §3.1 and §4.1. -/
theorem spec_theta_add_eq_zero_iff (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D)
    (l : D.lattice) (v : V) : θ (v + l) = 0 ↔ θ v = 0 :=
  spec_theta_add_eq_zero_iff_aux D hθ l v

example (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D) (l : D.lattice) :
    θ l = 0 ↔ θ 0 = 0 := by
  simpa using spec_theta_add_eq_zero_iff D hθ l 0

/-- The preimage in `V` of the divisor of a theta function is exactly its zero set.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §4.1. -/
theorem spec_preimage_thetaDivisor (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D) :
    proj D.lattice ⁻¹' thetaDivisor D θ = {v | θ v = 0} :=
  spec_preimage_thetaDivisor_aux D hθ

example (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D) (v : V) :
    proj D.lattice v ∈ thetaDivisor D θ ↔ θ v = 0 := by
  rw [← mem_preimage, spec_preimage_thetaDivisor D hθ, mem_ofPred_eq]

/-- The divisor of a theta function is closed in the torus `V ⧸ Λ`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §4.1; the projection
`V → V ⧸ Λ` is an open quotient map (Bourbaki, *Topologie générale*, ch. III, §2.4). -/
theorem spec_isClosed_thetaDivisor (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D) :
    IsClosed (thetaDivisor D θ) :=
  spec_isClosed_thetaDivisor_aux D hθ

example (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D) :
    IsOpen (thetaDivisor D θ)ᶜ :=
  (spec_isClosed_thetaDivisor D hθ).isOpen_compl

/-- The divisor of a nonzero theta function has empty interior in the torus; in particular it is
a proper subset.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §4.1; Gunning--Rossi, *Analytic
Functions of Several Complex Variables*, Ch. I, §A, Theorem 6 (identity theorem). -/
theorem spec_interior_thetaDivisor_eq_empty (D : Datum (V := V)) {θ : V → ℂ}
    (hθ : θ ∈ sections D) (hne : θ ≠ 0) : interior (thetaDivisor D θ) = ∅ :=
  spec_interior_thetaDivisor_eq_empty_aux D hθ hne

example (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D) (hne : θ ≠ 0) :
    thetaDivisor D θ ≠ univ := fun h => by
  have := spec_interior_thetaDivisor_eq_empty D hθ hne
  rw [h, interior_univ] at this
  exact univ_nonempty.ne_empty this

end Theta

/-- Genus one: the zero set of a theta function on `ℂ` is closed analytic. An entire function of
one variable is analytic.

Source: Ahlfors, *Complex Analysis*, 3rd ed., Ch. 5, §1.2 (Taylor series of a holomorphic
function); Mathlib's `Differentiable.analyticAt`; Birkenhake--Lange, *Complex Abelian
Varieties*, 2nd ed., §3.1. -/
theorem spec_isClosedAnalytic_theta_genusOne (D : Datum (V := ℂ)) {θ : ℂ → ℂ}
    (hθ : θ ∈ sections D) : IsClosedAnalytic ℂ {z | θ z = 0} :=
  spec_isClosedAnalytic_theta_genusOne_aux D hθ

example (τ : ℂ) (hτ : 0 < τ.im) : ∃ D : Datum (V := ℂ), D.lattice = Submodule.span ℤ {1, τ} ∧
    IsClosedAnalytic ℂ
      {z | Complex.exp (Real.pi * z ^ 2 / (2 * τ.im)) * jacobiTheta₂ z τ = 0} := by
  obtain ⟨D, hL, -, -, hθ, -⟩ := spec_jacobiTheta₂_section τ hτ
  exact ⟨D, hL, spec_isClosedAnalytic_theta_genusOne D hθ⟩

/-- **Falsification for (c), part one.**  The integers form a closed analytic subset of `ℂ`: they
are the zeros of the entire function `sin (π z)`.

Source: Mathlib's `Complex.sin_eq_zero_iff`; Gunning--Rossi, *Analytic Functions of Several
Complex Variables*, Ch. II, §E, Definition 1. -/
theorem spec_isClosedAnalytic_range_intCast :
    IsClosedAnalytic ℂ (range ((↑) : ℤ → ℂ)) :=
  spec_isClosedAnalytic_range_intCast_aux

example : IsClosed (range ((↑) : ℤ → ℂ)) := spec_isClosedAnalytic_range_intCast.isClosed

/-- **Falsification for (c), part two.**  The integers are not Zariski closed in `𝔸¹(ℂ)`: they are
not the common zero set of any family of polynomials (a polynomial vanishing at infinitely many
points is zero, and `ℤ ≠ ℂ`). So "closed analytic implies algebraic" needs compactness.

Source: Hartshorne, *Algebraic Geometry*, Ch. I, Example 1.1.2 (the Zariski closed subsets of
`𝔸¹` are the finite sets and `𝔸¹`); Mathlib's `Polynomial.eq_zero_of_infinite_isRoot`. -/
theorem spec_range_intCast_not_zariskiClosed :
    ¬ ∃ S : Set (Polynomial ℂ), range ((↑) : ℤ → ℂ) = {z | ∀ p ∈ S, p.eval z = 0} :=
  spec_range_intCast_not_zariskiClosed_aux

example : ¬ ∃ p : Polynomial ℂ, range ((↑) : ℤ → ℂ) = {z | p.eval z = 0} := by
  rintro ⟨p, hp⟩
  exact spec_range_intCast_not_zariskiClosed ⟨{p}, by simpa using hp⟩

section ComplexPoints

open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- **Algebraic implies analytic.**  For a smooth integral `X` over `ℂ`, the complex points of a
Zariski closed subset `C ⊆ X` form a closed analytic subset of the complex manifold `X(ℂ)` (charted
on `ℂ^{dim X}` by upstream's algebraic coordinates): on an affine open `W`, `C ∩ W` is the common
zero set of finitely many regular functions (`W` is noetherian), and regular functions are
analytic in the charts. This is the easy converse of Chow's theorem; Chow's theorem itself is not
claimed.

Source: Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956), §2,
no. 5 (the analytic space `X^h`, algebraic subsets are analytic); upstream's
`AlgebraicGeometry.ComplexPoint.analyticAt_localChart_symm_evaluate` and
`AlgebraicGeometry.ComplexPoint.mem_overOpen_basicOpen_iff_evaluate_ne_zero`. -/
theorem spec_isClosedAnalytic_preimage_underlying (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] {C : Set X.left} (hC : IsClosed C) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ)
      ((Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :=
  spec_isClosedAnalytic_preimage_underlying_aux X hC

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (x : X.left) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ)
      ((Point.underlying : ComplexPoint X → X.left) ⁻¹' closure {x}) :=
  spec_isClosedAnalytic_preimage_underlying X isClosed_closure

end ComplexPoints

end HodgeLean.Foundations.AnalyticDivisorAlgebraic

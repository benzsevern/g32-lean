import HodgeLean.Adapters.ThetaDivisorOnXProofs

/-! # The theta divisor on `X(ℂ)` is a proper nonempty closed analytic zero locus: frozen specification

Scope (Appell–Humbert stage 5c, the adapter that the third Chow/GAGA stage deferred,
`docs/specs/AnalyticDivisorAlgebraic3.md`). For a smooth projective integral complex group `X`
with S12 period lattice `Λ ⊆ ℂ^g`, `g = dim X.left`, exponential `exp = abelianExp X`, and an
Appell–Humbert datum `D = datumOfX X H E hE χ hχ`, the zero locus on `X(ℂ)` of a function `θ` is
`thetaZeroLocusX X θ = exp({θ = 0})` (stage 5a). Claimed:
* for every datum on a finite-dimensional space, a twist `D.twist w` with `E(Λ, w) ⊆ ℤ` is `D`
  itself;
* for positive definite `H` on a nonzero space, every nonzero theta function has a zero (Liouville
  on a complex line: `|θ(v)|⁻¹ e^{(π/2)H(v, v)}` is `Λ`-periodic, hence bounded);
* closed analyticity descends along `exp`: a `Λ`-invariant closed analytic subset of `ℂ^g` has a
  closed analytic image in `X(ℂ)` (the assembly of the gaga3 descent theorem with the unif lane's
  local biholomorphy of `exp` and S12 surjectivity);
* for every theta function `θ` of `L(H, χ)`, `thetaZeroLocusX X θ` is closed analytic in `X(ℂ)`,
  and so is the image of the singular locus `{θ = 0, dθ = 0}` of the equation;
* for positive definite `H` and `g > 0`: `L(H, χ)` has a nonzero theta function, and the zero locus
  of every nonzero one is a closed analytic, nonempty subset of `X(ℂ)` with empty interior (in
  particular proper), the implication from this file's statements, stage 5a's empty interior and
  stage 5b's existence;
* translations: the zero locus of the translate `v ↦ e^{-π H(w, v)} θ(v + w)` is the translate of
  `thetaZeroLocusX X θ` by `exp w`, for every `θ`; for `E(Λ, w) ⊆ ℤ`, the translate of the zero
  locus of a nonzero theta function of `L(H, χ)` is the zero locus of another one;
* falsifications: for `H = 0` and a nontrivial `χ` there is no nonzero section, so the zero locus of
  every section is all of `X(ℂ)` and there is no divisor; for the trivial datum the constant `1` is
  a section with empty zero locus, so positivity is needed for nonemptiness.

Not claimed: that the zero locus has a regular point as an analytic set (a point near which it is a
complex submanifold of codimension one), nor that the regular points of the equation are dense in
it; both need a reduced local equation (Weierstrass preparation), and the second is false for
`θ²`. Not claimed either: irreducible components, multiplicities, the divisor `(θ)` with
multiplicities; that the zero locus is algebraic (Chow/GAGA); its cycle class; `dim sections D`;
any projective embedding or `LefschetzOneOneHyp` (`docs/specs/ThetaDivisorOnX.md`).
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open scoped Manifold CategoryTheory.MonObj

namespace HodgeLean.Adapters

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- A twist by a vector `w` with `E(l, w) ∈ ℤ` for every lattice vector `l` is the datum itself: the
semicharacter is multiplied by `exp(2πi E(l, w)) = 1`, and the lattice, form and integrality are
unchanged. So `t_w^* L(H, χ) ≅ L(H, χ)` for such `w`, the points of `K(L)` lifted to `V`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 2.3.2 and §2.4 (`K(L)` is
`Λ(L) / Λ` with `Λ(L) = {w | E(w, Λ) ⊆ ℤ}`); `Datum.twist`, `spec_twist_lattice`. -/
theorem spec_twist_eq_self_of_integral (D : Datum (V := V)) (w : V)
    (hw : ∀ l : D.lattice, ∃ n : ℤ, D.hermitian.imaginary l w = n) :
    D.twist w = D :=
  spec_twist_eq_self_of_integral_aux D w hw

example (D : Datum (V := V)) (m : D.lattice) : D.twist m = D :=
  spec_twist_eq_self_of_integral D m (fun l ↦ D.integral l m)

/-- For positive definite `H` on a nonzero space, every nonzero theta function has a zero. If `θ`
had none, `ρ(v) = |θ(v)|⁻¹ exp((π/2) Re H(v, v))` would be continuous and `Λ`-periodic
(`|a(l, v)| = exp(π Re H(l, v) + (π/2) H(l, l))` and `Re H(v + l, v + l) = Re H(v, v)
+ 2 Re H(l, v) + H(l, l)`), hence bounded by compactness of `V ⧸ Λ`. On a line `t ↦ t u`, `u ≠ 0`,
the entire function `1 / θ(t u)` is then bounded by `C exp(-(π/2) H(u, u) |t|²)`, so it tends to `0`
and is `0` by Liouville's theorem, which is absurd.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §3.1 and §4.1 (the divisor of a
theta function for a positive `H` is an effective, nonzero, ample divisor); Mumford, *Abelian
Varieties*, §3; Liouville's theorem (Mathlib `Differentiable.apply_eq_apply_of_bounded`). -/
theorem spec_exists_zero_of_isPositiveDefinite [Nontrivial V] (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) (θ : V → ℂ) (hθ : θ ∈ sections D) (hne : θ ≠ 0) :
    ∃ v : V, θ v = 0 :=
  spec_exists_zero_of_isPositiveDefinite_aux D hH θ hθ hne

example [Nontrivial V] (D : Datum (V := V)) (hH : D.hermitian.IsPositiveDefinite) (θ : V → ℂ)
    (hθ : θ ∈ sections D) (hne : θ ≠ 0) : ¬ ∀ v, θ v ≠ 0 := fun h ↦
  let ⟨v, hv⟩ := spec_exists_zero_of_isPositiveDefinite D hH θ hθ hne
  h v hv

end General

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- Closed analyticity descends along `exp : ℂ^g → X(ℂ)`: for a closed analytic `S ⊆ ℂ^g` that is
`Λ`-invariant, `exp(S)` is closed analytic in `X(ℂ)`. By invariance and S12 (kernel `Λ`),
`exp⁻¹(exp S) = S`; `exp(S)` is closed because its complement is `exp(Sᶜ)` (S12 surjectivity) and
`exp` is open; every point `exp v` lies in the target of the unif lane's local biholomorphism at
`v`; `X(ℂ)` is an analytic manifold (stage 4e's `spec_lieGroup_complexPoint`); then apply gaga3's
`spec_isClosedAnalytic_of_localBiholomorph`.
Source: Chirka, *Complex Analytic Sets*, §2.1 (analyticity is local and invariant under
biholomorphisms); Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1;
`HodgeLean.Foundations.AnalyticDivisorAlgebraic3.spec_isClosedAnalytic_of_localBiholomorph`,
`spec_complexExponential_localBiholomorph`, `spec_lieGroup_complexPoint`. -/
theorem spec_isClosedAnalytic_abelianExp_image (S : Set (Fin (dim X.left) → ℂ))
    (hS : IsClosedAnalytic (Fin (dim X.left) → ℂ) S)
    (hinv : ∀ v ∈ S, ∀ l : abelianPeriodLattice X, v + l ∈ S) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ) (abelianExp X '' S) :=
  spec_isClosedAnalytic_abelianExp_image_aux X S hS hinv

example : IsClosedAnalytic (Fin (dim X.left) → ℂ) (abelianExp X '' Set.univ) :=
  spec_isClosedAnalytic_abelianExp_image X Set.univ isClosedAnalytic_univ
    (fun _ _ _ ↦ Set.mem_univ _)

/-- **The theta divisor on `X(ℂ)` is closed analytic.** For every theta function `θ` of
`L(H, χ)`, `thetaZeroLocusX X θ = exp({θ = 0})` is closed analytic in `X(ℂ)`: `{θ = 0}` is closed
analytic in `ℂ^g` (gaga2's `spec_isClosedAnalytic_theta`) and `Λ`-invariant (`θ(v + l) = a(l, v) θ(v)`
with `a(l, v) ≠ 0`), so `spec_isClosedAnalytic_abelianExp_image` applies. No positivity is needed;
for `θ = 0` the locus is all of `X(ℂ)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1; Chirka, *Complex Analytic
Sets*, §2.1; `HodgeLean.Foundations.AnalyticDivisorAlgebraic2.spec_isClosedAnalytic_theta`,
`HodgeLean.Foundations.AnalyticDivisorAlgebraic.spec_theta_add_eq_zero_iff`,
`spec_isClosedAnalytic_abelianExp_image`. -/
theorem spec_isClosedAnalytic_thetaZeroLocusX (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ)) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ) (thetaZeroLocusX X θ) :=
  spec_isClosedAnalytic_thetaZeroLocusX_aux X H E hE χ hχ θ hθ

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ)) :
    IsClosed (thetaZeroLocusX X θ) :=
  (spec_isClosedAnalytic_thetaZeroLocusX X H E hE χ hχ θ hθ).isClosed

/-- For positive definite `H` and `g > 0`, the zero locus on `X(ℂ)` of a nonzero theta function of
`L(H, χ)` is nonempty: `spec_exists_zero_of_isPositiveDefinite` on `ℂ^g` (nonzero as `g > 0`), and
`exp` of a zero lies in the locus.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1;
`spec_exists_zero_of_isPositiveDefinite`, `thetaZeroLocusX`. -/
theorem spec_thetaZeroLocusX_nonempty (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (hH : H.IsPositiveDefinite) (hg : 0 < dim X.left)
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ))
    (hne : θ ≠ 0) :
    (thetaZeroLocusX X θ).Nonempty :=
  spec_thetaZeroLocusX_nonempty_aux X H E hE χ hχ hH hg θ hθ hne

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (hH : H.IsPositiveDefinite) (hg : 0 < dim X.left)
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ))
    (hne : θ ≠ 0) :
    thetaZeroLocusX X θ ≠ ∅ :=
  (spec_thetaZeroLocusX_nonempty X H E hE χ hχ hH hg θ hθ hne).ne_empty

/-- **The theta divisor is a proper nonempty closed analytic zero locus in `X(ℂ)`** (stage-5c
assembly). This is not yet a hypersurface statement: codimension one is expressible but not proved here. For positive definite
`H` and `g > 0`: `L(H, χ)` has a nonzero theta function (stage 5b's `spec_sections_ne_bot`), and the
zero locus of every nonzero one is closed analytic (`spec_isClosedAnalytic_thetaZeroLocusX`),
nonempty (`spec_thetaZeroLocusX_nonempty`) and has empty interior (stage 5a's
`spec_interior_thetaZeroLocusX`), so it is a proper nonempty closed analytic subset of the connected
`X(ℂ)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §3.2 and §4.1;
`spec_sections_ne_bot`, `spec_isClosedAnalytic_thetaZeroLocusX`, `spec_thetaZeroLocusX_nonempty`,
`spec_interior_thetaZeroLocusX`. -/
theorem spec_thetaZeroLocusX_proper_nonempty_closedAnalytic (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (hH : H.IsPositiveDefinite) (hg : 0 < dim X.left) :
    (∃ θ ∈ sections (datumOfX X H E hE χ hχ), θ ≠ 0) ∧
      ∀ θ ∈ sections (datumOfX X H E hE χ hχ), θ ≠ 0 →
        IsClosedAnalytic (Fin (dim X.left) → ℂ) (thetaZeroLocusX X θ) ∧
          (thetaZeroLocusX X θ).Nonempty ∧ interior (thetaZeroLocusX X θ) = ∅ :=
  spec_thetaZeroLocusX_hypersurface_aux X H E hE χ hχ hH hg

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (hH : H.IsPositiveDefinite) (hg : 0 < dim X.left) :
    ∃ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z ∧ Z.Nonempty ∧
      Z ≠ Set.univ := by
  obtain ⟨⟨θ, hθ, hne⟩, h⟩ := spec_thetaZeroLocusX_proper_nonempty_closedAnalytic X H E hE χ hχ hH hg
  obtain ⟨hZ, hn, hi⟩ := h θ hθ hne
  refine ⟨_, hZ, hn, fun hu ↦ ?_⟩
  rw [hu, interior_univ] at hi
  exact Set.univ_nonempty.ne_empty hi

/-- Translation of zero loci: for every function `θ` on `ℂ^g`, every `H` and every `w`, the zero
locus of the translate `v ↦ e^{-π H(w, v)} θ(v + w)` is the translate of the zero locus of `θ` by
`exp w`, i.e. its preimage under `x ↦ x · exp w`. The exponential factor never vanishes, and
`exp(v + w) = exp v · exp w` (S12 `complexExponentialHom`). For `θ ∈ sections D` the translate is a
theta function of `D.twist w` (`spec_sections_translate`), the datum of `t_w^* L`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 2.3.2 and §4.1
(`t_x^*(θ) = (t_x^* θ)`); S12 `complexExponentialHom`; `spec_sections_translate`. -/
theorem spec_thetaZeroLocusX_translate (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (w : Fin (dim X.left) → ℂ) :
    thetaZeroLocusX X (fun v ↦ Complex.exp (-(Real.pi * H.toFun w v)) * θ (v + w)) =
      (fun x ↦ x * abelianExp X w) ⁻¹' thetaZeroLocusX X θ :=
  spec_thetaZeroLocusX_translate_aux X H θ w

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (w : Fin (dim X.left) → ℂ) (x : ComplexPoint X) :
    x ∈ thetaZeroLocusX X (fun v ↦ Complex.exp (-(Real.pi * H.toFun w v)) * θ (v + w)) ↔
      x * abelianExp X w ∈ thetaZeroLocusX X θ := by
  rw [spec_thetaZeroLocusX_translate X H θ w]; rfl

/-- **Translation invariance of the family of theta divisors of `L(H, χ)`.** For `w` with
`E(l, w) ∈ ℤ` for every `l ∈ Λ` (a lift of a point of `K(L)`) and a nonzero theta function `θ` of
`L(H, χ)`, the translate of `thetaZeroLocusX X θ` by `exp w` is the zero locus of a nonzero theta
function of the same `L(H, χ)`: the translate `θ'(v) = e^{-π H(w, v)} θ(v + w)` lies in
`sections (D.twist w)` (`spec_sections_translate`), `D.twist w = D`
(`spec_twist_eq_self_of_integral`), `θ' ≠ 0`, and its zero locus is given by
`spec_thetaZeroLocusX_translate`. For `w ∈ Λ`, `exp w = 1` and the translation is trivial.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 2.3.2 and §2.4 (`K(L)`, and
`t_x^* L ≅ L` for `x ∈ K(L)`); `spec_sections_translate`, `spec_twist_eq_self_of_integral`,
`spec_thetaZeroLocusX_translate`. -/
theorem spec_thetaZeroLocusX_translate_of_integral
    (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ))
    (hne : θ ≠ 0) (w : Fin (dim X.left) → ℂ)
    (hw : ∀ l : abelianPeriodLattice X, ∃ n : ℤ, H.imaginary l w = n) :
    ∃ θ' ∈ sections (datumOfX X H E hE χ hχ), θ' ≠ 0 ∧
      thetaZeroLocusX X θ' = (fun x ↦ x * abelianExp X w) ⁻¹' thetaZeroLocusX X θ :=
  spec_thetaZeroLocusX_translate_of_integral_aux X H E hE χ hχ θ hθ hne w hw

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ))
    (hne : θ ≠ 0) (l : abelianPeriodLattice X) :
    ∃ θ' ∈ sections (datumOfX X H E hE χ hχ), θ' ≠ 0 ∧
      thetaZeroLocusX X θ' = (fun x ↦ x * abelianExp X l) ⁻¹' thetaZeroLocusX X θ :=
  spec_thetaZeroLocusX_translate_of_integral X H E hE χ hχ θ hθ hne l
    (fun m ↦ ⟨E m l, (hE m l).symm⟩)

/-- The singular locus of the equation descends: for a theta function `θ` of `L(H, χ)`, the image
`exp({θ = 0, dθ = 0})` is closed analytic in `X(ℂ)`. The set `{θ = 0, dθ = 0}` is closed analytic
in `ℂ^g` (gaga3's `spec_isClosedAnalytic_singularLocus`) and `Λ`-invariant (gaga's
`spec_theta_add_eq_zero_iff` and gaga3's `spec_fderiv_theta_add_eq_zero_iff`), so
`spec_isClosedAnalytic_abelianExp_image` applies. This is the singular locus of the equation `θ`,
not of the reduced hypersurface (for `θ²` it is the whole zero locus).
Source: Chirka, *Complex Analytic Sets*, §2.3 (singular points of a hypersurface);
Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1;
`HodgeLean.Foundations.AnalyticDivisorAlgebraic3.spec_isClosedAnalytic_singularLocus`,
`HodgeLean.Foundations.AnalyticDivisorAlgebraic3.spec_fderiv_theta_add_eq_zero_iff`,
`spec_isClosedAnalytic_abelianExp_image`. -/
theorem spec_isClosedAnalytic_singularLocusX
    (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ)) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ)
      (abelianExp X '' {v | θ v = 0 ∧ fderiv ℂ θ v = 0}) :=
  spec_isClosedAnalytic_singularLocusX_aux X H E hE χ hχ θ hθ

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ)) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ)
      (thetaZeroLocusX X θ ∩ abelianExp X '' {v | θ v = 0 ∧ fderiv ℂ θ v = 0}) :=
  (spec_isClosedAnalytic_thetaZeroLocusX X H E hE χ hχ θ hθ).inter
    (spec_isClosedAnalytic_singularLocusX X H E hE χ hχ θ hθ)

/-- Falsification: for `H = 0` and a nontrivial semicharacter `χ` (then a character of `Λ`),
`L(0, χ)` has no nonzero section (stage 5a's `spec_sections_eq_bot_of_hermitian_zero`), so the
zero locus of every section is all of `X(ℂ)` (S12 surjectivity) and there is no divisor. Such `χ`
exist for `g > 0` (stage 5a's `spec_exists_nontrivial_characterX`).
Source: Mumford, *Abelian Varieties*, §8 (vii) (a nontrivial `L ∈ Pic⁰(X)` has no nonzero
section); Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.2;
`spec_sections_eq_bot_of_hermitian_zero`. -/
theorem spec_thetaZeroLocusX_eq_univ_of_hermitian_zero
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m *
        Circle.exp (Real.pi * (HermitianForm.zero (V := Fin (dim X.left) → ℂ)).imaginary l m))
    (h0 : ∀ l m : abelianPeriodLattice X,
      ((0 : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) l m : ℝ) =
        (HermitianForm.zero (V := Fin (dim X.left) → ℂ)).imaginary l m)
    (hne : ∃ l, χ l ≠ 1) (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X HermitianForm.zero 0 h0 χ hχ)) :
    thetaZeroLocusX X θ = Set.univ :=
  spec_thetaZeroLocusX_eq_univ_of_hermitian_zero_aux X χ hχ h0 hne θ hθ

example (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m *
        Circle.exp (Real.pi * (HermitianForm.zero (V := Fin (dim X.left) → ℂ)).imaginary l m))
    (h0 : ∀ l m : abelianPeriodLattice X,
      ((0 : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) l m : ℝ) =
        (HermitianForm.zero (V := Fin (dim X.left) → ℂ)).imaginary l m)
    (hne : ∃ l, χ l ≠ 1) :
    ¬ ∃ θ ∈ sections (datumOfX X HermitianForm.zero 0 h0 χ hχ),
      interior (thetaZeroLocusX X θ) = ∅ := by
  rintro ⟨θ, hθ, hi⟩
  rw [spec_thetaZeroLocusX_eq_univ_of_hermitian_zero X χ hχ h0 hne θ hθ, interior_univ] at hi
  exact Set.univ_nonempty.ne_empty hi

/-- Falsification for nonemptiness: for the trivial datum (`H = 0`, `χ = 1`) the constant `1` is a
nonzero theta function (`holFactor = 1`) with empty zero locus. So positivity of `H` cannot be
dropped from `spec_thetaZeroLocusX_nonempty`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3 (the trivial bundle
has the constant sections); `datumOfXTrivial`. -/
theorem spec_thetaZeroLocusX_trivial_eq_empty :
    (fun _ ↦ (1 : ℂ)) ∈ sections (datumOfXTrivial X) ∧
      thetaZeroLocusX X (fun _ ↦ (1 : ℂ)) = ∅ :=
  spec_thetaZeroLocusX_trivial_eq_empty_aux X

example : ∃ θ ∈ sections (datumOfXTrivial X), θ ≠ 0 ∧ thetaZeroLocusX X θ = ∅ :=
  ⟨_, (spec_thetaZeroLocusX_trivial_eq_empty X).1, fun h ↦ one_ne_zero (congrFun h 0),
    (spec_thetaZeroLocusX_trivial_eq_empty X).2⟩

end HodgeLean.Adapters

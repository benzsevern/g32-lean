module

public import HodgeLean.Foundations.Program.GaussManinToriLatticeProofs

/-!
# Period matrices, their lattices and `H^{1,0}` (FROZEN SPEC, Mathlib only)

Track D2. The statements about a single period matrix that need only Mathlib, frozen apart from
the variation so that they elaborate without the repository's Hodge vocabulary. Each theorem is
the matching `_aux` theorem of `GaussManinToriLatticeProofs.lean`.

Claimed:
* the columns of a period matrix span a full lattice (`DiscreteTopology`, `IsZLattice ℝ`), and the
  marking `ℤ^{2g} → Λ` is injective;
* a Riemann form forces a period matrix;
* `F¹ = H^{1,0}` has dimension `g`;
* witnesses: `(1, τ)` is a period matrix when `Im τ ≠ 0`, and the standard form is a Riemann form
  for it exactly when `Im τ > 0` (for `Im τ < 0` it is not).

Not claimed: anything about variations, period maps or families; the comparison of Riemann forms
with `HermitianForm`, the Hodge filtration and its polarization, which are in
`GaussManinTori.lean`. HC no distance; AV milestone no distance.
-/

@[expose] public noncomputable section

open scoped TensorProduct Matrix

namespace HodgeLean.Foundations.Program

section EllipticWitnesses

/-- `(1, τ)` is a period matrix exactly off the real line; here, when `Im τ ≠ 0`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §8.1. -/
theorem d2_ellipticPeriod_isPeriodMatrix {τ : ℂ} (hτ : τ.im ≠ 0) :
    d2_IsPeriodMatrix (d2_ellipticPeriod τ) :=
  d2_ellipticPeriod_isPeriodMatrix_aux hτ

example : d2_IsPeriodMatrix (d2_ellipticPeriod Complex.I) :=
  d2_ellipticPeriod_isPeriodMatrix (by simp)

/-- The standard form `[[0, 1], [-1, 0]]` is a Riemann form for `(1, τ)` when `Im τ > 0`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §8.1 (the upper half plane
parametrizes principally polarized elliptic curves). -/
theorem d2_ellipticPeriod_isRiemannForm {τ : ℂ} (hτ : 0 < τ.im) :
    d2_IsRiemannForm (d2_ellipticPeriod τ) d2_stdRiemann :=
  d2_ellipticPeriod_isRiemannForm_aux hτ

example : d2_IsRiemannForm (d2_ellipticPeriod Complex.I) d2_stdRiemann :=
  d2_ellipticPeriod_isRiemannForm (by simp)

/-- The degenerate case: for `Im τ < 0` the standard form is not a Riemann form for `(1, τ)`
(positivity fails; `-[[0, 1], [-1, 0]]` is the Riemann form there).
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §8.1. -/
theorem d2_ellipticPeriod_not_isRiemannForm {τ : ℂ} (hτ : τ.im < 0) :
    ¬ d2_IsRiemannForm (d2_ellipticPeriod τ) d2_stdRiemann :=
  d2_ellipticPeriod_not_isRiemannForm_aux hτ

example : ¬ d2_IsRiemannForm (d2_ellipticPeriod (-Complex.I)) d2_stdRiemann :=
  d2_ellipticPeriod_not_isRiemannForm (by simp)

end EllipticWitnesses

section Lattice

variable {g : ℕ} {P : Fin g → Fin (2 * g) → ℂ}

/-- The lattice spanned by the columns of a period matrix is discrete.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; Mathlib `ZSpan`. -/
theorem d2_lattice_discrete (hP : d2_IsPeriodMatrix P) : DiscreteTopology (d2_lattice P) :=
  d2_lattice_discrete_aux hP

example : DiscreteTopology (d2_lattice (d2_ellipticPeriod Complex.I)) :=
  d2_lattice_discrete (d2_ellipticPeriod_isPeriodMatrix (by simp))

/-- The lattice spanned by the columns of a period matrix is a full lattice, so `ℂ^g / Λ` is a
compact torus (`LatticeTorus.quotientEquiv`).
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; Mathlib `ZSpan`. -/
theorem d2_lattice_isZLattice (hP : d2_IsPeriodMatrix P) :
    haveI := d2_lattice_discrete hP
    IsZLattice ℝ (d2_lattice P) :=
  d2_lattice_isZLattice_aux hP

example (hP : d2_IsPeriodMatrix P) : haveI := d2_lattice_discrete hP
    Module.finrank ℤ (d2_lattice P) = 2 * g := by
  have := d2_lattice_discrete hP
  have := d2_lattice_isZLattice hP
  rw [ZLattice.rank ℝ (d2_lattice P), Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

/-- The marking `ℤ^{2g} → Λ` of a period matrix is injective: it is an isomorphism onto the
lattice, so `H¹(ℂ^g/Λ, ℚ) = Hom(Λ, ℚ) = ℚ^{2g}`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
theorem d2_markingMap_injective (hP : d2_IsPeriodMatrix P) :
    Function.Injective (d2_markingMap P) :=
  d2_markingMap_injective_aux hP

example (hP : d2_IsPeriodMatrix P) (n : Fin (2 * g) → ℤ) (h : d2_markingMap P n = 0) :
    n = 0 :=
  d2_markingMap_injective hP (h.trans (map_zero _).symm)

/-- A Riemann form forces a period matrix: `E(s, i s) > 0` for `s ≠ 0` makes the real map
injective.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 and Lemma 1.3.1. -/
theorem d2_isPeriodMatrix_of_isRiemannForm {A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}
    (hA : d2_IsRiemannForm P A) : d2_IsPeriodMatrix P :=
  d2_isPeriodMatrix_of_isRiemannForm_aux hA

example {τ : ℂ} (hτ : 0 < τ.im) : d2_IsPeriodMatrix (d2_ellipticPeriod τ) :=
  d2_isPeriodMatrix_of_isRiemannForm (d2_ellipticPeriod_isRiemannForm hτ)

/-- `H^{1,0}` of a `g`-dimensional complex torus has dimension `g`: a `ℂ`-linear form vanishing
on the lattice vanishes.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.4. -/
theorem d2_finrank_hodgeOne (hP : d2_IsPeriodMatrix P) : Module.finrank ℂ (d2_hodgeOne P) = g :=
  d2_finrank_hodgeOne_aux hP

example {τ : ℂ} (hτ : τ.im ≠ 0) :
    Module.finrank ℂ (d2_hodgeOne (d2_ellipticPeriod τ)) = 1 :=
  d2_finrank_hodgeOne (d2_ellipticPeriod_isPeriodMatrix hτ)

end Lattice

end HodgeLean.Foundations.Program

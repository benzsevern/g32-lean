import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HodgeLean.Foundations.Symplectic

/-! # Definitions for the Appell--Humbert core spec (FROZEN)

This file is part of the frozen Appell--Humbert lattice-and-forms spec. Do not edit it.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.AppellHumbert

section Forms

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V]
  [IsScalarTower ℝ ℂ V]

/-- A complex Hermitian form, recorded with the convention that it is conjugate-linear in its
first argument and complex-linear in its second argument.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1. -/
structure HermitianForm where
  toFun : V → V → ℂ
  add_left : ∀ x y z, toFun (x + y) z = toFun x z + toFun y z
  smul_left : ∀ (c : ℂ) x y, toFun (c • x) y = star c * toFun x y
  add_right : ∀ x y z, toFun x (y + z) = toFun x y + toFun x z
  smul_right : ∀ (c : ℂ) x y, toFun x (c • y) = c * toFun x y
  conj_symm : ∀ x y, star (toFun y x) = toFun x y

/-- The imaginary alternating form underlying a Hermitian form.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1. -/
def HermitianForm.imaginary (H : HermitianForm (V := V)) (x y : V) : ℝ :=
  (H.toFun x y).im

example (H : HermitianForm (V := V)) (x y : V) :
    H.imaginary x y = (H.toFun x y).im := rfl

/-- Positive definiteness of a Hermitian form.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Chapter 4. -/
def HermitianForm.IsPositiveDefinite (H : HermitianForm (V := V)) : Prop :=
  ∀ v, v ≠ 0 → 0 < (H.toFun v v).re

example (H : HermitianForm (V := V)) : H.IsPositiveDefinite ↔
    ∀ v, v ≠ 0 → 0 < (H.toFun v v).re := Iff.rfl

/-- Invariance under the complex structure, the first Riemann relation for a real bilinear form.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1. -/
def IsTypeOneOne (E : V → V → ℝ) : Prop :=
  ∀ v w, E (Complex.I • v) (Complex.I • w) = E v w

example (E : V → V → ℝ) : IsTypeOneOne E ↔
    ∀ v w, E (Complex.I • v) (Complex.I • w) = E v w := Iff.rfl

/-- Kernel nondegeneracy for a real-valued form. This is the form-side condition which is later
transported to `Symplectic.IsNondegenerate` for a polarization 2-vector.

Source: Bourbaki, *Algèbre*, ch. IX, §5. -/
def IsNondegenerate (E : V → V → ℝ) : Prop :=
  ∀ v, (∀ w, E v w = 0) → v = 0

example (E : V → V → ℝ) : IsNondegenerate E ↔
    ∀ v, (∀ w, E v w = 0) → v = 0 := Iff.rfl

end Forms

/-- A positive-semidefinite Hermitian form on `ℂ²` that is degenerate: `H(v,w) = conj(v₀) w₀`.
It is the witness that positivity cannot be weakened to semipositivity.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 (the forms on
`ℂ²` with `H(v,w) = ∑ conj(vᵢ) aᵢ wᵢ`, here `a = (1,0)`). -/
def degenerateForm : HermitianForm (V := Fin 2 → ℂ) where
  toFun v w := star (v 0) * w 0
  add_left x y z := by simp [add_mul]
  smul_left c x y := by simp [mul_assoc]
  add_right x y z := by simp [mul_add]
  smul_right c x y := by simp; ring
  conj_symm x y := by simp [mul_comm]

example (v w : Fin 2 → ℂ) : degenerateForm.toFun v w = star (v 0) * w 0 := rfl

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- An Appell--Humbert datum on a full real lattice in a finite-dimensional complex normed
space. The lattice is a discrete `ℤ`-submodule spanning `V` over `ℝ` (`IsZLattice ℝ`); it is then
finitely generated and free of rank `dim_ℝ V = 2 dim_ℂ V` (`ZLattice.module_finite`,
`ZLattice.rank`). Integrality is stated directly on lattice points, and the semicharacter is
circle-valued.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (lattices) and
Theorem 2.2.3. -/
structure Datum where
  lattice : Submodule ℤ V
  [discrete : DiscreteTopology lattice]
  [isZLattice : IsZLattice ℝ lattice]
  hermitian : HermitianForm (V := V)
  integral : ∀ l m : lattice, ∃ n : ℤ, hermitian.imaginary l m = n
  semicharacter : lattice → Circle
  semicharacter_add : ∀ l m,
    semicharacter (l + m) = semicharacter l * semicharacter m *
      Circle.exp (Real.pi * hermitian.imaginary l m)

attribute [instance] Datum.discrete Datum.isZLattice

example (D : Datum (V := V)) (l m : D.lattice) :
    D.semicharacter (l + m) = D.semicharacter l * D.semicharacter m *
      Circle.exp (Real.pi * D.hermitian.imaginary l m) :=
  D.semicharacter_add l m

example (D : Datum (V := V)) : Module.Finite ℤ D.lattice := ZLattice.module_finite ℝ D.lattice

example (D : Datum (V := V)) : Module.finrank ℤ D.lattice = 2 * Module.finrank ℂ V := by
  rw [ZLattice.rank ℝ D.lattice, finrank_real_of_complex]

/-- The Appell--Humbert factor of automorphy.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3. -/
def factor (D : Datum (V := V)) (l : D.lattice) (v : V) : ℂ :=
  (D.semicharacter l : ℂ) * Complex.exp
    (Real.pi * D.hermitian.toFun v l + (Real.pi / 2) * D.hermitian.toFun l l)

example (D : Datum (V := V)) (l : D.lattice) (v : V) :
    factor D l v = (D.semicharacter l : ℂ) * Complex.exp
      (Real.pi * D.hermitian.toFun v l + (Real.pi / 2) * D.hermitian.toFun l l) := rfl

end Lattice

end HodgeLean.Foundations.AppellHumbert

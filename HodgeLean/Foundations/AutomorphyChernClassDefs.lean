import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import HodgeLean.Foundations.AppellHumbertSectionsDefs

/-! # Definitions for the first Chern class of a factor of automorphy (FROZEN)

This file is part of the frozen spec of the alternating form of a factor of automorphy
(Appell--Humbert stage 3, Chern-class side). Do not edit it after review.
HC no distance; AV milestone no distance.

A factor `a : L → V → ℂ` is written `a l v = exp(2πi f l v)`. The logarithm `f` is an explicit
argument everywhere: nothing here assumes it exists, is continuous, or that `a` is a cocycle. The
statements take those as explicit hypotheses.
-/

noncomputable section

namespace HodgeLean.Foundations.AutomorphyChernClass

open AppellHumbert

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}

/-- The alternating expression of a logarithm `f` of a factor of automorphy, at the base point
`v`: `E_f(l, m) = f(m, v + l) + f(l, v) - f(l, v + m) - f(m, v)`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2. -/
def logForm (f : L → V → ℂ) (v : V) (l m : L) : ℂ :=
  f m (v + l) + f l v - f l (v + m) - f m v

example (f : L → V → ℂ) (v : V) (l m : L) :
    logForm f v l m = f m (v + l) + f l v - f l (v + m) - f m v := rfl

example (f : L → V → ℂ) (v : V) (l : L) : logForm f v l l = 0 := by
  simp [logForm]

/-- The integer-valued form of a logarithm `f`: the value of `logForm f` at the base point `0`,
read off by rounding its real part. For a continuous logarithm of a cocycle, `logForm f v l m` is
an integer independent of `v`, and rounding is exact on integers; without those hypotheses this
is only a function `L → L → ℤ` with no claimed meaning.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2. -/
def chernForm (f : L → V → ℂ) (l m : L) : ℤ :=
  round (logForm f 0 l m).re

example (f : L → V → ℂ) (l m : L) : chernForm f l m = round (logForm f 0 l m).re := rfl

example (l m : L) : chernForm (0 : L → V → ℂ) l m = 0 := by
  simp [chernForm, logForm]

end General

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- A logarithm of the holomorphic Appell--Humbert factor `holFactor D`:
`f(l, v) = arg χ(l) / 2π + (π H(l, v) + (π/2) H(l, l)) / 2πi`, so that
`exp(2πi f(l, v)) = χ(l) exp(π H(l, v) + (π/2) H(l, l))` because `|χ(l)| = 1`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 and Theorem 2.2.3. -/
def holLog (D : Datum (V := V)) (l : D.lattice) (v : V) : ℂ :=
  ((D.semicharacter l : ℂ).arg : ℂ) / (2 * Real.pi) +
    (Real.pi * D.hermitian.toFun l v + (Real.pi / 2) * D.hermitian.toFun l l) /
      (2 * Real.pi * Complex.I)

example (D : Datum (V := V)) (l : D.lattice) (v : V) :
    holLog D l v = ((D.semicharacter l : ℂ).arg : ℂ) / (2 * Real.pi) +
      (Real.pi * D.hermitian.toFun l v + (Real.pi / 2) * D.hermitian.toFun l l) /
        (2 * Real.pi * Complex.I) := rfl

end Lattice

end HodgeLean.Foundations.AutomorphyChernClass

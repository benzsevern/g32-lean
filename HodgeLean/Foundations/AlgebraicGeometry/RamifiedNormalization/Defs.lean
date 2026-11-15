import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart
import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialCover
import HodgeLean.Foundations.Program.SchoenTowerFibreDefs
import Mathlib.Topology.Connected.Clopen

/-! # Original-field charts and the compact two-branch model

The chart keeps the existing quotient presentation. Its normalization is taken
inside the supplied covering field. The compact model is an abbreviation of
an existing type; no identification with a scheme fibre is part of this file.
HC no distance; AV milestone no distance. -/

noncomputable section
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization

/-- The quotient chart map to the original field, with ratio u/v.
Source: Barth–Hulek–Peters–Van de Ven, Compact Complex Surfaces, III.5;
Hartshorne, Algebraic Geometry, II.7, affine blowup charts. -/
def chartMap {R K : Type*} [CommRing R] [Field K] (f : R →+* K)
    (u v : R) (hv : f v ≠ 0) : RegularPairChart.ring u v →+* K :=
  Ideal.Quotient.lift _ (Polynomial.eval₂RingHom f (f u / f v)) (by
    change Ideal.span _ ≤ RingHom.ker (Polynomial.eval₂RingHom f (f u / f v))
    apply Ideal.span_le.mpr
    intro p hp
    have hp' : p = Polynomial.C u - Polynomial.X * Polynomial.C v :=
      Set.mem_singleton_iff.mp hp
    rw [hp']
    change Polynomial.eval₂ f (f u / f v)
      (Polynomial.C u - Polynomial.X * Polynomial.C v) = 0
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    exact sub_eq_zero.mpr (div_mul_cancel₀ (f u) hv).symm)

example : chartMap (RingHom.id ℚ) (6 : ℚ) (2 : ℚ) (by norm_num)
    (RegularPairChart.ratio (6 : ℚ) (2 : ℚ)) = 3 := by
  norm_num [chartMap, RegularPairChart.ratio]

/-- Integral elements of the supplied field for the specified chart map.
The ambient field is an argument, not a newly chosen binomial extension.
Source: Esnault–Viehweg, Lectures on Vanishing Theorems, §3, cyclic covers
and normalization; Mathlib, integralClosure. -/
def normalizedChart {A K : Type*} [CommRing A] [Field K] (f : A →+* K) :
    Subring K := by
  letI := f.toAlgebra
  exact (integralClosure A K).toSubring

example : (3 : ℚ) ∈ normalizedChart (RingHom.id ℚ) :=
  (show _root_.IsIntegral ℚ (3 : ℚ) from isIntegral_algebraMap (x := (3 : ℚ)))

/-- The existing compact model with gcd(m,a) labelled sphere components.
Source: Barth–Hulek–Peters–Van de Ven, Compact Complex Surfaces, III.5;
existing SchoenTowerFibreDefs.s2c_twoPointFibre. -/
abbrev componentModel (m a : ℕ) :=
  HodgeLean.Foundations.Program.s2c_twoPointFibre m a

example : (1 : ZMod (Nat.gcd 6 2)) ≠ 0 ∧
    Nonempty (componentModel 6 2) := by
  refine ⟨by decide, ⟨(1, ((2 : ℂ) : OnePoint ℂ))⟩⟩

/-- The existing component translation and dilation, including the wrap.
Source: Barth–Hulek–Peters–Van de Ven, Compact Complex Surfaces, III.5;
existing SchoenTowerFibreDefs.s2c_twoPointDeck. -/
abbrev deck (m a : ℕ) (c : ℂ) (hc : c ≠ 0) :
    componentModel m a ≃ₜ componentModel m a :=
  HodgeLean.Foundations.Program.s2c_twoPointDeck m a c hc

example : (deck 6 2 (-1) (by norm_num)
    ((1 : ZMod (Nat.gcd 6 2)), ((2 : ℂ) : OnePoint ℂ))).2 =
      ((-2 : ℂ) : OnePoint ℂ) := by
  change (((-1 : ℂ) * 2 : ℂ) : OnePoint ℂ) = _
  norm_num

/-- The existing degree m/gcd(m,a) projection with its component phase.
Source: Esnault–Viehweg, Lectures on Vanishing Theorems, §3;
existing SchoenTowerFibreDefs.s2c_twoPointProjection. -/
abbrev projection (m a : ℕ) (c : ℂ) : componentModel m a → OnePoint ℂ :=
  HodgeLean.Foundations.Program.s2c_twoPointProjection m a c

example : projection 6 2 (-1)
    ((1 : ZMod (Nat.gcd 6 2)), ((2 : ℂ) : OnePoint ℂ)) =
      ((-8 : ℂ) : OnePoint ℂ) := by
  change (( (-1 : ℂ) ^ (-((6 / Nat.gcd 6 2 *
    (1 : ZMod (Nat.gcd 6 2)).val : ℕ) : ℤ)) * 2 ^ (6 / Nat.gcd 6 2) : ℂ) :
      OnePoint ℂ) = _
  norm_num [ZMod.val_one_eq_one_mod]

/-- Automorphisms fixing every value of a specified point evaluation.
Source: Esnault–Viehweg, Lectures on Vanishing Theorems, §3, inertia at
geometric points; TameMonomialCover.integralClosure_inertia. -/
def evaluationStabilizer {R A F : Type*} [CommRing R] [CommRing A]
    [CommRing F] [Algebra R A] (p : A →+* F) : Subgroup (A ≃ₐ[R] A) where
  carrier := {g | ∀ b, p (g b) = p b}
  one_mem' _ := rfl
  mul_mem' hg hk b := (hg _).trans (hk b)
  inv_mem' := fun {g} hg b => by
    have H := hg (g⁻¹ b)
    simpa only [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] using H.symm

example : Polynomial.algEquivAevalNegX (R := ℂ) ∈
    evaluationStabilizer (Polynomial.evalRingHom (0 : ℂ)) := by
  intro p
  change (p.comp (-Polynomial.X)).eval 0 = p.eval 0
  simp [Polynomial.eval_comp]

end AlgebraicGeometry.RamifiedNormalization

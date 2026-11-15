import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Field.Rat

/-! # Rational finite-group traces and invariant duality

The algebraic layer for deck actions; geometric duality is a separate input.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.QuotientDuality

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- Fixed vectors as a rational submodule.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2. -/
def fixed (ρ : G →* (V ≃ₗ[ℚ] V)) : Submodule ℚ V where
  carrier := {v | ∀ g, ρ g v = v}
  zero_mem' := by intro g; exact map_zero _
  add_mem' := by intro x y hx hy g; rw [map_add, hx g, hy g]
  smul_mem' := by intro a x hx g; rw [map_smul, hx g]

/-- Normalized deck trace, including stabilizers.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2. -/
def trace (ρ : G →* (V ≃ₗ[ℚ] V)) : V →ₗ[ℚ] V :=
  (Fintype.card G : ℚ)⁻¹ • ∑ g : G, (ρ g).toLinearMap

/-- Restriction of a bilinear pairing to the two fixed submodules.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2. -/
def fixedPairing (ρ : G →* (V ≃ₗ[ℚ] V)) (σ : G →* (W ≃ₗ[ℚ] W))
    (B : V →ₗ[ℚ] Module.Dual ℚ W) :
    fixed ρ →ₗ[ℚ] Module.Dual ℚ (fixed σ) :=
  (LinearMap.dualMap (fixed σ).subtype) ∘ₗ B ∘ₗ (fixed ρ).subtype

/-- Orbit trace on rational functions, with inverse pullback convention.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2. -/
def orbitTrace {X : Type*} [MulAction G X] (f : X → ℚ) (x : X) : ℚ :=
  (Fintype.card G : ℚ)⁻¹ * ∑ g : G, f (g⁻¹ • x)


private def trivial : Unit →* (ℚ ≃ₗ[ℚ] ℚ) := 1

-- Positive-rank tests with a nonzero vector and pairing.
example : (3 : ℚ) ∈ fixed trivial := by intro g; rfl
example : trace trivial (3 : ℚ) = 3 := by
  simp [trace, trivial]
example : (trace trivial).comp (trace trivial) = trace trivial := by
  ext x
  simp [trace, trivial]
example : (LinearMap.mul ℚ ℚ) (trace trivial 2) 3 =
    (LinearMap.mul ℚ ℚ) 2 (trace trivial 3) := by
  norm_num [trace, trivial]
example : Function.Bijective
    (fixedPairing trivial trivial (LinearMap.mul ℚ ℚ)) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have he := congrArg (fun l => l ⟨1, by intro g; rfl⟩) h
    simpa [fixedPairing] using he
  · intro l
    refine ⟨⟨l ⟨1, by intro g; rfl⟩, by intro g; rfl⟩, ?_⟩
    ext w
    have hw : w = (w : ℚ) • (⟨1, by intro g; rfl⟩ : fixed trivial) := by
      apply Subtype.ext
      simp
    conv_rhs => rw [hw, map_smul]
    simp [fixedPairing, mul_comm]
example : orbitTrace (G := Unit) (fun x : ℚ => 2 * x) (3 : ℚ) = 6 := by
  norm_num [orbitTrace]

end HodgeLean.Foundations.QuotientDuality

module

public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Convex.Topology

/-! # Cochains for logarithmic lifting

Unbundled integral cochains and their alternating differentials. Values outside the stated
supports are immaterial. These are data types and formulas, not geometric assumptions.
HC no distance; AV milestone no distance.
-/

@[expose] public section

noncomputable section
open CategoryTheory Set
open scoped Simplicial BigOperators
namespace HodgeLean.Foundations

/-- A singular simplex with values in affine complex space.
Source: Hatcher, *Algebraic Topology*, §2.1, singular chains. -/
abbrev cech_simplex (n q : ℕ) := C(SimplexCategory.toTop₀.obj ⦋q⦌, Fin n → ℂ)

example : cech_simplex 0 0 := ContinuousMap.const _ 0

/-- Restriction to a singular face, in the standard vertex order.
Source: Hatcher, *Algebraic Topology*, §2.1, the singular boundary formula. -/
def cech_face (n q : ℕ) (i : Fin (q + 2)) (σ : cech_simplex n (q + 1)) :
    cech_simplex n q :=
  σ.comp (SimplexCategory.toTop₀.map (SimplexCategory.δ i)).hom

example (n q : ℕ) (i : Fin (q + 2)) :
    cech_face n q i (ContinuousMap.const _ (0 : Fin n → ℂ)) =
      ContinuousMap.const _ 0 := rfl

/-- The integral singular coboundary on unbundled cochains.
Source: Hatcher, *Algebraic Topology*, §3.1, dual singular complex. -/
def cech_d (n q : ℕ) (f : cech_simplex n q → ℤ) : cech_simplex n (q + 1) → ℤ :=
  fun σ ↦ ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val * f (cech_face n q i σ)

example (n q : ℕ) : cech_d n q (fun _ ↦ 0) = fun _ ↦ 0 := by
  funext σ
  simp [cech_d]

/-- The integral Čech differential on ordered tuples, including repeated indices.
Source: Bott--Tu, *Differential Forms in Algebraic Topology*, §8, the Čech complex. -/
def cech_h (n p : ℕ) {A : Type} (f : (Fin (p + 1) → (Fin n → ℂ)) → A → ℤ) :
    (Fin (p + 2) → (Fin n → ℂ)) → A → ℤ :=
  fun t x ↦ ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val * f (t ∘ i.succAbove) x

example (n p : ℕ) :
    cech_h n p (A := Unit) (fun _ _ ↦ 0) = fun _ _ ↦ 0 := by
  funext t x
  simp [cech_h]

/-- Subtract an integral period from a chosen overlap logarithm.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, VIII,
exponential sequence, with period `2πi`. -/
def cech_correct (n : ℕ)
    (b : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (k : (Fin n → ℂ) → (Fin n → ℂ) → ℤ) :
    (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ :=
  fun p q z ↦ b p q z - (2 * Real.pi * Complex.I) * (k p q : ℂ)

example (n : ℕ) : cech_correct n (fun _ _ _ ↦ 0) (fun _ _ ↦ 0) = fun _ _ _ ↦ 0 := by
  funext p q z
  simp [cech_correct]

end HodgeLean.Foundations

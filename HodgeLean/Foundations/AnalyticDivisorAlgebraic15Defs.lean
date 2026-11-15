import HodgeLean.Foundations.AnalyticDivisorAlgebraic14

/-! # Equivalent local equations and meromorphic divisor data

This file adds the data-level relations needed to compare two local presentations of a divisor
and to represent a meromorphic divisor by numerator-denominator pairs.  HC no distance; AV
milestone no distance.
-/

noncomputable section
open Filter Set Topology
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic15

open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic8
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14

/-- Two families of local equations are equivalent when their equations are associated at every
point of every cross-overlap.  The condition contains only presentation data.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1 (divisors). -/
def EquivalentLocalDivisorData {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι κ : Type*} (V : ι → Set E) (f : ι → E → ℂ)
    (W : κ → Set E) (g : κ → E → ℂ) : Prop :=
  ∀ i j, ∀ x ∈ V i ∩ W j, AreAssociatedAt (f i) (g j) x

/-- Local numerator-denominator presentations of a meromorphic divisor.  On an overlap, equality
of quotients is recorded without division by associating the two cross-products.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1 (meromorphic divisors);
Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
def IsLocalMeromorphicDivisorData {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (U : Set E) (V : ι → Set E) (g h : ι → E → ℂ) : Prop :=
  (∀ i, IsOpen (V i)) ∧ (⋃ i, V i) = U ∧
    (∀ i, AnalyticOnNhd ℂ (g i) (V i)) ∧ (∀ i, AnalyticOnNhd ℂ (h i) (V i)) ∧
    (∀ i, ∀ x ∈ V i, ¬ ∀ᶠ y in 𝓝 x, g i y = 0) ∧
    (∀ i, ∀ x ∈ V i, ¬ ∀ᶠ y in 𝓝 x, h i y = 0) ∧
    ∀ i j, ∀ x ∈ V i ∩ V j,
      AreAssociatedAt (fun y ↦ g i y * h j y) (fun y ↦ g j y * h i y) x

/-- Equivalence of two numerator-denominator presentations, expressed by cross-multiplication on
every cross-overlap.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
def EquivalentLocalMeromorphicDivisorData {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι κ : Type*} (V : ι → Set E) (g h : ι → E → ℂ)
    (W : κ → Set E) (a b : κ → E → ℂ) : Prop :=
  ∀ i j, ∀ x ∈ V i ∩ W j,
    AreAssociatedAt (fun y ↦ g i y * b j y) (fun y ↦ a j y * h i y) x

/-- The integer multiplicity function of a numerator-denominator pair at a point.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
def localMeromorphicDivisorAt (n : ℕ) (g h : (Fin n → ℂ) × ℂ → ℂ)
    (p : (Fin n → ℂ) × ℂ) : LocalFactorClass n →₀ ℤ :=
  (localDivisorAt n g p).mapRange Nat.cast (by simp) -
    (localDivisorAt n h p).mapRange Nat.cast (by simp)

end HodgeLean.Foundations.AnalyticDivisorAlgebraic15

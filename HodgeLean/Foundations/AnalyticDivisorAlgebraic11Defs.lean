import HodgeLean.Foundations.AnalyticDivisorAlgebraic10

/-! # Definitions for nearby-point translation of analytic germs

This file supplies only the nearby-point germ ring and elementary notation used by the stage
eleven frozen statements. Translation equivalences and their properties are theorems, not
definitions. HC no distance; AV milestone no distance.
-/

noncomputable section
open Filter Polynomial Topology
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic11

/-- Germs at `p ∈ ℂⁿ` which have a representative analytic at `p`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
def analyticGermAtSubring (n : ℕ) (p : Fin n → ℂ) :
    Subring (Filter.Germ (nhds p) ℂ) where
  carrier := {g | ∃ f : (Fin n → ℂ) → ℂ, AnalyticAt ℂ f p ∧
    (@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) f) = g}
  zero_mem' := ⟨fun _ ↦ 0, analyticAt_const, rfl⟩
  one_mem' := ⟨fun _ ↦ 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun x ↦ f x + g x, hf.add hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨fun x ↦ -f x, hf.neg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun x ↦ f x * g x, hf.mul hg, rfl⟩

example (n : ℕ) (p : Fin n → ℂ) :
    (0 : Filter.Germ (nhds p) ℂ) ∈ analyticGermAtSubring n p :=
  (analyticGermAtSubring n p).zero_mem

/-- The local ring of analytic function germs at `p ∈ ℂⁿ`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
abbrev AnalyticGermAt (n : ℕ) (p : Fin n → ℂ) := analyticGermAtSubring n p

example (n : ℕ) (p : Fin n → ℂ) : Nonempty (AnalyticGermAt n p) := ⟨0⟩

/-- Evaluation at the base point on analytic germs at `p`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
def analyticGermAtValue (n : ℕ) (p : Fin n → ℂ) : AnalyticGermAt n p →+* ℂ :=
  (Filter.Germ.valueRingHom (X := Fin n → ℂ) (E := ℂ)).comp
    (analyticGermAtSubring n p).subtype

example (n : ℕ) (p : Fin n → ℂ) : analyticGermAtValue n p 0 = 0 := by simp

/-- A monic positive-degree polynomial over germs at `p` whose nonleading coefficients vanish
at `p`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 2. -/
def IsWeierstrassPolynomialAt {n : ℕ} {p : Fin n → ℂ}
    (P : Polynomial (AnalyticGermAt n p)) : Prop :=
  P.Monic ∧ 0 < P.natDegree ∧
    ∀ j < P.natDegree, analyticGermAtValue n p (P.coeff j) = 0

example {n : ℕ} {p : Fin n → ℂ} :
    IsWeierstrassPolynomialAt (X : Polynomial (AnalyticGermAt n p)) := by
  constructor
  · exact monic_X
  · simp [IsWeierstrassPolynomialAt]

/-- The germ at `p ∈ ℂ¹` of the coordinate function.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
def gaga11_coordinateGermAt (p : Fin 1 → ℂ) : AnalyticGermAt 1 p :=
  ⟨@Filter.Germ.ofFun (Fin 1 → ℂ) ℂ (nhds p) (fun z ↦ z 0),
    ⟨fun z ↦ z 0,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt p, rfl⟩⟩

example (p : Fin 1 → ℂ) : analyticGermAtValue 1 p (gaga11_coordinateGermAt p) = p 0 := by
  change (@Filter.Germ.ofFun (Fin 1 → ℂ) ℂ (nhds p) (fun z ↦ z 0)).value = p 0
  simpa using (Filter.Germ.value_ofFun (fun z : Fin 1 → ℂ ↦ z 0) p)

/-- The neighbourhood of zero obtained by translating a set by `p`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
def gaga11_translatedSet {n : ℕ} (p : Fin n → ℂ) (U : Set (Fin n → ℂ)) :
    Set (Fin n → ℂ) := {z | p + z ∈ U}

example {n : ℕ} (p : Fin n → ℂ) :
    gaga11_translatedSet p Set.univ = Set.univ := by
  ext z
  simp [gaga11_translatedSet]

end HodgeLean.Foundations.AnalyticDivisorAlgebraic11

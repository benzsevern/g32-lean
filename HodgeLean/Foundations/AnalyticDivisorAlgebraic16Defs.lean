import HodgeLean.Foundations.AnalyticDivisorAlgebraic14

/-! # Irreducible components of analytic divisor support: definitions

This file gives set-theoretic names for local factor zero sets, the clean part of a divisor
support, and relative closures of its connected components.  Components are indexed by clean
points, so no point outside the clean locus contributes an empty component.

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic16

open Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14

/-- The part of a local irreducible factor's zero set which lies in a chart and in the support.
Source: Chirka, *Complex Analytic Sets*, §5.1 (local irreducible components). -/
def gaga16_localComponent {n : ℕ} {ι : Type*}
    (V : ι → Set ((Fin n → ℂ) × ℂ)) (f : ι → (Fin n → ℂ) × ℂ → ℂ)
    (i : ι) (P : (Fin n → ℂ) × ℂ → ℂ) : Set ((Fin n → ℂ) × ℂ) :=
  V i ∩ localDivisorSupport V f ∩ {x | P x = 0}

example {n : ℕ} {V : Unit → Set ((Fin n → ℂ) × ℂ)}
    {f P : (Fin n → ℂ) × ℂ → ℂ} :
    gaga16_localComponent V (fun _ ↦ f) () P =
      V () ∩ localDivisorSupport V (fun _ ↦ f) ∩ {x | P x = 0} := rfl

/-- The clean part of the support: locally it is the zero set of one irreducible factor, with
positive multiplicity and nonzero derivative at the point.
Source: Chirka, *Complex Analytic Sets*, §5.1 (regular points of irreducible components). -/
def gaga16_cleanSupport {n : ℕ} {ι : Type*}
    (V : ι → Set ((Fin n → ℂ) × ℂ)) (f : ι → (Fin n → ℂ) × ℂ → ℂ) :
    Set ((Fin n → ℂ) × ℂ) :=
  {x | ∃ (i : ι) (P u : (Fin n → ℂ) × ℂ → ℂ) (m : ℕ),
    x ∈ V i ∧ AnalyticAt ℂ P x ∧ IsIrreducibleAt P x ∧ AnalyticAt ℂ u x ∧
      u x ≠ 0 ∧ 0 < m ∧ (f i =ᶠ[nhds x] fun y ↦ u y * (P y) ^ m) ∧
      P x = 0 ∧ fderiv ℂ P x ≠ 0}

example {n : ℕ} {ι : Type*} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} :
    gaga16_cleanSupport V f =
      {x | ∃ (i : ι) (P u : (Fin n → ℂ) × ℂ → ℂ) (m : ℕ),
        x ∈ V i ∧ AnalyticAt ℂ P x ∧ IsIrreducibleAt P x ∧ AnalyticAt ℂ u x ∧
          u x ≠ 0 ∧ 0 < m ∧ (f i =ᶠ[nhds x] fun y ↦ u y * P y ^ m) ∧
          P x = 0 ∧ fderiv ℂ P x ≠ 0} := rfl

/-- The candidate component through a clean point is the ambient closure of its connected
component, intersected with `U`; this is closure relative to `U`.
Source: Chirka, *Complex Analytic Sets*, §5.2 (global irreducible components). -/
def gaga16_componentThrough {E : Type*} [TopologicalSpace E]
    (U C : Set E) (x : E) : Set E :=
  U ∩ closure (connectedComponentIn C x)

example {E : Type*} [TopologicalSpace E] (U C : Set E) (x : E) :
    gaga16_componentThrough U C x = U ∩ closure (connectedComponentIn C x) := rfl

/-- Candidate global components indexed by points of the clean locus.
Source: Chirka, *Complex Analytic Sets*, §5.2 (components from regular points). -/
def gaga16_componentIndex {E : Type*} [TopologicalSpace E] (U C : Set E) :=
  Set.range (fun x : C ↦ gaga16_componentThrough U C x)

example {E : Type*} [TopologicalSpace E] (U C : Set E) :
    gaga16_componentIndex U C = Set.range (fun x : C ↦ gaga16_componentThrough U C x) := rfl

/-- The set represented by a candidate-component index.
Source: Chirka, *Complex Analytic Sets*, §5.2 (global irreducible components). -/
def gaga16_component {E : Type*} [TopologicalSpace E] (U C : Set E)
    (Z : gaga16_componentIndex U C) : Set E :=
  Z.1

example {E : Type*} [TopologicalSpace E] (U C : Set E) (Z : gaga16_componentIndex U C) :
    gaga16_component U C Z = Z.1 := rfl

end HodgeLean.Foundations.AnalyticDivisorAlgebraic16

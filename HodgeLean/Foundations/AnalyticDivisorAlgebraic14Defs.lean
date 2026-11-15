import HodgeLean.Foundations.AnalyticDivisorAlgebraic13

/-! # Definitions for local divisor data on an open set

This file supplies explicit-cover local divisor data, its support, and the stage-eight local
divisor read at an arbitrary point after translation to the origin. Compatibility of
multiplicities, closedness of the support, refinement and clean-locus density remain theorems.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Filter Set Topology
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic14

open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic8

/-- Local divisor data on `U`: open charts `V i` whose union is `U`, and on each chart a local
equation `f i` analytic on `V i` and not identically zero near any point of `V i`, such that at
every point of an overlap `V i ∩ V j` the two equations are associated by an analytic germ
which does not vanish at that point.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1 (divisors);
Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
def IsLocalDivisorData {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (U : Set E) (V : ι → Set E) (f : ι → E → ℂ) : Prop :=
  (∀ i, IsOpen (V i)) ∧ (⋃ i, V i) = U ∧ (∀ i, AnalyticOnNhd ℂ (f i) (V i)) ∧
    (∀ i, ∀ x ∈ V i, ¬ ∀ᶠ y in 𝓝 x, f i y = 0) ∧
    ∀ i j, ∀ x ∈ V i ∩ V j, AreAssociatedAt (f i) (f j) x

-- The constant equation `1` on the whole line is local divisor data with one chart.
example : IsLocalDivisorData (univ : Set ℂ) (fun _ : Unit ↦ univ) (fun _ _ ↦ (1 : ℂ)) := by
  refine ⟨fun _ ↦ isOpen_univ, iUnion_const _, fun _ ↦ analyticOnNhd_const, ?_, ?_⟩
  · intro _ x _ h
    exact one_ne_zero h.self_of_nhds
  · intro _ _ x _
    exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun _ ↦ by simp⟩

/-- The support of local divisor data: the points of some chart at which its local equation
vanishes.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
def localDivisorSupport {E : Type*} {ι : Type*} (V : ι → Set E) (f : ι → E → ℂ) : Set E :=
  {x | ∃ i, x ∈ V i ∧ f i x = 0}

example : localDivisorSupport (fun _ : Unit ↦ (univ : Set ℂ)) (fun _ z ↦ z) = {0} := by
  ext z
  simp [localDivisorSupport]

/-- The stage-eight local divisor of `f` at `p`, computed from the translated function
`y ↦ f (p + y)` at the origin. A function whose translate is not analytic at the origin is
assigned the zero function; statements below carry analyticity explicitly.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1; Gunning--Rossi, II.B,
Definition 1. -/
def localDivisorAt (n : ℕ) (f : (Fin n → ℂ) × ℂ → ℂ) (p : (Fin n → ℂ) × ℂ) :
    LocalFactorClass n →₀ ℕ := by
  classical
  exact if h : AnalyticAt ℂ (fun y ↦ f (p + y)) 0 then
    localDivisor n (productAnalyticGermOf (fun y ↦ f (p + y)) h) else 0

-- At the origin the translated divisor is the stage-eight local divisor.
example {n : ℕ} (f : (Fin n → ℂ) × ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    localDivisorAt n f 0 = localDivisor n (productAnalyticGermOf f hf) := by
  have h : AnalyticAt ℂ (fun y ↦ f (0 + y)) 0 := by simpa using hf
  simp only [localDivisorAt, h, ↓reduceDIte]
  congr 2
  · simp

end HodgeLean.Foundations.AnalyticDivisorAlgebraic14

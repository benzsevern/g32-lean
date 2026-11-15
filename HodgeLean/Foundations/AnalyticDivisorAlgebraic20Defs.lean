import HodgeLean.Foundations.AnalyticDivisorAlgebraic19

/-! # Analytic divisor gluing: definitions

This file records the regular hypersurface locus and the topological carrier data for a future glued
analytic divisor.  It does not choose global components from local factor data.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic20

open Set

/-- The regular part of the zero set, expressed by the hypersurface Jacobian criterion.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, III.A, Theorem 4. -/
def gaga20_regularZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) : Set E :=
  {x | f x = 0 ∧ fderiv ℂ f x ≠ 0}

/-- A nonempty closed preirreducible topological carrier; no analyticity is asserted.
Source: Chirka, *Complex Analytic Sets*, §5.1. -/
structure gaga20_TopologicalComponent (E : Type*) [TopologicalSpace E] where
  carrier : Set E
  closed' : IsClosed carrier
  nonempty' : carrier.Nonempty
  irreducible' : IsPreirreducible carrier

/-- A locally finite weighted topological family; this is not an analytic divisor.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
structure gaga20_WeightedTopologicalFamily (E : Type*) [TopologicalSpace E] (U : Set E) where
  Component : Type
  component : Component → gaga20_TopologicalComponent E
  multiplicity : Component → ℕ
  multiplicity_pos : ∀ a, 0 < multiplicity a
  component_subset : ∀ a, (component a).carrier ⊆ U
  locallyFinite : LocallyFinite fun a ↦
    ((↑) : U → E) ⁻¹' (component a).carrier

/-- Carrier intersection, retaining the same component index; this does not construct a divisor
restriction or decompose the intersected carriers.
Source: Bourbaki, *General Topology*, Ch. I, §1 (intersection of subsets). -/
def gaga20_WeightedTopologicalFamily.carrierIntersection {E : Type*} [TopologicalSpace E] {U : Set E}
    (D : gaga20_WeightedTopologicalFamily E U) (W : Set E) : D.Component → Set E :=
  fun a ↦ (D.component a).carrier ∩ W

example : gaga20_regularZero (fun z : ℂ ↦ z) = {0} := by
  ext z
  simp only [gaga20_regularZero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · exact fun h ↦ h.1
  · intro hz
    refine ⟨hz, ?_⟩
    intro h
    have h1 := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1) h
    simp at h1

end HodgeLean.Foundations.AnalyticDivisorAlgebraic20

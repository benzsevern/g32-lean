import HodgeLean.Foundations.AnalyticDivisorAlgebraic16Proofs

/-! # Irreducible components of analytic divisor support: frozen specification

This stage freezes only the implication from a local irreducible factorization to the local
support description.  It also names candidate components using closure relative to the open set,
indexed by clean points.  It does not claim the global component, local-finiteness, connectedness,
or multiplicity results deferred to later stages.

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic16

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14

/-- A factor in a local irreducible decomposition defines its local support component.
Source: Chirka, *Complex Analytic Sets*, §2. -/
theorem spec_local_factor_component {n k : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i)
    {u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    (hu : AnalyticAt ℂ u p) (hu0 : u p ≠ 0)
    (hP : ∀ j, AnalyticAt ℂ (P j) p ∧ IsIrreducibleAt (P j) p ∧ 0 < m j)
    (hfac : f i =ᶠ[nhds p] fun y ↦ u y * ∏ j, (P j y) ^ (m j)) (j : Fin k) :
    (∀ᶠ y in nhds p, y ∈ gaga16_localComponent V f i (P j) ↔ y ∈ V i ∧ P j y = 0) ∧
      ∀ᶠ y in nhds p,
        y ∈ V i → (y ∈ localDivisorSupport V f ↔ ∃ l : Fin k, P l y = 0) :=
  spec_local_factor_component_aux hD i p hi hu hu0 hP hfac j

/-! ### Degenerate checks -/

example {E : Type*} [TopologicalSpace E] (U : Set E) :
    gaga16_componentIndex U (∅ : Set E) = ∅ := by
  simp [gaga16_componentIndex]

example {n : ℕ} {U V : Set ((Fin n → ℂ) × ℂ)}
    (hD : IsLocalDivisorData U (fun _ : Unit ↦ V) (fun _ y ↦ y.2))
    (p : (Fin n → ℂ) × ℂ) (hp : p ∈ V)
    (hP : AnalyticAt ℂ (fun y : (Fin n → ℂ) × ℂ ↦ y.2) p ∧
      IsIrreducibleAt (fun y : (Fin n → ℂ) × ℂ ↦ y.2) p) :
    ∀ᶠ y in nhds p,
      y ∈ gaga16_localComponent (fun _ : Unit ↦ V) (fun _ y ↦ y.2) () (fun y ↦ y.2) ↔
        y ∈ V ∧ y.2 = 0 := by
  have h := spec_local_factor_component (k := 1) hD () p hp
    (u := fun _ ↦ 1) (P := fun _ y ↦ y.2) (m := fun _ ↦ 1)
    analyticAt_const one_ne_zero (fun _ ↦ ⟨hP.1, hP.2, by omega⟩)
    (by simp) 0
  exact h.1

example {U V : Set ((Fin 1 → ℂ) × ℂ)}
    (P : Fin 2 → (Fin 1 → ℂ) × ℂ → ℂ)
    (hP0 : P 0 = fun y ↦ y.1 0) (hP1 : P 1 = fun y ↦ y.2)
    (hD : IsLocalDivisorData U (fun _ : Unit ↦ V) (fun _ y ↦ y.1 0 * y.2))
    (p : (Fin 1 → ℂ) × ℂ) (hp : p ∈ V)
    (hP : ∀ j, AnalyticAt ℂ (P j) p ∧ IsIrreducibleAt (P j) p) :
    ∀ᶠ y in nhds p,
      y ∈ V → (y ∈ localDivisorSupport (fun _ : Unit ↦ V)
        (fun _ y ↦ y.1 0 * y.2) ↔ ∃ j : Fin 2, P j y = 0) := by
  have h := spec_local_factor_component hD () p hp
    (u := fun _ ↦ 1) (P := P) (m := fun _ ↦ 1)
    analyticAt_const one_ne_zero (fun j ↦ ⟨(hP j).1, (hP j).2, by omega⟩)
    (by filter_upwards with y; rw [Fin.prod_univ_two, hP0, hP1]; simp) 0
  exact h.2

example {n : ℕ} {U V : Set ((Fin n → ℂ) × ℂ)}
    (hD : IsLocalDivisorData U (fun _ : Unit ↦ V) (fun _ y ↦ y.2 ^ 2))
    (p : (Fin n → ℂ) × ℂ) (hp : p ∈ V)
    (hP : AnalyticAt ℂ (fun y : (Fin n → ℂ) × ℂ ↦ y.2) p ∧
      IsIrreducibleAt (fun y : (Fin n → ℂ) × ℂ ↦ y.2) p) :
    ∀ᶠ y in nhds p,
      y ∈ gaga16_localComponent (fun _ : Unit ↦ V) (fun _ y ↦ y.2 ^ 2) ()
        (fun y ↦ y.2) ↔ y ∈ V ∧ y.2 = 0 := by
  have h := spec_local_factor_component (k := 1) hD () p hp
    (u := fun _ ↦ 1) (P := fun _ y ↦ y.2) (m := fun _ ↦ 2)
    analyticAt_const one_ne_zero (fun _ ↦ ⟨hP.1, hP.2, by omega⟩)
    (by simp) 0
  exact h.1

example (V : Set ((Fin 0 → ℂ) × ℂ))
    (f : Unit → (Fin 0 → ℂ) × ℂ → ℂ) :
    gaga16_localComponent (fun _ : Unit ↦ V) f () (fun y ↦ y.2) =
      V ∩ localDivisorSupport (fun _ : Unit ↦ V) f ∩ {y | y.2 = 0} := rfl

example (U C : Set ((Fin 1 → ℂ) × ℂ)) (x : (Fin 1 → ℂ) × ℂ) :
    gaga16_componentThrough U C x = U ∩ closure (connectedComponentIn C x) := rfl

example :
    IsOpen ({0, 2} : Set (Fin 3)) ∧
      Disjoint ({0} : Set (Fin 3)) {2} ∧
      ({0} : Set (Fin 3)) ∪ {2} = {0, 2} ∧
      gaga16_componentThrough ({0, 2} : Set (Fin 3)) ({0, 2} : Set (Fin 3)) 0 ⊆ {0, 2} ∧
      gaga16_componentThrough ({0, 2} : Set (Fin 3)) ({0, 2} : Set (Fin 3)) 2 ⊆ {0, 2} := by
  refine ⟨isOpen_discrete _, by simp, by ext x; fin_cases x <;> simp, ?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro x hx
    exact hx.1

end HodgeLean.Foundations.AnalyticDivisorAlgebraic16

import HodgeLean.Foundations.Program.SchoenTransferR2LocalDeformation
import HodgeLean.Foundations.Program.SchoenTransferR2FiniteDeformation
import Mathlib.Analysis.Complex.Basic

/-! # Neighbourhood deformation for a compact subset with flat complex charts

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Compactness combines local normal-chart contractions into an ambient map
homotopic to the identity and taking a neighbourhood into the actual support.
Source: Hatcher, Algebraic Topology, §0; local normal charts and compactness.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_compact_flat_deformation
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (S : Set X) (hS : IsCompact S)
    (hcharts : ∀ x ∈ S, ∃ r c : ℕ,
      ∃ e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin c → ℂ)),
        x ∈ e.source ∧ ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) :
    ∃ (F : C(X, X)), Nonempty (ContinuousMap.Homotopy (ContinuousMap.id X) F) ∧
      (∀ x ∈ S, F x = x) ∧ ∃ V : Opens X, S ⊆ V ∧ Set.MapsTo F V S := by
  classical
  have hlocal (x : S) : ∃ (U : Opens X), x.val ∈ U ∧ ∃ f : C(X, X),
      Nonempty (ContinuousMap.Homotopy (ContinuousMap.id X) f) ∧
        (∀ y ∈ S, f y = y) ∧ Set.MapsTo f U S := by
    obtain ⟨r, c, e, hxe, hflat⟩ := hcharts x.val x.property
    exact s4_assembly_local_flat_deformation S e hflat x.val x.property hxe
  choose U hxU f H hfix hinto using hlocal
  apply s4_assembly_compact_deformation S hS f (fun x => Classical.choice (H x)) hfix U hinto
  intro x hx
  exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩

#print axioms s4_assembly_compact_flat_deformation
end HodgeLean.Foundations.Program

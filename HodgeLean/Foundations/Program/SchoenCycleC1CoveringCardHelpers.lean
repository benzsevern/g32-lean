import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! # Fibre cardinality on a connected covering base -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Fibre cardinality of a surjective covering is constant on a preconnected base. -/
theorem s2e_c1_covering_fibre_card_eq {E B : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [PreconnectedSpace B]
    (f : E → B) (hf : IsCoveringMap f) (hs : Function.Surjective f) (x y : B) :
    Nat.card (f ⁻¹' {x}) = Nat.card (f ⁻¹' {y}) := by
  have hloc : IsLocallyConstant (fun b : B => Nat.card (f ⁻¹' {b})) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro b
    obtain ⟨z, hz⟩ := hs b
    haveI : Nonempty (f ⁻¹' {b}) := ⟨⟨z, hz⟩⟩
    let t := (hf b).toTrivialization
    refine ⟨t.baseSet, t.open_baseSet, (hf b).mem_toTrivialization_baseSet, ?_⟩
    intro c hc
    exact Nat.card_congr (t.preimageSingletonHomeomorph hc).toEquiv
  exact hloc.apply_eq_of_preconnectedSpace x y

end HodgeLean.Foundations.Program

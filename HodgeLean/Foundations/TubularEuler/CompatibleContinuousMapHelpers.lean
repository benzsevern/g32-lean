import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens

/-! # Continuous maps retained on an open union

Exact overlap agreement retains the supplied maps under continuous gluing.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology TopologicalSpace
namespace HodgeLean.Foundations.TubularEuler

theorem compatible_continuousOn_maps_union
    {I X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (U : I → Opens X) (f : I → X → Y) (hf : ∀ i, ContinuousOn (f i) (U i))
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → f i x = f j x) :
    ∃ m : C((⟨⋃ i, (U i : Set X), isOpen_iUnion (fun i => (U i).isOpen)⟩ : Opens X), Y),
      ∀ i x (hx : x ∈ U i), m ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩⟩ = f i x := by
  let O : Opens X := ⟨⋃ i, (U i : Set X), isOpen_iUnion (fun i => (U i).isOpen)⟩
  let S : I → Set O := fun i => Subtype.val ⁻¹' (U i : Set X)
  let g : ∀ i, C(S i, Y) := fun i =>
    ⟨fun x => f i x.val.val,
      (hf i).comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
        (fun x => x.property)⟩
  have hg : ∀ i j (x : O) (hi : x ∈ S i) (hj : x ∈ S j), g i ⟨x, hi⟩ = g j ⟨x, hj⟩ := by
    intro i j x hi hj
    exact hcompat i j x.val hi hj
  have hS : ∀ x : O, ∃ i, S i ∈ nhds x := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp x.property
    exact ⟨i, ((U i).isOpen.preimage continuous_subtype_val).mem_nhds hi⟩
  refine ⟨ContinuousMap.liftCover S g hg hS, ?_⟩
  intro i x hx
  exact ContinuousMap.liftCover_coe (S := S) (φ := g) (hφ := hg) (hS := hS)
    (i := i) (⟨⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩⟩, hx⟩ : S i)

#print axioms compatible_continuousOn_maps_union

end HodgeLean.Foundations.TubularEuler

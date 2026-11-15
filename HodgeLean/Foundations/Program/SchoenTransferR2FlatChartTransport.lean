import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! # Flat charts transported through open embeddings

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.Program

/-- An open embedding transports a flat chart, with its actual support predicate.
Source: Munkres, Topology, §18, subspace topology and composition.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_flat_chart_open_transport
    {X Y E F : Type*} [TopologicalSpace X] [Nonempty X] [TopologicalSpace Y]
    [TopologicalSpace E] [TopologicalSpace F] [Zero F]
    (f : X → Y) (hf : IsOpenEmbedding f) (S : Set Y)
    (e : OpenPartialHomeomorph X (E × F))
    (hflat : ∀ x ∈ e.source, f x ∈ S ↔ (e x).2 = 0) :
    ∃ d : OpenPartialHomeomorph Y (E × F),
      d.source = f '' e.source ∧ (∀ x, d (f x) = e x) ∧
        ∀ y ∈ d.source, y ∈ S ↔ (d y).2 = 0 := by
  let a := hf.toOpenPartialHomeomorph f
  let d := a.symm.trans e
  have hval (x : X) : d (f x) = e x := by
    change e (a.symm (f x)) = e x
    rw [hf.toOpenPartialHomeomorph_left_inv f]
  have hsource : d.source = f '' e.source := by
    ext y
    change (y ∈ a.target ∧ a.symm y ∈ e.source) ↔ _
    rw [show a.target = Set.range f from hf.toOpenPartialHomeomorph_target f]
    constructor
    · intro hy
      exact ⟨a.symm y, hy.2, hf.toOpenPartialHomeomorph_right_inv f hy.1⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, rfl⟩, ?_⟩
      simpa only [a, hf.toOpenPartialHomeomorph_left_inv f] using hx
  refine ⟨d, hsource, hval, ?_⟩
  intro y hy
  rw [hsource] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [hval]
  exact hflat x hx

#print axioms s4_assembly_flat_chart_open_transport
end HodgeLean.Foundations.Program

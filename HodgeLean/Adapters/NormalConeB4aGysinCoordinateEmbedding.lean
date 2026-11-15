import Mathlib.Geometry.Manifold.ChartedSpace

noncomputable section
namespace HodgeLean.Adapters

/-- Expressing an embedding in source and target partial coordinates preserves
its embedding property on the domain where both coordinates are defined. -/
theorem a3b4a_gysin_coordinate_embedding
    {X Y E F : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace E] [TopologicalSpace F]
    (f : X → Y) (hf : Topology.IsEmbedding f)
    (e : OpenPartialHomeomorph X E) (Φ : OpenPartialHomeomorph Y F) :
    Topology.IsEmbedding (fun a : {a : E | a ∈ e.target ∧ f (e.symm a) ∈ Φ.source} =>
      Φ (f (e.symm a))) := by
  let Ω : Set E := e.target ∩ e.symm ⁻¹' (f ⁻¹' Φ.source)
  have hi : Topology.IsEmbedding (Set.inclusion (show Ω ⊆ e.target from fun _ ha => ha.1)) :=
    Topology.IsEmbedding.inclusion _
  have hb : Topology.IsEmbedding (fun a : Ω => f (e.symm a)) :=
    hf.comp (e.symm.isEmbedding_restrict.comp hi)
  exact Φ.isEmbedding_restrict.comp
    (hb.codRestrict Φ.source (fun a => a.2.2))

end HodgeLean.Adapters

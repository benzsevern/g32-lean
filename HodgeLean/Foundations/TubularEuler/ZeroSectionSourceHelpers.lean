import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! # Restricting inverse sources along the zero projection

Every point in the restricted source retains the zero vector over its base point.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.TubularEuler

def zeroSectionSourceRestriction
    {B N X : Type*} [TopologicalSpace B] [TopologicalSpace N] [Zero N]
    [TopologicalSpace X] (L : OpenPartialHomeomorph (B × N) X) :
    OpenPartialHomeomorph (B × N) X :=
  L.restrOpen (L.source ∩ (fun z : B × N => (z.1, (0 : N))) ⁻¹' L.source)
    (L.open_source.inter (L.open_source.preimage (continuous_fst.prodMk continuous_const)))

theorem zeroSectionSourceRestriction_source_zero
    {B N X : Type*} [TopologicalSpace B] [TopologicalSpace N] [Zero N]
    [TopologicalSpace X] (L : OpenPartialHomeomorph (B × N) X)
    (z : B × N) (hz : z ∈ (zeroSectionSourceRestriction L).source) :
    (z.1, (0 : N)) ∈ (zeroSectionSourceRestriction L).source := by
  exact ⟨hz.2.2, hz.2.2, hz.2.2⟩

#print axioms zeroSectionSourceRestriction
#print axioms zeroSectionSourceRestriction_source_zero

end HodgeLean.Foundations.TubularEuler

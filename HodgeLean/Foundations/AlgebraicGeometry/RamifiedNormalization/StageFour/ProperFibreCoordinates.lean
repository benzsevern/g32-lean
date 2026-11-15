import Mathlib.Topology.Maps.Proper.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Bijective continuous coordinates over a proper base projection retain the full topology. -/
def properFibreCoordinateHomeomorph
    {X Y B : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
    [T2Space Y] (f : X → Y) (p : X → B) (q : Y → B)
    (hf : Continuous f) (hq : Continuous q) (hp : IsProperMap p)
    (hpq : ∀ x, q (f x) = p x) (hbij : Function.Bijective f) : X ≃ₜ Y := by
  have hcomp : q ∘ f = p := funext hpq
  have hproper : IsProperMap f := isProperMap_of_comp_of_t2 hf hq (hcomp ▸ hp)
  exact (isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨hf, hproper.isClosedMap, hbij⟩).homeomorph f

end AlgebraicGeometry.RamifiedNormalization.StageFour

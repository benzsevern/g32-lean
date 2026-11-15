import HodgeLean.Foundations.TubularEuler.PartialHomeomorphRestrictionHelpers

/-! # Transporting coordinate inverses through actual charts

The transported map has the same coordinate source and coordinate values as the supplied inverse.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.TubularEuler

theorem partialHomeomorph_transported_coordinates
    {X Y Z T : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace T]
    (P : OpenPartialHomeomorph X Z) (a : OpenPartialHomeomorph Y T)
    (c : OpenPartialHomeomorph Z T)
    (hP : c.source ⊆ P.target) (ha : c.target ⊆ a.target) :
    let L := (P.trans c).trans a.symm
    let C := (P.symm.trans L).trans a
    C.source = c.source ∧ Set.EqOn C c c.source := by
  let L := (P.trans c).trans a.symm
  let C := (P.symm.trans L).trans a
  constructor
  · apply Set.Subset.antisymm
    · intro w hw
      have hc : P (P.symm w) ∈ c.source := hw.1.2.1.2
      rw [P.right_inv hw.1.1] at hc
      exact hc
    · intro w hw
      have hwP : w ∈ P.target := hP hw
      have hzL : P.symm w ∈ L.source := by
        refine ⟨⟨P.map_target hwP, ?_⟩, ?_⟩
        · change P (P.symm w) ∈ c.source
          rw [P.right_inv hwP]
          exact hw
        · change c (P (P.symm w)) ∈ a.target
          rw [P.right_inv hwP]
          exact ha (c.map_source hw)
      have hza : L (P.symm w) ∈ a.source := by
        change a.symm (c (P (P.symm w))) ∈ a.source
        rw [P.right_inv hwP]
        exact a.map_target (ha (c.map_source hw))
      exact ⟨⟨hwP, hzL⟩, hza⟩
  · intro w hw
    change a (a.symm (c (P (P.symm w)))) = c w
    rw [P.right_inv (hP hw), a.right_inv (ha (c.map_source hw))]

#print axioms partialHomeomorph_transported_coordinates

end HodgeLean.Foundations.TubularEuler

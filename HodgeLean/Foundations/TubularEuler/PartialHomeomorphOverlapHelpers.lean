import HodgeLean.Foundations.TubularEuler.PartialHomeomorphRestrictionHelpers

/-! # Ambient chart restriction to the image of a shared source

Injectivity of the retained ambient map identifies its local preimages.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology TopologicalSpace
namespace HodgeLean.Foundations.TubularEuler

def partialHomeomorphOverlap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A L : OpenPartialHomeomorph X Y) : Opens Y :=
  ⟨L '' (L.source ∩ A.source), L.isOpen_image_of_subset_source
    (L.open_source.inter A.open_source) Set.inter_subset_left⟩

theorem partialHomeomorph_overlap_pullback {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A L : OpenPartialHomeomorph X Y)
    (he : Set.EqOn A L (A.source ∩ L.source))
    (z : X) (hz : z ∈ A.source) (hH : A z ∈ partialHomeomorphOverlap A L) :
    z ∈ L.source ∧ A z = L z := by
  obtain ⟨w, ⟨hwL, hwA⟩, hw⟩ := hH
  have hwz : w = z := A.injOn hwA hz ((he ⟨hwA, hwL⟩).trans hw)
  subst w
  exact ⟨hwL, he ⟨hz, hwL⟩⟩

theorem partialHomeomorph_restricted_coordinates {X Y Z T : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]
    (P : OpenPartialHomeomorph X Z) (A L : OpenPartialHomeomorph X Y)
    (a : OpenPartialHomeomorph Y T)
    (he : Set.EqOn A L (A.source ∩ L.source)) :
    let H := partialHomeomorphOverlap A L
    let a' := a.restrOpen H H.isOpen
    let c := (P.symm.trans A).trans a'
    let c' := (P.symm.trans L).trans a
    c.source ⊆ c'.source ∧ Set.EqOn c c' c.source := by
  dsimp only
  constructor
  · intro p hp
    change (p ∈ P.target ∧ P.symm p ∈ A.source) ∧
      A (P.symm p) ∈ a.source ∩ partialHomeomorphOverlap A L at hp
    obtain ⟨hL, hAL⟩ := partialHomeomorph_overlap_pullback A L he (P.symm p) hp.1.2 hp.2.2
    change (p ∈ P.target ∧ P.symm p ∈ L.source) ∧ L (P.symm p) ∈ a.source
    exact ⟨⟨hp.1.1, hL⟩, hAL ▸ hp.2.1⟩
  · intro p hp
    change (p ∈ P.target ∧ P.symm p ∈ A.source) ∧
      A (P.symm p) ∈ a.source ∩ partialHomeomorphOverlap A L at hp
    obtain ⟨_, hAL⟩ := partialHomeomorph_overlap_pullback A L he (P.symm p) hp.1.2 hp.2.2
    change a (A (P.symm p)) = a (L (P.symm p))
    exact congrArg a hAL

#print axioms partialHomeomorph_restricted_coordinates
#print axioms partialHomeomorphOverlap
#print axioms partialHomeomorph_overlap_pullback

end HodgeLean.Foundations.TubularEuler

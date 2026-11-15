import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportCollar
import Mathlib.Topology.Maps.Proper.Basic

/-! # Actual neighborhoods with entire deformation tracks in a prescribed open
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- A support-fixing deformation has an actual open support neighborhood whose entire tracks lie in any prescribed support neighborhood.
Source: Munkres, Topology, section 26, the tube lemma for a compact parameter interval.
HC no distance; AV milestone no distance. -/
lemma properCycle_support_collar_track_neighborhood
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (hfixed : ∀ (t : unitInterval) (s : TopCat.of S),
      C.deformation (t, C.inclusion s) = C.inclusion s)
    (P : Set X) (hP : IsOpen P) (hSP : S ⊆ P) :
    ∃ V : Set X, IsOpen V ∧ S ⊆ V ∧ ∃ hVC : V ⊆ C.neighborhood,
      ∀ (v : X) (hv : v ∈ V) (t : unitInterval),
        (C.deformation (t, ⟨v, hVC hv⟩) : X) ∈ P := by
  let B : Set (unitInterval × C.neighborhood) :=
    {tu | (C.deformation tu : X) ∉ P}
  have hB : IsClosed B := hP.isClosed_compl.preimage
    (continuous_subtype_val.comp C.deformation.continuous)
  let bad : Set C.neighborhood := Prod.snd '' B
  have hbad : IsClosed bad := isClosedMap_snd_of_compactSpace B hB
  let O : Set C.neighborhood := badᶜ
  have hO (u : C.neighborhood) : u ∈ O ↔
      ∀ t : unitInterval, (C.deformation (t, u) : X) ∈ P := by
    constructor
    · intro hu t
      by_contra hnot
      exact hu ⟨(t, u), hnot, rfl⟩
    · intro hu ⟨⟨t, v⟩, hb, he⟩
      change v = u at he
      subst v
      exact hb (hu t)
  let V : Set X := Subtype.val '' O
  have hV : IsOpen V := C.isOpen.isOpenEmbedding_subtypeVal.isOpenMap O hbad.isOpen_compl
  have hVC : V ⊆ C.neighborhood := by
    rintro v ⟨u, _, rfl⟩
    exact u.property
  refine ⟨V, hV, ?_, hVC, ?_⟩
  · intro s hs
    let z : TopCat.of S := ⟨s, hs⟩
    have hz : C.inclusion z ∈ O := (hO _).mpr (fun t => by
      have hh := congrArg (fun u : C.neighborhood => (u : X)) (hfixed t z)
      change (C.deformation (t, C.inclusion z) : X) = (C.inclusion z : X) at hh
      rw [hh]
      have hj := ConcreteCategory.congr_hom C.inclusion_factor z
      change (C.inclusion z : X) = s at hj
      rw [hj]
      exact hSP hs)
    exact ⟨C.inclusion z, hz, ConcreteCategory.congr_hom C.inclusion_factor z⟩
  · rintro v ⟨u, hu, rfl⟩ t
    exact (hO u).mp hu t

end HodgeLean.Foundations.QuotientDuality

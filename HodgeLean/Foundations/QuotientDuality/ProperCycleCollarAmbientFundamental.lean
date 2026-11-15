import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarAmbientPoint
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeTriadPointProjection
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodFundamentalPoint

/-! # The specified original ambient class in the literal collar point triad
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original excised ambient class projected into the actual collar triad has precisely the specified original ambient local value under point excision.
Source: properCycle_relative_triad_point_projection; properCycle_neighborhood_fundamental_point_value.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.pointAmbient_fundamental {X : TopCat.{0}} {S : Set X}
    [T1Space X] (C : ProperCycleSupportCollar X S) (hS : IsClosed S) (z : S)
    (n : ℕ) (c : Homology ℚ X n) :
    (C.pointAmbientIso hS z n).hom.hom
      ((HomologicalComplex.homologyMap
        (properCycle_relative_to_triad_chain_map (TopCat.of C.neighborhood)
          (Subtype.val ⁻¹' Sᶜ) (C.retraction ⁻¹' ({z} : Set S)ᶜ)) n).hom
        (properCycle_neighborhood_relative_fundamental X S C.neighborhood hS C.isOpen
          C.contains n c)) =
      localOrientation X n c (C.inclusion z).val := by
  let U := TopCat.of C.neighborhood
  let A : Set U := Subtype.val ⁻¹' Sᶜ
  let B : Set U := C.retraction ⁻¹' ({z} : Set S)ᶜ
  have hA : IsOpen A := hS.isOpen_compl.preimage continuous_subtype_val
  have hB : IsOpen B := isClosed_singleton.isOpen_compl.preimage C.retraction.hom.continuous
  have hu : A ∪ B = ({C.inclusion z} : Set U)ᶜ := C.point_triad_union z
  have hj : (C.inclusion z).val = z.val := by
    have h := ConcreteCategory.congr_hom C.inclusion_factor (z : TopCat.of S)
    exact h
  have hzS : (C.inclusion z).val ∈ S := hj.symm ▸ z.property
  let d := properCycle_neighborhood_relative_fundamental X S C.neighborhood hS C.isOpen
    C.contains n c
  let f := TopPair.ofSubsetHom (𝟙 U)
    (show Set.MapsTo (𝟙 U) A ({C.inclusion z} : Set U)ᶜ from fun _ ha => hu ▸ Or.inl ha)
  have hh := ConcreteCategory.congr_hom
    (properCycle_relative_triad_point_projection U A B hA hB (C.inclusion z) hu n) d
  change (C.pointTriadIso hS z n).hom.hom
    ((HomologicalComplex.homologyMap (properCycle_relative_to_triad_chain_map U A B) n).hom d) =
      relativeHomologyMap ℚ n f d at hh
  have hf : f = supportInclusionPairMap U (Set.singleton_subset_iff.mpr hzS) := by
    ext x : 2 <;> rfl
  rw [hf] at hh
  change relativeHomologyMap ℚ n
    (imagePointPairMap (TopPair.ofSubset (X := X) C.neighborhood).map Subtype.val_injective
      (C.inclusion z))
    ((C.pointTriadIso hS z n).hom.hom
      ((HomologicalComplex.homologyMap (properCycle_relative_to_triad_chain_map U A B) n).hom d)) = _
  exact (congrArg (relativeHomologyMap ℚ n
    (imagePointPairMap (TopPair.ofSubset (X := X) C.neighborhood).map Subtype.val_injective
      (C.inclusion z))) hh).trans
    (properCycle_neighborhood_fundamental_point_value X S C.neighborhood hS C.isOpen
      C.contains n c (C.inclusion z) hzS)

end HodgeLean.Foundations.QuotientDuality

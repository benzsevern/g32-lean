import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarAmbientPoint
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenPointExcisionMap

/-! # The original ambient inverse in the actual collar point triad
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual collar ambient inverse is original open point excision followed by the original inverse triad comparison.
Source: ProperCycleSupportCollar.pointAmbientIso; properCycle_open_local_homology_iso_map.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.point_ambient_inverse
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S)
    (hS : IsClosed S) (z : S) (n : ℕ)
    (c : orientationGroup X n (C.inclusion z).val) :
    (C.pointAmbientIso hS z n).inv.hom c =
      (C.pointTriadIso hS z n).inv.hom
        ((properCycle_open_local_homology_iso X ⟨C.neighborhood, C.isOpen⟩ (C.inclusion z) n).inv.hom c) := by
  let e := C.pointAmbientIso hS z n
  let t := C.pointTriadIso hS z n
  let o := properCycle_open_local_homology_iso X ⟨C.neighborhood, C.isOpen⟩ (C.inclusion z) n
  let i : TopCat.of C.neighborhood ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  apply e.toLinearEquiv.injective
  change e.hom.hom (e.inv.hom c) = e.hom.hom (t.inv.hom (o.inv.hom c))
  rw [e.inv_hom_id_apply]
  change c = relativeHomologyMap ℚ n
    (imagePointPairMap i Subtype.val_injective (C.inclusion z))
    (t.hom.hom (t.inv.hom (o.inv.hom c)))
  rw [t.inv_hom_id_apply]
  have ho := properCycle_open_local_homology_iso_map X ⟨C.neighborhood, C.isOpen⟩ (C.inclusion z) n
  change o.hom.hom = relativeHomologyMap ℚ n (imagePointPairMap i Subtype.val_injective (C.inclusion z)) at ho
  rw [← ho]
  exact (o.inv_hom_id_apply c).symm

end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarRestrictedPointTriad
import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadLocalHomology

/-! # Literal point excision on smaller collar point triads
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual open-triad excision identifies the smaller collar triad with its original ambient point homology.
Source: properCycle_triad_local_homology_iso; ProperCycleSupportCollar.restricted_point_triad_union.
HC no distance; AV milestone no distance. -/
def ProperCycleSupportCollar.restricted_point_triad_iso
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S)
    (hS : IsClosed S) (W : Opens X) (hWN : (W : Set X) ⊆ C.neighborhood)
    (z : S) (hzW : z.val ∈ W) (n : ℕ) :
    TriadRelativeHomology ℚ (TopCat.of W) (Subtype.val ⁻¹' Sᶜ)
      ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) n ≅
      orientationGroup (TopCat.of W) n ⟨z.val, hzW⟩ := by
  let i : TopCat.of W ⟶ TopCat.of C.neighborhood :=
    TopCat.ofHom ⟨fun x => ⟨x.val, hWN x.property⟩, continuous_subtype_val.subtype_mk _⟩
  exact properCycle_triad_local_homology_iso (TopCat.of W) _ _
    (hS.isOpen_compl.preimage continuous_subtype_val)
    ((isClosed_singleton (x := z)).isOpen_compl.preimage
      (C.retraction.hom.continuous.comp i.hom.continuous))
    ⟨z.val, hzW⟩ (C.restricted_point_triad_union W hWN z hzW) n

end HodgeLean.Foundations.QuotientDuality

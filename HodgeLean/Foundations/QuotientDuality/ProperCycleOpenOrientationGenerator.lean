import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTransport

/-! # The specified ambient orientation after actual point excision
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Inverse point excision carries the specified ambient orientation to a generator on every actual open neighborhood.
Source: properCycle_open_local_homology_iso; Hatcher, Algebraic Topology, section 2.2.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_orientation_generator
    (X : TopCat.{0}) [T1Space X] (W : Opens X) (w : W) (n : ℕ)
    (c : Homology ℚ X n)
    (hc : Function.Bijective (orientationLine X n c w.val)) :
    Function.Bijective (LinearMap.toSpanSingleton ℚ _
      ((properCycle_open_local_homology_iso X W w n).inv.hom
        (localOrientation X n c w.val))) := by
  let e := properCycle_open_local_homology_iso X W w n
  have he : LinearMap.toSpanSingleton ℚ _ (e.inv.hom (localOrientation X n c w.val)) =
      e.inv.hom.comp (orientationLine X n c w.val) := by
    apply LinearMap.ext
    intro q
    exact (map_smul e.inv.hom q _).symm
  rw [he]
  exact e.toLinearEquiv.symm.bijective.comp hc

end HodgeLean.Foundations.QuotientDuality

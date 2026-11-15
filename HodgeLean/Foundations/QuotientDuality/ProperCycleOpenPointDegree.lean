import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTransport

/-! # Original degree transport and inverse point excision
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Original inverse open point excision commutes with literal transport of the homology degree.
Source: properCycle_open_local_homology_iso; equality transport.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_point_inverse_degree
    (X : TopCat.{0}) [T1Space X] (W : Opens X) (w : W) (n m : ℕ) (h : n = m)
    (c : orientationGroup X n w.val) :
    (properCycle_open_local_homology_iso X W w m).inv.hom
      ((eqToIso (congrArg (fun j => orientationGroup X j w.val) h)).hom.hom c) =
    (eqToIso (congrArg (fun j => orientationGroup (TopCat.of W) j w) h)).hom.hom
      ((properCycle_open_local_homology_iso X W w n).inv.hom c) := by
  subst m
  rfl

end HodgeLean.Foundations.QuotientDuality

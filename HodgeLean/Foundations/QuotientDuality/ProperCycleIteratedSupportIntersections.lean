import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedSupportSuspension
import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionRelativeSupportCapRecurrence

/-! # Literal intersections in actual iterated normal cap supports
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual iterated normal and tangential supports intersect in the iterated point support of their original intersection.
Source: Munkres, Topology, section 19, finite product subspaces.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_support_intersection
    (Y : TopCat.{0}) (S T : Set Y) (n : ℕ) :
    properCycle_real_normal_support Y S n ∩ properCycle_real_point_support Y T n =
      properCycle_real_point_support Y (S ∩ T) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext z
    change (z.2 ∈ properCycle_real_normal_support Y S n ∧
      z.1 = 0 ∧ z.2 ∈ properCycle_real_point_support Y T n) ↔
      z.1 = 0 ∧ z.2 ∈ properCycle_real_point_support Y (S ∩ T) n
    have hz : z.2 ∈ properCycle_real_point_support Y (S ∩ T) n ↔
        z.2 ∈ properCycle_real_normal_support Y S n ∧
        z.2 ∈ properCycle_real_point_support Y T n := (Set.ext_iff.mp ih z.2).symm
    rw [hz]
    tauto

/-- The actual recursive support-intersection equality gives its specified identity pair isomorphism.
Source: properCycle_iterated_support_intersection; CategoryTheory.eqToIso.
HC no distance; AV milestone no distance. -/
def properCycle_iterated_support_intersection_pair_iso
    (Y : TopCat.{0}) (S T : Set Y) (n : ℕ) :
    TopPair.ofSubset (X := properCycle_real_support_space Y n)
      (properCycle_real_normal_support Y S n ∩ properCycle_real_point_support Y T n)ᶜ ≅
      TopPair.ofSubset (X := properCycle_real_support_space Y n)
        (properCycle_real_point_support Y (S ∩ T) n)ᶜ :=
  eqToIso (congrArg (fun U : Set (properCycle_real_support_space Y n) =>
    TopPair.ofSubset (X := properCycle_real_support_space Y n) Uᶜ)
      (properCycle_iterated_support_intersection Y S T n))

end HodgeLean.Foundations.QuotientDuality

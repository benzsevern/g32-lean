import HodgeLean.Foundations.RationalHomologyManifold.CompactDetection

/-! From compact point detection to injectivity of absolute localization.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- All point values detect an absolute top class, with no connectedness requirement.
Source: Hatcher, Algebraic Topology, Theorem 3.26 and its compact-support gluing argument.
HC no distance; AV milestone no distance.
-/
theorem finiteTriangulation_localization_injective (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (t : FiniteTriangulation X)
    (n : ℕ) (o : LocalRationalOrientation X n) :
    Function.Injective (localization X n) := by
  intro c d hall
  obtain ⟨e, he, hu⟩ := fundamental_class_of_compact_detection X n o
    (finiteTriangulation_compact_detection X t n o)
  have hw : localization X n (e + (c - d)) = o.generator := by
    rw [map_add, map_sub, hall, sub_self, add_zero]
    exact funext he
  have hz : e + (c - d) = e := hu _ (fun y => congrFun hw y)
  exact sub_eq_zero.mp (add_left_cancel (hz.trans (add_zero e).symm))

#print axioms finiteTriangulation_localization_injective
end HodgeLean.Foundations.RationalHomologyManifold

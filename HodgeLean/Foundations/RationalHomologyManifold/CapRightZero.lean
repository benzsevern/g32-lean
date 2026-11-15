import HodgeLean.Foundations.RationalHomologyManifold.TopClass
import HodgeLean.Foundations.RationalHomologyManifold.CapNaturality
import HodgeLean.Foundations.QuotientDuality.LocalTriangulationConnectedness

/-! The complementary-degree edge with degree-zero target homology.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Cap maps top cohomology bijectively to degree-zero homology.
Source: Hatcher, Algebraic Topology, section 3.3, cup-cap evaluation and Theorem 3.26.
HC no distance; AV milestone no distance.
-/
theorem cap_right_zero_bijective (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    [ConnectedSpace X] (t : FiniteTriangulation X) (p : ℕ)
    (o : LocalRationalOrientation X (p + 0)) (c : Homology ℚ X (p + 0))
    (hc : localization X (p + 0) c = o.generator) :
    Function.Bijective (localTraceCap X p 0 c) := by
  letI := triangulated_pathConnected X t.ambient t.complex t.finite_faces t.realization
  let e : Homology ℚ X 0 →ₗ[ℚ] ℚ := cohomologyEquivDualHomology ℚ X 0
    (HodgeLean.Foundations.Singular.unit X)
  have hei : Function.Injective e := by
    intro z w hzw
    apply sub_eq_zero.mp
    by_contra hne
    apply singular_unit_evaluation_ne_zero X (z - w) hne
    exact (map_sub e z w).trans (sub_eq_zero.mpr hzw)
  have heval (a : Cohomology ℚ X p) :
      e (localTraceCap X p 0 c a) = cohomologyEquivDualHomology ℚ X p a c := by
    simpa only [e, Nat.add_zero, HodgeLean.Foundations.Singular.cup_one] using
      cap_evaluation X p 0 c a (HodgeLean.Foundations.Singular.unit X)
  have ht := topClass_evaluation_bijective X t (p + 0) o c hc
  constructor
  · intro a b hab
    apply ht.1
    exact (heval a).symm.trans ((congrArg e hab).trans (heval b))
  · intro z
    obtain ⟨a, ha⟩ := ht.2 (e z)
    exact ⟨a, hei ((heval a).trans ha)⟩

#print axioms cap_right_zero_bijective
end HodgeLean.Foundations.RationalHomologyManifold

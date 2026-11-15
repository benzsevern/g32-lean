import HodgeLean.Foundations.RationalHomologyManifold.Defs
import HodgeLean.Foundations.QuotientDuality.LocalCupCompatibility

/-! Naturality of the actual cap map under arbitrary continuous maps.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Evaluating cap is evaluation of the ordered cup product on the original class.
Source: Hatcher, Algebraic Topology, section 3.3, cup-cap evaluation identity.
HC no distance; AV milestone no distance.
-/
theorem cap_evaluation (X : TopCat.{0}) (p q : ℕ)
    (c : Homology ℚ X (p + q)) (a : Cohomology ℚ X p) (b : Cohomology ℚ X q) :
    cohomologyEquivDualHomology ℚ X q b (localTraceCap X p q c a) =
      cohomologyEquivDualHomology ℚ X (p + q)
        (HodgeLean.Foundations.Singular.cup X rfl a b) c := by
  rw [← localTraceCup_eq_singularCup]
  change _ = cohomologyEquivDualHomology ℚ X (p + q)
    ((cohomologyEquivDualHomology ℚ X (p + q)).symm _) c
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Pushforward of cap with a pulled-back class equals cap with the pushed-forward class.
Source: Hatcher, Algebraic Topology, section 3.3, naturality of cap.
HC no distance; AV milestone no distance.
-/
theorem cap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (c : Homology ℚ X (p + q)) (a : Cohomology ℚ Y p) :
    homologyMap ℚ q f (localTraceCap X p q c (cohomologyMap ℚ p f a)) =
      localTraceCap Y p q (homologyMap ℚ (p + q) f c) a := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro l
  obtain ⟨b, rfl⟩ := (cohomologyEquivDualHomology ℚ Y q).surjective l
  rw [map_sub]
  apply sub_eq_zero.mpr
  rw [← cohomologyEquivDualHomology_cohomologyMap, cap_evaluation, cap_evaluation,
    ← HodgeLean.Foundations.Singular.cohomologyMap_cup,
    cohomologyEquivDualHomology_cohomologyMap]

#print axioms cap_evaluation
#print axioms cap_naturality
end HodgeLean.Foundations.RationalHomologyManifold

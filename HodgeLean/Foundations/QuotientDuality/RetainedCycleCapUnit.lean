import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapWithOrientation
import HodgeLean.Foundations.QuotientDuality.OrientationDefs
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Capping the actual singular cup unit returns the specified global class. -/
theorem retained_cap_with_orientation_unit (X : TopCat.{0}) (n : ℕ)
    (c : Homology ℚ X n) :
    retainedCapWithOrientation X 0 n ((Nat.zero_add n).symm ▸ c)
      (HodgeLean.Foundations.Singular.unit X) = c := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro f
  obtain ⟨b, rfl⟩ := (cohomologyEquivDualHomology ℚ X n).surjective f
  rw [map_sub]
  apply sub_eq_zero.mpr
  have h := retained_orientation_cap_evaluation_cast X 0 n n (Nat.zero_add n) c
    (HodgeLean.Foundations.Singular.unit X) b
  rw [HodgeLean.Foundations.Singular.one_cup] at h
  exact h.symm

/-- The local projection of cap on constant classes is the exact supplied orientation line. -/
theorem retained_local_cap_on_constants (X : TopCat.{0}) (n : ℕ)
    (c : Homology ℚ X n) (x : X) (r : ℚ) :
    (relativeHomologyProjection ℚ (pointComplementPair x) n).hom
      (retainedCapWithOrientation X 0 n ((Nat.zero_add n).symm ▸ c)
        (r • HodgeLean.Foundations.Singular.unit X)) = orientationLine X n c x r := by
  rw [map_smul, retained_cap_with_orientation_unit, map_smul]
  rfl

/-- The actual local cap operation on constants is bijective under the frozen local orientation hypothesis. -/
theorem retained_local_cap_on_constants_bijective (X : TopCat.{0}) (n : ℕ)
    (c : Homology ℚ X n) (x : X)
    (ho : Function.Bijective (orientationLine X n c x)) :
    Function.Bijective (fun r : ℚ =>
      (relativeHomologyProjection ℚ (pointComplementPair x) n).hom
        (retainedCapWithOrientation X 0 n ((Nat.zero_add n).symm ▸ c)
          (r • HodgeLean.Foundations.Singular.unit X))) := by
  simpa only [retained_local_cap_on_constants] using ho

end HodgeLean.Foundations.QuotientDuality

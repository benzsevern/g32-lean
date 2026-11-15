import HodgeLean.Foundations.QuotientDuality.LocalCupCompatibility
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The actual singular cup unit controls the degree-zero trace pairing. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The singular cup unit spans degree-zero cohomology on a path-connected space.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.2. -/
theorem exists_smul_singular_unit (X : TopCat.{0}) [PathConnectedSpace X]
    (a : Cohomology ℚ X 0) :
    ∃ r : ℚ, r • HodgeLean.Foundations.Singular.unit X = a := by
  obtain ⟨t, ht⟩ := exists_smul_cohomologyUnitZero ℚ X
    (HodgeLean.Foundations.Singular.unit X)
  have ht0 : t ≠ 0 := by
    intro h
    apply HodgeLean.Foundations.Singular.unit_ne_zero (R := ℚ) X
    rw [← ht, h, zero_smul]
  obtain ⟨s, hs⟩ := exists_smul_cohomologyUnitZero ℚ X a
  refine ⟨s / t, ?_⟩
  rw [← ht, smul_smul, div_mul_cancel₀ _ ht0, hs]

/-- The cup unit evaluates nontrivially on any nonzero degree-zero homology class.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.2; universal coefficients over ℚ. -/
theorem singular_unit_evaluation_ne_zero (X : TopCat.{0}) [PathConnectedSpace X]
    (c : Homology ℚ X 0) (hc : c ≠ 0) :
    cohomologyEquivDualHomology ℚ X 0 (HodgeLean.Foundations.Singular.unit X) c ≠ 0 := by
  intro h
  apply hc
  apply (Module.forall_dual_apply_eq_zero_iff ℚ c).mp
  intro f
  obtain ⟨a, ha⟩ := (cohomologyEquivDualHomology ℚ X 0).surjective f
  obtain ⟨r, rfl⟩ := exists_smul_singular_unit X a
  rw [← ha, map_smul, LinearMap.smul_apply, h, smul_zero]

/-- The degree-zero trace pairing is perfect for any nonzero class on a path-connected space.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.2; the singular cup unit law. -/
theorem localTracePairing_zero_bijective (X : TopCat.{0}) [PathConnectedSpace X]
    [FiniteDimensional ℚ (Cohomology ℚ X 0)]
    (c : Homology ℚ X 0) (hc : c ≠ 0) :
    Function.Bijective (localTracePairing X 0 0 c) := by
  let u : Cohomology ℚ X 0 := HodgeLean.Foundations.Singular.unit X
  have he : localTracePairing X 0 0 c u u =
      cohomologyEquivDualHomology ℚ X 0 u c := by
    have h := congrArg (fun v => cohomologyEquivDualHomology ℚ X 0 v c)
      (localTraceCup_eq_singularCup X 0 0 u u)
    change (cohomologyEquivDualHomology ℚ X 0
      ((cohomologyEquivDualHomology ℚ X 0).symm _)) c = _ at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.trans (congrArg (fun v => cohomologyEquivDualHomology ℚ X 0 v c)
      (HodgeLean.Foundations.Singular.cup_one X u))
  have hne : localTracePairing X 0 0 c u u ≠ 0 := by
    rw [he]
    exact singular_unit_evaluation_ne_zero X c hc
  have hi : Function.Injective (localTracePairing X 0 0 c) := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm ?_ bot_le
    intro a ha
    change a = 0
    obtain ⟨r, rfl⟩ := exists_smul_singular_unit X a
    have hz := congrArg (fun f : Module.Dual ℚ (Cohomology ℚ X 0) => f u)
      (show localTracePairing X 0 0 c (r • u) = 0 from ha)
    have hr : r = 0 := (mul_eq_zero.mp (show r * localTracePairing X 0 0 c u u = 0 by
      simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] using hz)).resolve_right hne
    rw [hr, zero_smul]
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Subspace.dual_finrank_eq])).mp hi⟩

/-- A global class realizing local rational generators is nonzero on a nonempty space.
Source: Hatcher, Algebraic Topology, section 3.3, definition of a fundamental class. -/
theorem global_class_ne_zero_of_local_generators (X : TopCat.{0}) [Nonempty X]
    (n : ℕ) (o : LocalRationalOrientation X n) (c : Homology ℚ X n)
    (hc : ∀ x, localOrientation X n c x = o.generator x) : c ≠ 0 := by
  intro h
  let x : X := Classical.choice inferInstance
  have hg : o.generator x = 0 := by
    rw [← hc x, h]
    exact map_zero (relativeHomologyProjection ℚ (pointComplementPair x) n).hom
  have h01 : (0 : ℚ) = 1 := (o.generates x).1 (by
    simp only [LinearMap.toSpanSingleton_apply, hg, smul_zero])
  exact zero_ne_one h01

#print axioms global_class_ne_zero_of_local_generators

#print axioms localTracePairing_zero_bijective

#print axioms singular_unit_evaluation_ne_zero

#print axioms exists_smul_singular_unit
end HodgeLean.Foundations.QuotientDuality

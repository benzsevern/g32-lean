import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Actual degree-zero supported cohomology on a one-point space -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual whole-support rational cohomology in degree zero on a nonempty one-point space has dimension one.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.1, degree-zero homology and universal coefficients.
HC no distance; AV milestone no distance. -/
lemma properCycle_subsingleton_whole_support_zero_finrank
    (X : TopCat.{0}) [Subsingleton X] [Nonempty X] :
    Module.finrank ℚ (CohomologyWithSupport ℚ X Set.univ 0) = 1 := by
  letI : PathConnectedSpace X :=
    ⟨inferInstance, fun x y => by simpa only [Subsingleton.elim y x] using Joined.refl x⟩
  let e := (asIso (TopCat.singularHomology₀ε X (ModuleCat.of ℚ ℚ))).toLinearEquiv
  calc
    _ = Module.finrank ℚ (Cohomology ℚ X 0) :=
      (wholeSupportCohomologyLinearEquiv ℚ X 0).finrank_eq
    _ = Module.finrank ℚ (Module.Dual ℚ (Homology ℚ X 0)) :=
      (cohomologyEquivDualHomology ℚ X 0).finrank_eq
    _ = Module.finrank ℚ (Homology ℚ X 0) := Subspace.dual_finrank_eq
    _ = Module.finrank ℚ ℚ := e.finrank_eq
    _ = 1 := Module.finrank_self ℚ

/-- Every nonzero actual degree-zero whole-support class on a nonempty one-point space is a rational generator.
Source: Hatcher, Algebraic Topology, section 3.1, degree-zero cohomology of a point.
HC no distance; AV milestone no distance. -/
lemma properCycle_subsingleton_whole_support_zero_generator
    (X : TopCat.{0}) [Subsingleton X] [Nonempty X]
    (a : CohomologyWithSupport ℚ X Set.univ 0) (ha : a ≠ 0) :
    Function.Bijective (LinearMap.toSpanSingleton ℚ (CohomologyWithSupport ℚ X Set.univ 0) a) := by
  constructor
  · intro q r hqr
    exact smul_left_injective ℚ ha hqr
  · intro b
    exact (finrank_eq_one_iff_of_nonzero' a ha).mp
      (properCycle_subsingleton_whole_support_zero_finrank X) b

end HodgeLean.Foundations.QuotientDuality

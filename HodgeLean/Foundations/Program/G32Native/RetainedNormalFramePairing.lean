import HodgeLean.Foundations.TubularEuler.NormalFrameRegularCoefficientHelpers
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Evaluating a retained normal functional in algebraic frame coordinates -/
noncomputable section
set_option maxHeartbeats 100000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- Evaluation in a finite basis is the pairing of its primal and dual coordinates.
Source: `Module.Basis.sum_repr` and `Module.Basis.dualBasis_equivFun`. -/
theorem dual_coordinate_pairing {K M : Type*} [Field K]
    [AddCommGroup M] [Module K M] {k : ℕ} (b : Module.Basis (Fin k) K M)
    (n : Module.Dual K M) (v : M) :
    n v = ∑ a, b.dualBasis.equivFun n a * b.repr v a := by
  conv_lhs => rw [← b.sum_repr v, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, Module.Basis.dualBasis_equivFun, smul_eq_mul, mul_comm]

/-- The original functional evaluates an algebraic section by the regular
coefficients of that section in the actual conormal frame.
Source: `dual_coordinate_pairing` and `normalFrameSectionCoefficient_evaluate`. -/
theorem retained_normal_frame_section_pairing
    {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (k : ℕ)
    (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U)
    (n : i1_normalFibre j x) :
    n (i1_conormalSectionValue j U s x hx) =
      ∑ a, (i1_conormalFrameBasis j k U E x hx).dualBasis.equivFun n a *
        Point.evaluate U (normalFrameSectionCoefficient j k U E s a) x := by
  rw [dual_coordinate_pairing (i1_conormalFrameBasis j k U E x hx)]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  exact normalFrameSectionCoefficient_evaluate j k U E s x hx a

#print axioms dual_coordinate_pairing
#print axioms retained_normal_frame_section_pairing
end HodgeLean.Foundations.TubularEuler

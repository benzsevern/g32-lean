import HodgeLean.Foundations.Program.G32Native.PairedConormalActualCommonZero
import HodgeLean.Foundations.Program.G32Native.PairedConormalRelationMatrix

/-! # Invertible literal coefficient matrix of the actual original relation -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.Picard.LineBundles
open HodgeLean.Foundations.NormalPresentation
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual pointwise nonzero relation has an invertible literal homogeneous
coefficient matrix, with its exact original row coefficients retained. -/
theorem conormal_actual_relation_matrix (k : ℕ) (hk : 0 < k)
    (b : idealModule (s2e_hyperplaneIdeal k) ⟶
      (SheafOfModules.free (Fin k) : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules))
    (hrel : ∀ x : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))),
      (Scheme.Modules.pullback x.left).map (relation
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (s2e_hyperplaneIdeal k).subschemeι.toRingCatSheafHom)) b) ≠ 0) :
    ∃ p : Fin k → homogeneousSubmodule (Fin (k + 1)) ℂ 1,
      IsUnit (conormalRelationMatrix k p) ∧
      ∀ (t : Fin k) (j : Fin (k + 1)),
        conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k)
          (conormalOriginalIdealRow k k b t) (conormalNativeCoordinateOpen ℂ k j)
          (ProjSpace.coordinateRatioSection ℂ k j 0) (conormal_native_hyperplane_coordinate_mem ℂ k j) =
            ProjSpace.homogeneousRatioSection ℂ k 1 (p t) j := by
  obtain ⟨p, hp⟩ := conormal_original_ideal_rows_linear_forms k k (by omega) b
  refine ⟨p, Matrix.mulVec_injective_iff_isUnit.mp ?_, hp⟩
  intro v w hvw
  have hz : (conormalRelationMatrix k p).mulVec (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  apply sub_eq_zero.mp
  apply conormal_actual_relation_rows_common_zero k b hrel p hp
  · have h := congrFun hz 0
    simpa only [conormal_relation_matrix_mulVec_zero, Pi.zero_apply] using h
  · intro t
    have h := congrFun hz t.succ
    simpa only [conormal_relation_matrix_mulVec_succ, Pi.zero_apply] using h

end HodgeLean.Foundations.Program.G32Native

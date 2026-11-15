import HodgeLean.Foundations.Program.G32Native.PairedConormalPointPolynomialCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedConormalNativePresentation
import HodgeLean.Foundations.Program.G32Native.PairedConormalRelationMatrix
import HodgeLean.Foundations.Program.G32Native.PairedConormalDistinguishedCoordinate

/-! # The actual retained relation matrix on normalized complex fibres -/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original coefficient matrix gives the actual normalized relation
column, with the exact single nonzero denominator scalar retained. -/
theorem conormal_actual_point_relation_matrix (k : ℕ)
    (b : idealModule (s2e_hyperplaneIdeal k) ⟶
      (SheafOfModules.free (Fin k) : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules))
    (p : Fin k → homogeneousSubmodule (Fin (k + 1)) ℂ 1)
    (hp : ∀ (t : Fin k) (j : Fin (k + 1)),
      conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k)
        (conormalOriginalIdealRow k k b t) (conormalNativeCoordinateOpen ℂ k j)
        (ProjSpace.coordinateRatioSection ℂ k j 0)
        (conormal_native_hyperplane_coordinate_mem ℂ k j) =
          ProjSpace.homogeneousRatioSection ℂ k 1 (p t) j)
    (v : Fin (k + 1) → ℂ) (i : Fin (k + 1)) (hi : v i ≠ 0) :
    let x := conormalPolynomialChartComplexPoint v i hi
    let hx : x ∈ Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1 :=
      conormal_polynomial_chart_complex_point_mem v i hi
    EulerModel.normalHomogeneousCoordinates k
      (conormalPointRelationVector k
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (conormalNativeHyperplaneIdeal ℂ k).subschemeι.toRingCatSheafHom))
        (conormalNativeRetainedArrow k b) x.left (conormalNativeIdealPointFrame k i x hx)) =
      (v i)⁻¹ • (conormalRelationMatrix k p).mulVec v := by
  dsimp only
  let a := kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (conormalNativeHyperplaneIdeal ℂ k).subschemeι.toRingCatSheafHom)
  let rows : Fin (k + 1) → homogeneousSubmodule (Fin (k + 1)) ℂ 1 :=
    Fin.cases (conormalCoordinatePolynomial ℂ k 0) p
  have h := conormal_native_point_relation_polynomial_coordinates k a
    (conormalNativeRetainedArrow k b) rows (by
      intro r j
      refine Fin.cases ?_ (fun t => ?_) r
      · exact conormal_native_hyperplane_inclusion_numerator k j
      · dsimp only [Fin.cases_succ, rows]
        rw [conormal_native_retained_arrow_row]
        exact hp t j) v i hi
  dsimp only at h
  refine h.trans ?_
  apply congrArg (fun w : Fin (k + 1) → ℂ => (v i)⁻¹ • w)
  funext r
  refine Fin.cases ?_ (fun t => ?_) r
  · simp only [rows, Fin.cases_zero, conormalCoordinatePolynomial,
      eval_X, conormal_relation_matrix_mulVec_zero]
  · simp only [rows, Fin.cases_succ, conormal_relation_matrix_mulVec_succ]

#print axioms conormal_actual_point_relation_matrix
end HodgeLean.Foundations.Program.G32Native

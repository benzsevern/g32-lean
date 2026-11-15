import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateIdealEvaluationIso
import HodgeLean.Foundations.Program.G32Native.PairedC3LinearCommonZero
import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeIdealForms
import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialRowZero
import HodgeLean.Foundations.Program.G32Native.PairedConormalFreeProjectionDetection
import HodgeLean.Foundations.Program.G32Native.PairedConormalLinearFormCoefficients
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # A common fibre zero of fewer than k+1 linear sections on projective k-space -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Matrix
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Fewer than k+1 actual maps from the negative line have a common
complex fibre zero, with the original maps retained.
Source: Hartshorne, Algebraic Geometry, I.2, homogeneous linear subspaces. -/
theorem paired_c3_negative_to_free_zero_fibre (k n : ℕ) (hk : 0 < k) (hn : n < k + 1)
    (f : pairedC3NegativeLine k ⟶
      (SheafOfModules.free (R := (pairedC3Proj k).ringCatSheaf) (Fin n) : (pairedC3Proj k).Modules)) :
    ∃ x : ComplexPoint (conormalPolynomialModelOver k), (Scheme.Modules.pullback x.left).map f = 0 := by
  letI := paired_c3_coordinate_ideal_evaluation_isIso k 0
  let eI : pairedC3NegativeLine k ≅ idealModule (conormalNativeHyperplaneIdeal ℂ k) :=
    asIso (pairedC3CoordinateIdealEvaluation k 0)
  let fI := eI.inv ≫ f
  let row (t : Fin n) := fI ≫ i1_freeSheafProjection (pairedC3Proj k) n t
  have hforms (t : Fin n) := conormal_native_ideal_map_linear_form ℂ k hk
    (conormalNativeHyperplaneIdeal ℂ k) (conormal_native_hyperplane_coordinate_mem ℂ k) (row t)
  choose p hp using hforms
  let A : Matrix (Fin n) (Fin (k + 1)) ℂ := Matrix.of
    (fun t j => conormalLinearFormCoefficient k (p t) j)
  obtain ⟨v, hv, hl⟩ := paired_c3_linear_common_zero hn A.mulVecLin
  have hvp (t : Fin n) : eval v (p t).val = 0 := by
    have h := congrFun hl t
    change (∑ j, conormalLinearFormCoefficient k (p t) j * v j) = 0 at h
    exact (conormal_linear_form_eval k (p t) v).trans h
  obtain ⟨i, hi⟩ : ∃ i : Fin (k + 1), v i ≠ 0 := by
    by_contra hzero
    apply hv
    funext i
    exact not_not.mp ((not_exists.mp hzero) i)
  let x := conormalPolynomialChartComplexPoint v i hi
  let G := Scheme.Modules.pullback x.left
  have hrow (t : Fin n) : G.map (row t) = 0 :=
    (conormal_polynomial_ideal_row_pullback_zero_iff k (row t) (p t) (hp t) v i hi).mpr (hvp t)
  have hIz : G.map fI = 0 := by
    apply conormal_map_free_projections_detect_zero (pairedC3Proj k) n G
    intro t
    simpa only [row, CategoryTheory.Functor.map_comp] using hrow t
  refine ⟨x, ?_⟩
  have he : eI.hom ≫ fI = f := by
    simp only [fI, Iso.hom_inv_id_assoc]
  have h := congrArg G.map he
  simpa only [CategoryTheory.Functor.map_comp, hIz, comp_zero] using h.symm

end HodgeLean.Foundations.Program.G32Native

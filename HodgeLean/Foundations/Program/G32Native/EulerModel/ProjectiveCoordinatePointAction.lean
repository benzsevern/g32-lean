import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveCoordinateOpens
import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveCoordinateChartMaps

/-! # Actual homogeneous points under the specified coordinate permutation -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- A specified coordinate permutation retains a nonzero homogeneous representative. -/
theorem projectiveCoordinateVector_ne_zero (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (v : CoordinateSpace k) (hv : v ≠ 0) :
    v ∘ e.symm ≠ 0 := by
  intro hz
  apply hv
  funext j
  have hj := congrFun hz (e j)
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] using hj

#print axioms projectiveCoordinateVector_ne_zero
/-- The specified integral projective isomorphism retains the exact homogeneous parameters in every chart. -/
theorem projectiveCoordinateChartPoint_action (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (v : CoordinateSpace k)
    (j : Fin (k + 1)) (hj : v (e.symm j) ≠ 0) :
    chartIntegralProjAt v (e.symm j) hj ≫ (integralProjectiveCoordinateIso e).hom =
      chartIntegralProjAt (v ∘ e.symm) j hj := by
  unfold chartIntegralProjAt
  rw [Category.assoc, ← projectiveCoordinateChartMap_awayι, ← Category.assoc,
    ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  exact projectiveCoordinateChartMap_evaluation k e v j hj

#print axioms projectiveCoordinateChartPoint_action
/-- The integral projective coordinate isomorphism sends each actual homogeneous point to its specified permuted vector. -/
theorem projectiveCoordinateIntegralPoint_action (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (v : CoordinateSpace k) (hv : v ≠ 0) :
    chartIntegralProj v hv ≫ (integralProjectiveCoordinateIso e).hom =
      chartIntegralProj (v ∘ e.symm) (projectiveCoordinateVector_ne_zero k e v hv) := by
  let j := e (coordinateIndex v hv)
  have hj : v (e.symm j) ≠ 0 := by
    simpa only [j, Equiv.symm_apply_apply] using coordinateIndex_ne_zero v hv
  rw [chartIntegralProj_eq_chartIntegralProjAt v hv (e.symm j) hj,
    chartIntegralProj_eq_chartIntegralProjAt (v ∘ e.symm)
      (projectiveCoordinateVector_ne_zero k e v hv) j hj]
  exact projectiveCoordinateChartPoint_action k e v j hj

#print axioms projectiveCoordinateIntegralPoint_action
/-- The actual complex scheme isomorphism retains the specified homogeneous coordinate permutation on every point. -/
theorem complexProjectiveCoordinatePoint_action (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (v : CoordinateSpace k) (hv : v ≠ 0) :
    Point.map (complexProjectiveCoordinateIso e).hom (vectorToComplexPoint v hv) =
      vectorToComplexPoint (v ∘ e.symm) (projectiveCoordinateVector_ne_zero k e v hv) := by
  apply Over.OverMorphism.ext
  change vectorToProjectiveSpace v hv ≫ (complexProjectiveCoordinateIso e).hom.left =
    vectorToProjectiveSpace (v ∘ e.symm) (projectiveCoordinateVector_ne_zero k e v hv)
  apply pullback.hom_ext
  · rw [Category.assoc]
    change vectorToProjectiveSpace v hv ≫
      s2e_projectiveBaseChange (integralProjectiveCoordinateIso e).hom ≫
        pullback.fst _ _ = _
    rw [s2e_projectiveBaseChange, pullback.lift_fst]
    exact (vectorToProjectiveSpace_toBase v hv).trans
      (vectorToProjectiveSpace_toBase (v ∘ e.symm)
        (projectiveCoordinateVector_ne_zero k e v hv)).symm
  · rw [Category.assoc, complexProjectiveCoordinateIso_hom_snd, ← Category.assoc,
      vectorToProjectiveSpace_toProj, vectorToProjectiveSpace_toProj,
      projectiveCoordinateIntegralPoint_action]

#print axioms complexProjectiveCoordinatePoint_action
end HodgeLean.Foundations.Program.G32Native.EulerModel

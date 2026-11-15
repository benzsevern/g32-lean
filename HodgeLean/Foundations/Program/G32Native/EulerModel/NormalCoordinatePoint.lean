import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalProjectiveScheme
import HodgeLean.Foundations.Program.SchoenCycleProjectiveCoordinateSubspace

/-! # The actual coordinate point underlying the global normal zero -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Actual homogeneous projective points belong to a coordinate intersection exactly when those coordinates vanish. -/
theorem normal_coordinate_intersection_mem (k : ℕ) (T : Finset (Fin (k + 1)))
    (v : CoordinateSpace k) (hv : v ≠ 0) :
    (vectorToComplexPoint v hv).underlying ∈ (s2e_s2b_intersectionIdeal k T).support ↔
      ∀ j ∈ T, v j = 0 := by
  rw [s2e_intersection_support_coordinates]
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v hv
  have he (j : Fin (k + 1)) :
      (MvPolynomial.X j : MvPolynomial (Fin (k + 1)) (ULift.{0} ℤ)) ∈
        ((pullback.snd (terminal.from (Spec ↧ℂ))
          (terminal.from (Proj (UniversalGrading.{0} k))))
            (vectorToComplexPoint v hv).underlying).asHomogeneousIdeal.toIdeal ↔ v j = 0 := by
    change (MvPolynomial.X j : MvPolynomial (Fin (k + 1)) (ULift.{0} ℤ)) ∈
      ((vectorToProjectiveSpace v hv ≫ pullback.snd (terminal.from (Spec ↧ℂ))
        (terminal.from (Proj (UniversalGrading.{0} k)))) (IsLocalRing.closedPoint ℂ)).asHomogeneousIdeal.toIdeal ↔ _
    rw [vectorToProjectiveSpace_toProj, chartIntegralProj_eq_chartIntegralProjAt v hv i hi]
    exact not_iff_not.mp (s2e_projective_chart_mem_basicOpen v i j hi)
  exact forall_congr' (fun j => forall_congr' (fun _ => he j))

#print axioms normal_coordinate_intersection_mem
/-- The actual coordinate intersection complementary to the leading coordinate is precisely the global section zero. -/
theorem normal_coordinate_point_support (k : ℕ)
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) :
    (normalProjectiveSchemeHomeomorph k p).underlying ∈
      (s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).support ↔
        p = normalProjectiveBase k := by
  classical
  induction p using Projectivization.ind with
  | h v hv =>
    rw [normalProjectiveSchemeHomeomorph_mk, normal_coordinate_intersection_mem]
    have he : (∀ j ∈ (Finset.univ.erase (0 : Fin (k + 1))),
        normalHomogeneousCoordinates k v j = 0) ↔ v.2 = 0 := by
      constructor
      · intro h
        funext j
        exact h j.succ (by simp)
      · intro h j hj
        revert hj
        refine Fin.cases (by simp) (fun t _ => ?_) j
        exact congrFun h t
    rw [he, ← homogeneousNormalSection_zero_iff k v hv,
      ← projectiveNormalSectionVector_mk k v hv, projectiveNormalSectionVector_zero_iff]

#print axioms normal_coordinate_point_support
end HodgeLean.Foundations.Program.G32Native.EulerModel

import HodgeLean.Foundations.Program.SchoenCycleS2bDefs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- A homogeneous coordinate is nonzero exactly on its standard chart.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14. -/
theorem s2e_coordinatePoint_mem_chart {k : ℕ} (v : Fin (k + 1) → ℂ) (hv : v ≠ 0)
    (j : Fin (k + 1)) :
    (vectorToComplexPoint v hv).underlying ∈ projectiveSpaceBasicOpen k (MvPolynomial.X j) ↔
      v j ≠ 0 := by
  change IsLocalRing.closedPoint ℂ ∈
    (vectorToProjectiveSpace v hv ≫ Limits.pullback.snd
      (Limits.terminal.from (Spec ↧ℂ)) (Limits.terminal.from (Proj (UniversalGrading k)))) ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading k) (MvPolynomial.X j) ↔ _
  rw [vectorToProjectiveSpace_toProj, chartIntegralProj_preimage_basicOpen v hv
    (MvPolynomial.X j) zero_lt_one (MvPolynomial.isHomogeneous_X _ _), coordinateEvaluationHom_X]
  split_ifs with h <;> simp [h]

/-- The coordinate vectors with one zero coordinate are Zariski dense in the coordinate hyperplane.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14. -/
theorem s2e_coordinate_hyperplane_closure (k : ℕ) (j : Fin (k + 1)) :
    closure {p | ∃ (v : Fin (k + 1) → ℂ) (hv : v ≠ 0),
      v j = 0 ∧ p = (vectorToComplexPoint v hv).underlying} =
        (projectiveSpaceBasicOpen k (MvPolynomial.X j)).carrierᶜ := by
  let P := ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)
  let s : P ⟶ Spec ↧ℂ := ProjectiveSpace.toBase _ _
  letI : JacobsonSpace (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).left :=
    LocallyOfFiniteType.jacobsonSpace (ProjectiveSpace.toBase _ _)
  have heq : {p | ∃ (v : Fin (k + 1) → ℂ) (hv : v ≠ 0),
      v j = 0 ∧ p = (vectorToComplexPoint v hv).underlying} =
      (projectiveSpaceBasicOpen k (MvPolynomial.X j)).carrierᶜ ∩ closedPoints P := by
    ext p
    constructor
    · rintro ⟨v, hv, hz, rfl⟩
      refine ⟨?_, ?_⟩
      · change (vectorToComplexPoint v hv).underlying ∉ projectiveSpaceBasicOpen k (MvPolynomial.X j)
        rw [s2e_coordinatePoint_mem_chart]
        exact not_ne_iff.mpr hz
      · exact ((pointEquivClosedPoint s) ⟨(vectorToComplexPoint v hv).left, (vectorToComplexPoint v hv).w⟩).2
    · intro hp
      let q : AlgebraicGeometry.ComplexPoint (Over.mk s) :=
        Over.homMk (pointOfClosedPoint s p hp.2) (by simp)
      have hq : q.underlying = p := pointOfClosedPoint_apply s p hp.2 _
      obtain ⟨v, hvq⟩ := surjective_vectorToComplexPoint q
      have hvp : (vectorToComplexPoint v.val v.property).underlying = p := by
        change vectorToComplexPoint v.val v.property = q at hvq
        exact (congrArg AlgebraicGeometry.Point.underlying hvq).trans hq
      refine ⟨v.val, v.property, ?_, hvp.symm⟩
      have hp' : (vectorToComplexPoint v.val v.property).underlying ∉
          projectiveSpaceBasicOpen k (MvPolynomial.X j) := hvp ▸ hp.1
      simpa only [s2e_coordinatePoint_mem_chart, not_not] using hp'
  rw [heq]
  exact closure_inter_closedPoints (projectiveSpaceBasicOpen k (MvPolynomial.X j)).isOpen.isClosed_compl

end HodgeLean.Foundations.Program

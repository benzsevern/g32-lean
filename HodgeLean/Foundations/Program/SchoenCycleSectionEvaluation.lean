import HodgeLean.Foundations.Program.SchoenCycleStep1PointEvaluation

/-! # Scalar-compatible regular evaluation -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Stalk evaluation of a regular section agrees with its scalar-compatible point pullback.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_regular_evaluation_eq_pointEvaluation
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (p : ComplexPoint X)
    (hp : p.underlying ∈ U) (htop : ⊤ ≤ p.left ⁻¹ᵁ U) (s : Γ(X.left, U)) :
    Point.evaluate U s p = s2e_step1_pointEvaluation X U p htop s := by
  rw [Point.evaluate, dif_pos hp]
  have hg := Scheme.germ_stalkClosedPointTo p.left U hp
  change (X.left.presheaf.germ U (p.left (IsLocalRing.closedPoint ℂ)) hp ≫
    Scheme.stalkClosedPointTo p.left).hom s = _
  exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hg) s).trans (by rfl)

/-- Scalar multiplication of actual regular sections commutes with point evaluation.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_regular_evaluation_smul
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (p : ComplexPoint X)
    (c : ℂ) :
    letI := s2e_step1_sectionAlgebra X U
    ∀ s : Γ(X.left, U), Point.evaluate U (c • s) p = c • Point.evaluate U s p := by
  letI := s2e_step1_sectionAlgebra X U
  intro s
  by_cases hp : p.underlying ∈ U
  · have htop : ⊤ ≤ p.left ⁻¹ᵁ U := s2e_step1_point_preimage X p U hp
    rw [s2e_regular_evaluation_eq_pointEvaluation X U p hp htop,
      s2e_regular_evaluation_eq_pointEvaluation X U p hp htop]
    exact (s2e_step1_pointEvaluation X U p htop).toLinearMap.map_smul c s
  · simp only [Point.evaluate, dite_eq_right hp, smul_zero]

end HodgeLean.Foundations.Program

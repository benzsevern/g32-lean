import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartDomain

/-! # Detecting actual standard chart domains by homogeneous coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Membership of an actual homogeneous projective point in a retained standard affine open is exactly coordinate nonvanishing.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_standardProjectiveAffineOpen_mem_iff {n : ℕ} (v : CoordinateSpace n)
    (hv : v ≠ 0) (i : Fin (n + 1)) :
    (vectorToComplexPoint v hv).underlying ∈ (s2e_standardProjectiveAffineOpen i).1 ↔
      v i ≠ 0 := by
  letI : IsOpenImmersion (s2e_standardProjectiveChart i) :=
    s2e_standardProjectiveChart_isOpenImmersion i
  constructor
  · intro h
    change (vectorToComplexPoint v hv).underlying ∈ s2e_standardProjectiveChart i ''ᵁ ⊤ at h
    obtain ⟨x, hx, he⟩ := h
    let π := pullback.snd (terminal.from (Spec ↧ℂ))
      (terminal.from (Proj (UniversalGrading n)))
    have hm : (s2e_standardProjectiveChart i ≫ π) x ∈
        Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i) := by
      rw [s2e_standardProjectiveChart_toProj]
      rw [← Proj.opensRange_awayι (UniversalGrading n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ _) zero_lt_one]
      exact ⟨_, rfl⟩
    change π (s2e_standardProjectiveChart i x) ∈ _ at hm
    change s2e_standardProjectiveChart i x = (vectorToComplexPoint v hv).underlying at he
    rw [he] at hm
    change (vectorToProjectiveSpace v hv ≫ π) (IsLocalRing.closedPoint ℂ) ∈ _ at hm
    rw [vectorToProjectiveSpace_toProj] at hm
    obtain ⟨j, hj⟩ := exists_coordinate_ne_zero v hv
    rw [chartIntegralProj_eq_chartIntegralProjAt v hv j hj] at hm
    exact (s2e_projective_chart_mem_basicOpen v j i hj).mp hm
  · exact fun hi => s2e_standardProjectiveAffineOpen_mem v i hi

end HodgeLean.Foundations.Program

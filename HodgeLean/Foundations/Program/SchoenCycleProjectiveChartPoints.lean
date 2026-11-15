import HodgeLean.Foundations.Program.SchoenCycleProjectiveStandardChart

/-! # Coordinate points of the actual standard projective chart -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Evaluation of the actual base-changed projective chart at a homogeneous vector.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.7. -/
def s2e_standardProjectiveChartEvaluation {n : ℕ} (v : CoordinateSpace n)
    (i : Fin (n + 1)) (hi : v i ≠ 0) :
    ℂ ⊗[ℤ] HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) →ₐ[ℂ] ℂ :=
  AlgHom.liftEquiv ℤ ℂ _ ℂ (awayCoordinateEvaluation v i hi).toIntAlgHom

example {n : ℕ} (v : CoordinateSpace n) (i j : Fin (n + 1)) (hi : v i ≠ 0) :
    s2e_standardProjectiveChartEvaluation v i hi
      ((1 : ℂ) ⊗ₜ[ℤ] chartCoordinate i j) = v j / v i := by
  simp only [s2e_standardProjectiveChartEvaluation, AlgHom.liftEquiv_tmul, one_smul]
  exact s2e_projective_chartCoordinate_eval v i j hi

/-- The coordinate evaluation point maps to its actual homogeneous projective point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_standardProjectiveChartEvaluation_point {n : ℕ} (v : CoordinateSpace n)
    (i : Fin (n + 1)) (hi : v i ≠ 0) :
    Spec.map (CommRingCat.ofHom (s2e_standardProjectiveChartEvaluation v i hi).toRingHom) ≫
      s2e_standardProjectiveChart i =
      vectorToProjectiveSpace v (vector_ne_zero_of_coordinate v i hi) := by
  let A : Type := HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i)
  let φ := s2e_standardProjectiveChartEvaluation v i hi
  apply pullback.hom_ext
  · change (_ ≫ s2e_standardProjectiveChart i) ≫
      ProjectiveSpace.toBase _ _ = vectorToProjectiveSpace v
        (vector_ne_zero_of_coordinate v i hi) ≫ ProjectiveSpace.toBase _ _
    rw [Category.assoc, s2e_standardProjectiveChart_over, vectorToProjectiveSpace_toBase]
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    exact φ.commutes c
  · rw [Category.assoc, vectorToProjectiveSpace_toProj]
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      ((s2e_specTensorProductTerminalIso ℂ A).hom ≫
        pullback.lift _ _ _) ≫ pullback.snd _ _ = _
    rw [Category.assoc, pullback.lift_snd]
    rw [← Category.assoc (s2e_specTensorProductTerminalIso ℂ A).hom]
    rw [s2e_specTensorProductTerminalIso_hom_snd, ← Category.assoc, ← Spec.map_comp]
    rw [chartIntegralProj_eq_chartIntegralProjAt v (vector_ne_zero_of_coordinate v i hi) i hi]
    unfold chartIntegralProjAt
    congr 2
    ext r
    change φ ((1 : ℂ) ⊗ₜ[ℤ] r) = awayCoordinateEvaluation v i hi r
    simp [φ, s2e_standardProjectiveChartEvaluation]

/-- A nonzero homogeneous coordinate places the actual projective point in the corresponding affine chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_standardProjectiveAffineOpen_mem {n : ℕ} (v : CoordinateSpace n)
    (i : Fin (n + 1)) (hi : v i ≠ 0) :
    (vectorToComplexPoint v (vector_ne_zero_of_coordinate v i hi)).underlying ∈
      (s2e_standardProjectiveAffineOpen i).1 := by
  letI : IsOpenImmersion (s2e_standardProjectiveChart i) :=
    s2e_standardProjectiveChart_isOpenImmersion i
  let x := Spec.map (CommRingCat.ofHom (s2e_standardProjectiveChartEvaluation v i hi).toRingHom)
  have h := s2e_standardProjectiveChartEvaluation_point v i hi
  change vectorToProjectiveSpace v (vector_ne_zero_of_coordinate v i hi)
    (IsLocalRing.closedPoint ℂ) ∈ s2e_standardProjectiveChart i ''ᵁ ⊤
  rw [← h]
  exact ⟨x (IsLocalRing.closedPoint ℂ), trivial, rfl⟩

end HodgeLean.Foundations.Program

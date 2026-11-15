import HodgeLean.Foundations.Program.SchoenCycleProjectiveLinearSection
import HodgeLean.Foundations.Program.SchoenCycleOpenImmersionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartCoordinateComparison

/-! # Evaluation of actual projective chart sections -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open AlgebraicGeometry.ComplexPoint
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped TensorProduct BigOperators
namespace HodgeLean.Foundations.Program

/-- Actual projective section evaluation is scalar-compatible tensor-chart evaluation.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
theorem s2e_standardProjectiveSection_evaluate {n : ℕ}
    (v : CoordinateSpace n) (i : Fin (n + 1)) (hi : v i ≠ 0)
    (s : Γ(ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ),
      (s2e_standardProjectiveAffineOpen i).1)) :
    Point.evaluate (s2e_standardProjectiveAffineOpen i).1 s
      (vectorToComplexPoint v (vector_ne_zero_of_coordinate v i hi)) =
      (s2e_standardProjectiveChartEvaluation v i hi :
        (ℂ ⊗[ℤ] HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) : Type) →ₐ[ℂ] ℂ)
        ((s2e_baseChangedChartAlgEquiv ℂ i).symm
          (s2e_standardProjectiveSectionRingEquiv i s)) := by
  let A : Type := ℂ ⊗[ℤ] HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i)
  letI : IsOpenImmersion (s2e_standardProjectiveChart i) :=
    s2e_standardProjectiveChart_isOpenImmersion i
  let f : Over.mk (affineSpecStructureMap A) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)) :=
    Over.homMk (s2e_standardProjectiveChart i) (s2e_standardProjectiveChart_over i)
  letI : IsOpenImmersion f.left := s2e_standardProjectiveChart_isOpenImmersion i
  let φ := s2e_standardProjectiveChartEvaluation v i hi
  let z := (affineSpecEquiv A).symm φ
  have he : Point.map f z = vectorToComplexPoint v (vector_ne_zero_of_coordinate v i hi) := by
    apply Over.OverMorphism.ext
    exact s2e_standardProjectiveChartEvaluation_point v i hi
  rw [← he]
  let t := (s2e_standardProjectiveChart i).appIso ⊤ |>.hom s
  have hh := s2e_evaluate_openImmersion_appIso f ⊤ t z
  have ht : ((f.left.appIso ⊤).inv t) = s := by
    change ((f.left.appIso ⊤).inv ((f.left.appIso ⊤).hom s)) = s
    exact (f.left.appIso ⊤).hom_inv_id_apply s
  rw [ht] at hh
  change Point.evaluate (f.left ''ᵁ ⊤) s (Point.map f z) = _
  rw [hh, evaluate_affineSpecEquiv_symm_top]
  change φ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom t) =
    φ ((s2e_baseChangedChartAlgEquiv ℂ i).symm
      (s2e_baseChangedChartAlgEquiv ℂ i ((Scheme.ΓSpecIso (CommRingCat.of A)).hom t)))
  rw [AlgEquiv.symm_apply_apply]

/-- The actual regular linear section evaluates as the linear form divided by the chosen homogeneous coordinate.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_standardProjectiveLinearSection_evaluate
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k : ℕ) (hd : Module.finrank ℂ V = k + 1) (L : V →ₗ[ℂ] ℂ)
    (v : CoordinateSpace k) (i : Fin (k + 1)) (hi : v i ≠ 0) :
    Point.evaluate (s2e_standardProjectiveAffineOpen i).1
      (s2e_standardProjectiveLinearSection V k hd L i)
      (vectorToComplexPoint v (vector_ne_zero_of_coordinate v i hi)) =
      (v i)⁻¹ * L (∑ j, v j • Module.finBasisOfFinrankEq ℂ V hd j) := by
  rw [s2e_standardProjectiveSection_evaluate v i hi]
  unfold s2e_standardProjectiveLinearSection
  rw [RingEquiv.apply_symm_apply, s2e_baseChangedChartAlgEquiv_symm_linear]
  simp only [map_sum, map_mul, AlgHom.commutes, map_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he' : (s2e_standardProjectiveChartEvaluation v i hi :
      (ℂ ⊗[ℤ] HomogeneousLocalization.Away (UniversalGrading k) (MvPolynomial.X i) : Type) →ₐ[ℂ] ℂ)
      ((1 : ℂ) ⊗ₜ[ℤ] chartCoordinate i j) = v j / v i := by
    simp only [s2e_standardProjectiveChartEvaluation, AlgHom.liftEquiv_tmul, one_smul,
      RingHom.toIntAlgHom_apply]
    exact s2e_projective_chartCoordinate_eval v i j hi
  rw [he']
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

end HodgeLean.Foundations.Program

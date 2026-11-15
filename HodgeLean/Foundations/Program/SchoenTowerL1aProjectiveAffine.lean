import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective
import HodgeLean.Foundations.Program.SchoenTowerL1aHyperplaneAvoidance
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine neighborhoods of finite projective supports

The homogeneous coordinate calculation for affine neighborhoods of a finite
support. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace
open scoped BigOperators
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A degree-one projective basic open contains a coordinate point exactly when its linear form is nonzero.
Source: Hartshorne, Algebraic Geometry, II.2, homogeneous coordinates and projective basic opens. -/
theorem s2v_l1a_projective_linear_basicOpen
    {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0)
    (f : UniversalRing n) (hf : f ∈ UniversalGrading n 1) :
    chartIntegralProj v hv (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen (UniversalGrading n) f ↔ coordinateEvaluationHom v f ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v hv
  rw [chartIntegralProj_eq_chartIntegralProjAt v hv i hi]
  change IsLocalRing.closedPoint ℂ ∈
    (chartIntegralProjAt v i hi ⁻¹ᵁ Proj.basicOpen (UniversalGrading n) f) ↔ _
  rw [chartIntegralProjAt, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ (MvPolynomial.isHomogeneous_X _ i) zero_lt_one hf zero_lt_one]
  change (awayCoordinateEvaluation v i hi
    (HomogeneousLocalization.Away.isLocalizationElem (MvPolynomial.isHomogeneous_X _ i) hf)) ∉
      (IsLocalRing.closedPoint ℂ).asIdeal ↔ _
  rw [Subsingleton.elim (IsLocalRing.closedPoint ℂ) (⊥ : PrimeSpectrum ℂ)]
  change _ ≠ 0 ↔ _
  simp only [HomogeneousLocalization.Away.isLocalizationElem, pow_one]
  rw [awayCoordinateEvaluation_mk v i hi 1 f hf]
  rw [pow_one, mul_ne_zero_iff]
  exact and_iff_left (inv_ne_zero hi)

/-- Finitely many complex points of the integral projective model lie in one affine basic open.
Source: Hartshorne, Algebraic Geometry, II.2–3, hyperplane complements in projective space. -/
theorem s2v_l1a_integral_projective_finite_affine_neighborhood
    {n : ℕ} {κ : Type*} [Fintype κ]
    (p : κ → (Spec ↧ℂ ⟶ Proj (UniversalGrading n))) :
    ∃ U : (Proj (UniversalGrading n)).Opens, IsAffineOpen U ∧
      ∀ k, p k (IsLocalRing.closedPoint ℂ) ∈ U := by
  classical
  choose v hv using (fun k => surjective_chartIntegralProj (p k))
  obtain ⟨t, ht⟩ := s2v_l1a_finite_coordinate_avoidance (n + 1)
    (fun k => (v k).val) (fun k => (v k).property)
  let f : UniversalRing n := ∑ j : Fin (n + 1),
    MvPolynomial.C ((t : ULift ℤ) ^ j.val) * MvPolynomial.X j
  have hf : f ∈ UniversalGrading n 1 := by
    apply Submodule.sum_mem
    intro j _
    exact MvPolynomial.isHomogeneous_C_mul_X _ j
  have hnonzero (k : κ) : coordinateEvaluationHom (v k).val f ≠ 0 := by
    have he : coordinateEvaluationHom (v k).val f =
        ∑ j : Fin (n + 1), (v k).val j * (t : ℂ) ^ j.val := by
      simp only [f, map_sum, map_mul, map_pow, map_natCast, coordinateEvaluationHom_X]
      simp_rw [mul_comm]
    rw [he]
    exact ht k
  refine ⟨Proj.basicOpen (UniversalGrading n) f,
    Proj.isAffineOpen_basicOpen _ f hf zero_lt_one, ?_⟩
  intro k
  rw [← hv k]
  exact (s2v_l1a_projective_linear_basicOpen (v k).val (v k).property f hf).mpr
    (hnonzero k)

/-- A finite collection of complex points of a projective scheme lies in one affine open.
Source: Hartshorne, Algebraic Geometry, II.2–3, projective embeddings and hyperplane complements. -/
theorem s2v_l1a_projective_finite_affine_neighborhood
    (Z : Over (Spec ↧ℂ)) [IsProjective Z.hom]
    {κ : Type*} [Fintype κ] (p : κ → ComplexPoint Z) :
    ∃ U : Z.left.affineOpens, ∀ k, (p k).underlying ∈ U.1 := by
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := Z.hom)
  let : IsClosedImmersion P.immersion := P.isClosedImmersion
  let π : ProjectiveSpace (Fin (P.ambientDimension + 1)) (Spec ↧ℂ) ⟶
      Proj (UniversalGrading P.ambientDimension) :=
    CategoryTheory.Limits.pullback.snd _ _
  let : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom)
      (CategoryTheory.Limits.terminal.from (Proj (UniversalGrading P.ambientDimension))) :=
    { of_isPullback := fun pb h =>
        MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h }
  let : IsAffineHom π := MorphismProperty.pullback_snd (P := @IsAffineHom)
    (CategoryTheory.Limits.terminal.from (Spec ↧ℂ))
    (CategoryTheory.Limits.terminal.from (Proj (UniversalGrading P.ambientDimension)))
    (inferInstance : IsAffineHom (CategoryTheory.Limits.terminal.from (Spec ↧ℂ)))
  let g := P.immersion ≫ π
  obtain ⟨U, hU, hp⟩ := s2v_l1a_integral_projective_finite_affine_neighborhood
    (fun k => (p k).left ≫ g)
  refine ⟨⟨g ⁻¹ᵁ U, hU.preimage g⟩, ?_⟩
  intro k
  change g ((p k).left (IsLocalRing.closedPoint ℂ)) ∈ U
  exact (Scheme.Hom.comp_apply (p k).left g (IsLocalRing.closedPoint ℂ)) ▸ hp k

end HodgeLean.Foundations.Program

import HodgeLean.Adapters.GagaMaps
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

theorem s0_projective_ratios_eq
    {n : ℕ} (v w : CoordinateSpace n) (hv : v ≠ 0) (hw : w ≠ 0)
    (i : Fin (n + 1)) (hi : v i ≠ 0) (hwi : w i ≠ 0)
    (h : vectorToComplexPoint v hv = vectorToComplexPoint w hw) :
    ∀ j, v j / v i = w j / w i := by
  have he := congrArg (fun x ↦ x.left ≫ CategoryTheory.Limits.pullback.snd
    (CategoryTheory.Limits.terminal.from (Spec ↧ℂ))
    (CategoryTheory.Limits.terminal.from (Proj (UniversalGrading n)))) h
  change vectorToProjectiveSpace v hv ≫ _ = vectorToProjectiveSpace w hw ≫ _ at he
  rw [vectorToProjectiveSpace_toProj, vectorToProjectiveSpace_toProj,
    chartIntegralProj_eq_chartIntegralProjAt v hv i hi,
    chartIntegralProj_eq_chartIntegralProjAt w hw i hwi] at he
  unfold chartIntegralProjAt at he
  let e := Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
  letI : IsOpenImmersion e := by
    dsimp [e]
    exact Proj.instIsOpenImmersionAwayι (UniversalGrading n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
  have hf := (cancel_mono e).mp he
  have hh := Spec.map_injective hf
  intro j
  have hc := congrArg (fun f ↦ f.hom (chartCoordinate i j)) hh
  change awayCoordinateEvaluation v i hi (chartCoordinate i j) =
    awayCoordinateEvaluation w i hwi (chartCoordinate i j) at hc
  unfold chartCoordinate at hc
  rw [awayCoordinateEvaluation_mk (hr := MvPolynomial.isHomogeneous_X _ j),
    awayCoordinateEvaluation_mk (hr := MvPolynomial.isHomogeneous_X _ j),
    coordinateEvaluationHom_X, coordinateEvaluationHom_X, pow_one, pow_one] at hc
  exact hc

#print axioms s0_projective_ratios_eq

set_option backward.isDefEq.respectTransparency.types false in
theorem s0_integral_proj_coordinate_nonzero
    {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) (j : Fin (n + 1)) :
    chartIntegralProj v hv (⟨⊥, inferInstance⟩ : PrimeSpectrum ℂ) ∈
      Proj.basicOpen (UniversalGrading n) (MvPolynomial.X j) ↔ v j ≠ 0 := by
  let i := coordinateIndex v hv
  have hi : v i ≠ 0 := coordinateIndex_ne_zero v hv
  rw [chartIntegralProj_eq_chartIntegralProjAt v hv i hi]
  change (⟨⊥, inferInstance⟩ : PrimeSpectrum ℂ) ∈
    (Spec.map (CommRingCat.ofHom (awayCoordinateEvaluation v i hi)) ⁻¹ᵁ
      (Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ _) zero_lt_one ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading n) (MvPolynomial.X j))) ↔ _
  rw [Proj.awayι_preimage_basicOpen (𝒜 := UniversalGrading n)
    (f := MvPolynomial.X i) (g := MvPolynomial.X j) (MvPolynomial.isHomogeneous_X _ i) zero_lt_one
    (MvPolynomial.isHomogeneous_X _ j) zero_lt_one, SpecMap_preimage_basicOpen]
  change awayCoordinateEvaluation v i hi
    (HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X _ i) (MvPolynomial.isHomogeneous_X _ j)) ≠ 0 ↔ _
  dsimp only [HomogeneousLocalization.Away.isLocalizationElem]
  simp only [pow_one]
  rw [awayCoordinateEvaluation_mk (hr := MvPolynomial.isHomogeneous_X _ j),
    coordinateEvaluationHom_X, pow_one]
  simp [hi]

#print axioms s0_integral_proj_coordinate_nonzero

set_option backward.isDefEq.respectTransparency.types false in
theorem s0_projective_coordinate_map_injective {n : ℕ} :
    Function.Injective (projectivizationToComplexPoint (n := n)) := by
  intro x y h
  induction x using Projectivization.ind with
  | h v hv =>
    induction y using Projectivization.ind with
    | h w hw =>
      change vectorToComplexPoint v hv = vectorToComplexPoint w hw at h
      let i := coordinateIndex v hv
      have hi : v i ≠ 0 := coordinateIndex_ne_zero v hv
      have hq : chartIntegralProj v hv = chartIntegralProj w hw := by
        have hh := congrArg (fun z ↦ z.left ≫ CategoryTheory.Limits.pullback.snd
          (CategoryTheory.Limits.terminal.from (Spec ↧ℂ))
          (CategoryTheory.Limits.terminal.from (Proj (UniversalGrading n)))) h
        change vectorToProjectiveSpace v hv ≫ _ = vectorToProjectiveSpace w hw ≫ _ at hh
        simpa only [vectorToProjectiveSpace_toProj] using hh
      have hwi : w i ≠ 0 := by
        have hm := (s0_integral_proj_coordinate_nonzero v hv i).mpr hi
        rw [hq] at hm
        exact (s0_integral_proj_coordinate_nonzero w hw i).mp hm
      have hr := s0_projective_ratios_eq v w hv hw i hi hwi h
      apply (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mpr
      refine ⟨v i / w i, ?_⟩
      funext j
      change (v i / w i) * w j = v j
      rw [div_mul_eq_mul_div]
      apply (div_eq_iff hwi).mpr
      exact (mul_comm _ _).trans ((div_eq_div_iff hi hwi).mp (hr j)).symm

#print axioms s0_projective_coordinate_map_injective

/-- The homogeneous-coordinate comparison with scheme-theoretic complex points.
Source: Hartshorne, Algebraic Geometry, II.2.5, standard projective affine charts. -/
def s0_projective_coordinate_homeomorph (n : ℕ) :
    Projectivization ℂ (CoordinateSpace n) ≃ₜ
      AlgebraicGeometry.ComplexPoint
        (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) :=
  let e := Equiv.ofBijective (projectivizationToComplexPoint (n := n))
    ⟨s0_projective_coordinate_map_injective, surjective_projectivizationToComplexPoint⟩
  (show Continuous e from continuous_projectivizationToComplexPoint).homeoOfEquivCompactToT2

example (n : ℕ) :
    (s0_projective_coordinate_homeomorph n : _ → _) = projectivizationToComplexPoint := rfl

#print axioms s0_projective_coordinate_homeomorph

end HodgeLean.Foundations.Program

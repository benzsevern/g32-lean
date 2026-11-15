import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective
import Mathlib.Topology.IsLocalHomeomorph

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped LinearAlgebra.Projectivization
namespace HodgeLean.Foundations.Program

/-- Nonzero vectors with one coordinate determine the same line.
Source: Hartshorne, Algebraic Geometry, I.2, projective coordinates. -/
theorem s2e_c11_one_coordinate_line_unique
    (p q : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace 0)) : p = q := by
  induction p using Projectivization.ind with
  | _ v hv =>
    induction q using Projectivization.ind with
    | _ w hw =>
      have hv0 : v 0 ≠ 0 := by
        intro h
        apply hv
        funext i
        exact (congrArg v (Fin.eq_zero i)).trans h
      have hw0 : w 0 ≠ 0 := by
        intro h
        apply hw
        funext i
        exact (congrArg w (Fin.eq_zero i)).trans h
      apply (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).2
      refine ⟨v 0 / w 0, ?_⟩
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact div_mul_cancel₀ (v 0) hw0

/-- Local homeomorphisms can be checked on open target neighbourhoods.
Source: Mathlib, IsLocalHomeomorphOn.of_comp_right and open subtype inclusions. -/
theorem s2e_c11_local_homeomorph_of_target_opens
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    (h : ∀ y : Y, ∃ U : Set Y, y ∈ U ∧ IsOpen U ∧
      IsLocalHomeomorph (U.restrictPreimage f)) : IsLocalHomeomorph f := by
  intro x
  obtain ⟨U, hx, hU, hloc⟩ := h (f x)
  have hsrc := (hU.preimage hf).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have htgt := hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hcomp : IsLocalHomeomorph
      (f ∘ (Subtype.val : (f ⁻¹' U) → X)) := htgt.comp hloc
  have hlocal := (hcomp.isLocalHomeomorphOn (s := Set.univ)).of_comp_right
    (hsrc.isLocalHomeomorphOn (s := Set.univ))
  exact hlocal x ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩

/-- Equality in a fixed standard chart determines all normalized coordinates.
Source: Hartshorne, Algebraic Geometry, II.2, affine projective charts. -/
theorem s2e_c11_same_chart_ratios
    {n : ℕ} (v w : ComplexProjectiveSpace.CoordinateSpace n)
    (i : Fin (n + 1)) (hv : v i ≠ 0) (hw : w i ≠ 0)
    (h : ComplexProjectiveSpace.chartIntegralProjAt v i hv =
      ComplexProjectiveSpace.chartIntegralProjAt w i hw) :
    ∀ j, v j * (v i)⁻¹ = w j * (w i)⁻¹ := by
  open ComplexProjectiveSpace in
  have he : awayCoordinateEvaluation v i hv = awayCoordinateEvaluation w i hw := by
    letI : IsOpenImmersion (Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ _) zero_lt_one) :=
      Proj.instIsOpenImmersionAwayι _ _ _ _
    have hc : Spec.map (CommRingCat.ofHom (awayCoordinateEvaluation v i hv)) =
        Spec.map (CommRingCat.ofHom (awayCoordinateEvaluation w i hw)) :=
      (cancel_mono (Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ _) zero_lt_one)).mp h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hc)
  intro j
  have hj := DFunLike.congr_fun he (ComplexProjectiveSpace.chartCoordinate i j)
  change ComplexProjectiveSpace.awayCoordinateEvaluation v i hv
      (HomogeneousLocalization.Away.mk (ComplexProjectiveSpace.UniversalGrading n)
        (MvPolynomial.isHomogeneous_X _ i) 1 (MvPolynomial.X j) _) =
    ComplexProjectiveSpace.awayCoordinateEvaluation w i hw
      (HomogeneousLocalization.Away.mk (ComplexProjectiveSpace.UniversalGrading n)
        (MvPolynomial.isHomogeneous_X _ i) 1 (MvPolynomial.X j) _) at hj
  rw [ComplexProjectiveSpace.awayCoordinateEvaluation_mk (hr := by
        simpa using MvPolynomial.isHomogeneous_X (ULift ℤ) j),
      ComplexProjectiveSpace.awayCoordinateEvaluation_mk (hr := by
        simpa using MvPolynomial.isHomogeneous_X (ULift ℤ) j)] at hj
  simpa only [ComplexProjectiveSpace.coordinateEvaluationHom_X, pow_one] using hj

/-- A homogeneous coordinate is nonzero exactly on its standard open chart.
Source: Hartshorne, Algebraic Geometry, II.2, standard projective basic opens. -/
theorem s2e_c11_chart_coordinate_membership
    {n : ℕ} (v : ComplexProjectiveSpace.CoordinateSpace n)
    (i j : Fin (n + 1)) (hi : v i ≠ 0) :
    ComplexProjectiveSpace.chartIntegralProjAt v i hi (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen (ComplexProjectiveSpace.UniversalGrading n) (MvPolynomial.X j) ↔
      v j ≠ 0 := by
  open ComplexProjectiveSpace in
  change (Spec.map (CommRingCat.ofHom (awayCoordinateEvaluation v i hi)))
    (IsLocalRing.closedPoint ℂ) ∈
      (Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ _) zero_lt_one) ⁻¹ᵁ
          Proj.basicOpen (UniversalGrading n) (MvPolynomial.X j) ↔ _
  have hop := Proj.awayι_preimage_basicOpen
    (𝒜 := ComplexProjectiveSpace.UniversalGrading n)
    (f := (MvPolynomial.X i : ComplexProjectiveSpace.UniversalRing n))
    (g := (MvPolynomial.X j : ComplexProjectiveSpace.UniversalRing n))
    (show MvPolynomial.X i ∈ ComplexProjectiveSpace.UniversalGrading n 1 from
      MvPolynomial.isHomogeneous_X _ i) zero_lt_one
    (show MvPolynomial.X j ∈ ComplexProjectiveSpace.UniversalGrading n 1 from
      MvPolynomial.isHomogeneous_X _ j) zero_lt_one
  rw [hop]
  change (ComplexProjectiveSpace.awayCoordinateEvaluation v i hi)
      (HomogeneousLocalization.Away.isLocalizationElem
        (MvPolynomial.isHomogeneous_X (ULift ℤ) i)
        (MvPolynomial.isHomogeneous_X (ULift ℤ) j)) ∉
    (IsLocalRing.closedPoint ℂ).asIdeal ↔ _
  rw [show (IsLocalRing.closedPoint ℂ).asIdeal = ⊥ from IsLocalRing.maximalIdeal_eq_bot]
  simp only [HomogeneousLocalization.Away.isLocalizationElem, pow_one,
    ComplexProjectiveSpace.awayCoordinateEvaluation_mk (hr := by
      simpa using MvPolynomial.isHomogeneous_X (ULift ℤ) j),
    ComplexProjectiveSpace.coordinateEvaluationHom_X, Ideal.mem_bot,
    mul_ne_zero_iff]
  exact and_iff_left (inv_ne_zero hi)

end HodgeLean.Foundations.Program

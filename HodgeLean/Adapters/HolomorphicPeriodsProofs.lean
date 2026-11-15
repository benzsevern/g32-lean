import HodgeLean.Adapters.HolomorphicPeriodsDefs
import HodgeLean.Adapters.HolomorphicFormValues
import HodgeLean.Adapters.HolomorphicOneForms
import HodgeLean.Adapters.DegreeOneLattice

/-! # Proof obligations for periods of holomorphic `1`-forms as curve integrals

One obligation per statement of `HodgeLean.Adapters.HolomorphicPeriods`. All seven are proved, by two parallel provers. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

theorem spec_abelianLatticeLoop_eq_complexExponential_segment_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (l : abelianPeriodLattice X)
    (t : unitInterval) :
    abelianLatticeLoop X l ((t : ℝ) : UnitAddCircle) =
      (complexExponential X (dim X.left)
        (Path.segment (0 : Fin (dim X.left) → ℂ) (l : Fin (dim X.left) → ℂ) t)).toMul := by
  rw [Path.segment_apply, AffineMap.lineMap_apply, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero,
    complexExponential_smul]
  rfl

theorem spec_curveIntegral_segment_fderiv_aux {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (f : E → F)
    (hf : ContDiff ℂ 1 f) (a b : E) :
    ∫ᶜ x in Path.segment a b, fderiv ℂ f x = f b - f a := by
  rw [curveIntegral_segment]
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ f (AffineMap.lineMap a b s))
      (fderiv ℂ f (AffineMap.lineMap a b t) (b - a)) t := by
    intro t
    have h1 := ((hf.differentiable one_ne_zero (AffineMap.lineMap a b t)).hasFDerivAt).restrictScalars ℝ
    exact h1.comp_hasDerivAt t (AffineMap.hasDerivAt_lineMap (a := a) (b := b) (x := t))
  have hc : Continuous fun t : ℝ ↦ fderiv ℂ f (AffineMap.lineMap a b t) (b - a) :=
    ((hf.continuous_fderiv one_ne_zero).comp (AffineMap.lineMap_continuous)).clm_apply continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    (hc.intervalIntegrable _ _)]
  simp

theorem spec_curveIntegral_segment_add_fderiv_of_eq_aux {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (ω : E → E →L[ℂ] F) (hω : Continuous ω) (f : E → F) (hf : ContDiff ℂ 1 f) (a b : E)
    (hab : f b = f a) :
    ∫ᶜ x in Path.segment a b, (ω x + fderiv ℂ f x) = ∫ᶜ x in Path.segment a b, ω x := by
  have hl : Continuous fun t : ℝ ↦ AffineMap.lineMap a b t := AffineMap.lineMap_continuous
  have h1 : CurveIntegrable ω (Path.segment a b) := curveIntegrable_segment.2
    (((hω.comp hl).clm_apply continuous_const).intervalIntegrable _ _)
  have h2 : CurveIntegrable (fderiv ℂ f) (Path.segment a b) := curveIntegrable_segment.2
    ((((hf.continuous_fderiv one_ne_zero).comp hl).clm_apply continuous_const).intervalIntegrable _ _)
  rw [curveIntegral_fun_add h1 h2, spec_curveIntegral_segment_fderiv_aux f hf a b, hab, sub_self, add_zero]

theorem spec_curveIntegral_segment_expPullback_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (a b : Fin d → ℂ) :
    ∫ᶜ x in Path.segment a b, expPullback X d θ x = expPullback X d θ 0 (b - a) := by
  simp_rw [spec_expPullback_eq_expPullback_zero X d θ]
  exact curveIntegral_segment_const _ a b

theorem reDImForm_eq_smulRight : reDImForm =
    (Complex.ofRealCLM.comp Complex.reCLM).smulRight (Complex.ofRealCLM.comp Complex.imCLM) := by
  ext z v; simp [reDImForm]

theorem fderiv_reDImForm_apply (z u v : ℂ) :
    fderiv ℝ reDImForm z u v = (u.re : ℂ) * (v.im : ℂ) := by
  rw [reDImForm_eq_smulRight, ContinuousLinearMap.fderiv]
  simp

theorem spec_fderiv_reDImForm_not_symmetric_aux :
    fderiv ℝ reDImForm 0 1 Complex.I ≠ fderiv ℝ reDImForm 0 Complex.I 1 := by
  rw [fderiv_reDImForm_apply, fderiv_reDImForm_apply]; simp

theorem continuous_reDImForm : Continuous reDImForm := by
  rw [reDImForm_eq_smulRight]; exact ContinuousLinearMap.continuous _

theorem curveIntegrable_reDImForm_segment (a b : ℂ) :
    CurveIntegrable reDImForm (Path.segment a b) := by
  rw [curveIntegrable_segment]
  exact Continuous.intervalIntegrable
    ((continuous_reDImForm.comp AffineMap.lineMap_continuous).clm_apply continuous_const) _ _

theorem spec_curveIntegral_reDImForm_staircases_aux :
    rightUpPath.Homotopic upRightPath ∧
      ∫ᶜ x in rightUpPath, reDImForm x = 1 ∧ ∫ᶜ x in upRightPath, reDImForm x = 0 := by
  refine ⟨SimplyConnectedSpace.paths_homotopic _ _, ?_, ?_⟩
  · rw [rightUpPath, curveIntegral_trans (curveIntegrable_reDImForm_segment _ _)
      (curveIntegrable_reDImForm_segment _ _), curveIntegral_segment, curveIntegral_segment]
    simp [reDImForm, AffineMap.lineMap_apply]
  · rw [upRightPath, curveIntegral_trans (curveIntegrable_reDImForm_segment _ _)
      (curveIntegrable_reDImForm_segment _ _), curveIntegral_segment, curveIntegral_segment]
    simp [reDImForm, AffineMap.lineMap_apply]

theorem spec_comap_hodgeFiltration_one_le_of_periods_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (c : ℂ)
    (hper : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
        complexAbelianPeriod X ω l = c * ∫ᶜ x in Path.segment 0 (l : Fin (dim X.left) → ℂ),
          expPullback X (dim X.left) (cycleOneForm X z) x) :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  refine (spec_comap_hodgeFiltration_one_le_iff X).2 fun z ω hω => ?_
  let a := expPullback X (dim X.left) (cycleOneForm X z) 0
  refine ⟨c • (a.restrictScalars ℝ : (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℂ), fun v => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
    ring
  · funext l
    have h4 := spec_curveIntegral_segment_expPullback_aux X (dim X.left) (cycleOneForm X z) 0
      (l : Fin (dim X.left) → ℂ)
    rw [sub_zero] at h4
    rw [hper z ω hω l]
    exact (congrArg (c * ·) h4).symm

end HodgeLean.Adapters

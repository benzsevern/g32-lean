import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8CurvatureDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import Mathlib.Analysis.Analytic.Polynomial
import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.AnalyticLeftInverse
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian7Proofs
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open Filter Set Topology MeasureTheory
open scoped ContDiff
namespace HodgeLean.Adapters

/-- Differentiating a local left inverse makes the chart differential injective.
Source: the chain rule and the closed-immersion local section-lifting theorem. -/
theorem bh8_injective_fderiv_closedImmersion
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y) :
    Function.Injective (fderiv ℂ (inclusionInComplexCharts X Y i m d z)
      (localChart Y m z z)) := by
  obtain ⟨P, hP⟩ := exists_leftInverse_fderiv_inclusionInComplexCharts X Y i m d z
  intro v w hvw
  have hv := congrArg (fun T : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) ↦ T v) hP
  have hw := congrArg (fun T : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) ↦ T w) hP
  exact hv.symm.trans ((congrArg P hvw).trans hw)

/-- A normalized homogeneous lift with injective differential is immersive modulo its radial line.
Source: Griffiths--Harris, Chapter 0, standard affine coordinates on projective space. -/
theorem bh8_radial_immersion_of_normalized
    {n N : ℕ} {s : (Fin n → ℂ) → (Fin (N + 1) → ℂ)} {z : Fin n → ℂ}
    (hs : DifferentiableAt ℂ s z) (k : Fin (N + 1))
    (hk : ∀ᶠ w in 𝓝 z, s w k = 1)
    (hi : Function.Injective (fderiv ℂ s z))
    (v : Fin n → ℂ) (c : ℂ) (h : fderiv ℂ s z v = c • s z) : v = 0 := by
  have hd : fderiv ℂ (fun w ↦ s w k) z = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hk, fderiv_const_apply]
  have hdv : (fderiv ℂ s z v) k = 0 := by
    have he := congrArg (fun T : (Fin n → ℂ) →L[ℂ] ℂ ↦ T v) hd
    rw [fderiv_apply hs] at he
    exact he
  have hc : c = 0 := by
    have he := congrFun h k
    simpa only [hdv, Pi.smul_apply, smul_eq_mul, hk.self_of_nhds, mul_one] using he.symm
  apply hi
  simpa only [hc, zero_smul, map_zero] using h

/-- Two analytic nonvanishing lifts that are locally proportional differ by an analytic unit.
Source: Griffiths--Harris, Chapter 0, transition functions in homogeneous coordinates. -/
theorem bh8_analytic_unit_of_proportional
    {n N : ℕ} {s t : (Fin n → ℂ) → (Fin (N + 1) → ℂ)} {z : Fin n → ℂ}
    (hs : AnalyticAt ℂ s z) (ht : AnalyticAt ℂ t z)
    (hs0 : s z ≠ 0) (ht0 : t z ≠ 0)
    (h : ∀ᶠ w in 𝓝 z, ∃ c : ℂ, t w = c • s w) :
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, t w = u w • s w := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, s z k ≠ 0 := by
    by_contra hn
    apply hs0
    ext k
    exact not_not.mp (fun hk ↦ hn ⟨k, hk⟩)
  have hsk : AnalyticAt ℂ (fun w ↦ s w k) z :=
    analyticAt_pi_iff.mp hs k
  have htk : AnalyticAt ℂ (fun w ↦ t w k) z :=
    analyticAt_pi_iff.mp ht k
  have he : ∀ᶠ w in 𝓝 z, t w = (t w k / s w k) • s w := by
    filter_upwards [h, hsk.continuousAt.eventually_ne hk] with w hw hkw
    obtain ⟨c, hc⟩ := hw
    rw [hc]
    simp only [Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hkw]
  refine ⟨fun w ↦ t w k / s w k, htk.div hsk hk, ?_, he⟩
  intro hu
  change t z k / s z k = 0 at hu
  apply ht0
  exact he.self_of_nhds.trans (by rw [hu, zero_smul])

open scoped Manifold in
/-- The uniformization is analytic in the smooth coordinate chart centered at its value.
Source: Birkenhake--Lange, section 1.1; `spec_contMDiff_complexExponential`. -/
theorem bh8_analyticAt_abelianExp_chart (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (z : Fin (dim X.left) → ℂ) :
    AnalyticAt ℂ (fun w ↦ localChart X (dim X.left) (abelianExp X z) (abelianExp X w)) z := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  have h := (spec_contMDiff_complexExponential X (dim X.left) z)
  rw [contMDiffAt_iff] at h
  have hc := h.2
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    Function.comp_id, extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp,
    Set.range_id, id_eq] at hc
  exact (contDiffWithinAt_univ.mp hc).analyticAt

/-- Regular functions on an algebraic open pull back to analytic functions on the universal cover.
Source: regular-function evaluation in smooth coordinates and Birkenhake--Lange, section 1.1. -/
theorem bh8_analyticAt_evaluate_abelianExp
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (V : X.left.Opens) (s : Γ(X.left, V))
    (z : Fin (dim X.left) → ℂ) (hz : abelianExp X z ∈ Point.overOpen V) :
    AnalyticAt ℂ (fun w ↦ Point.evaluate V s (abelianExp X w)) z := by
  let e := localChart X (dim X.left) (abelianExp X z)
  have hzE : abelianExp X z ∈ e.source := mem_localChart_source X _ _
  have ha := analyticAt_localChart_symm_evaluate X (dim X.left) (abelianExp X z)
    (e.map_source hzE) V s (by rw [e.left_inv hzE]; exact hz)
  have hc := ha.comp (f := fun w ↦ e (abelianExp X w))
    (bh8_analyticAt_abelianExp_chart X z)
  apply hc.congr
  have he : ∀ᶠ w in 𝓝 z, abelianExp X w ∈ e.source :=
    (continuous_abelianExp X).continuousAt (e.open_source.mem_nhds hzE)
  filter_upwards [he] with w hw
  exact congrArg (Point.evaluate V s) (e.left_inv hw)

/-- Global regular functions on affine space are analytic in the usual vector coordinates.
Source: polynomial evaluation and the affine-space global-sections isomorphism. -/
theorem bh8_analyticAt_affine_evaluate_top {n : ℕ}
    (s : Γ(complexAffineSpace (Fin n), ⊤)) (z : Fin n → ℂ) :
    AnalyticAt ℂ (fun v ↦ Point.evaluate ⊤ s ((affineSpaceEquiv (Fin n)).symm v)) z := by
  simpa only [evaluate_affineSpaceEquiv_symm_top, ContinuousLinearMap.id_apply] using
    AnalyticOnNhd.eval_continuousLinearMap
      (ContinuousLinearMap.id ℂ (Fin n → ℂ)) (affineGlobalPolynomial s) z (mem_univ z)

/-- Local regular functions on affine space are analytic wherever they are defined.
Source: localization on principal affine opens expresses regular functions as polynomial ratios. -/
theorem bh8_analyticAt_affine_evaluate {n : ℕ}
    (V : (complexAffineSpace (Fin n)).Opens) (s : Γ(complexAffineSpace (Fin n), V))
    (z : Fin n → ℂ) (hz : (affineSpaceEquiv (Fin n)).symm z ∈ Point.overOpen V) :
    AnalyticAt ℂ (fun v ↦ Point.evaluate V s ((affineSpaceEquiv (Fin n)).symm v)) z := by
  let Y := complexAffineSpace (Fin n)
  let e := (affineSpaceEquiv (Fin n)).symm
  obtain ⟨f, hfV, hzf⟩ := (isAffineOpen_top Y).exists_basicOpen_le
    ⟨(e z).underlying, hz⟩ trivial
  let t := Y.presheaf.map (homOfLE hfV).op s
  obtain ⟨k, a, ha⟩ := Point.exists_evaluate_basicOpen_eq_div
    (X := Over.mk (Y ↘ Spec ↧ℂ)) (isAffineOpen_top Y) f t
  have hf0 : Point.evaluate ⊤ f (e z) ≠ 0 :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := Over.mk (Y ↘ Spec ↧ℂ)) (U := ⊤) f (e z) trivial).mp hzf
  have hrat := (bh8_analyticAt_affine_evaluate_top a z).div
    ((bh8_analyticAt_affine_evaluate_top f z).pow k) (pow_ne_zero k hf0)
  apply hrat.congr
  have hn : ∀ᶠ v in 𝓝 z, e v ∈ Point.overOpen (Y.basicOpen f) :=
    (isOpen_affineSpaceEquiv_symm_preimage_overOpen_basicOpen f).mem_nhds hzf
  filter_upwards [hn] with v hv
  exact ((Point.evaluate_res hfV s (e v) hv).trans (ha (e v) hv)).symm

attribute [local instance] MvPolynomial.gradedAlgebra in
open ComplexProjectiveSpace in
/-- Equal scheme-theoretic projective points have proportional homogeneous coordinates.
Source: equality of coordinate ratios on a common standard projective chart. -/
theorem bh8_projective_coordinates_proportional {N : ℕ}
    (v w : CoordinateSpace N) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : vectorToComplexPoint v hv = vectorToComplexPoint w hw) :
    ∃ c : ℂ, w = c • v := by
  let i := coordinateIndex v hv
  have hvi : v i ≠ 0 := coordinateIndex_ne_zero v hv
  have hp : chartIntegralProj v hv = chartIntegralProj w hw := by
    have he := congrArg (fun z ↦ z.left ≫ Limits.pullback.snd
      (Limits.terminal.from (Spec ↧ℂ))
      (Limits.terminal.from (Proj (UniversalGrading N)))) h
    change vectorToProjectiveSpace v hv ≫ _ = vectorToProjectiveSpace w hw ≫ _ at he
    simpa only [vectorToProjectiveSpace_toProj] using he
  have hwi : w i ≠ 0 := by
    intro hwi
    have he := congrArg (fun f : Spec ↧ℂ ⟶ Proj (UniversalGrading N) ↦
      f ⁻¹ᵁ Proj.basicOpen (UniversalGrading N) (MvPolynomial.X i)) hp
    rw [chartIntegralProj_preimage_basicOpen v hv _ zero_lt_one
        (MvPolynomial.isHomogeneous_X _ _),
      chartIntegralProj_preimage_basicOpen w hw _ zero_lt_one
        (MvPolynomial.isHomogeneous_X _ _)] at he
    simp only [coordinateEvaluationHom_X, ite_eq_right hvi, ite_eq_left hwi] at he
    have hf := congrArg (fun U : (Spec ↧ℂ).Opens ↦ IsLocalRing.closedPoint ℂ ∈ U) he
    exact (Eq.mp hf trivial)
  rw [chartIntegralProj_eq_chartIntegralProjAt v hv i hvi,
    chartIntegralProj_eq_chartIntegralProjAt w hw i hwi] at hp
  unfold chartIntegralProjAt at hp
  let : IsOpenImmersion (Proj.awayι (UniversalGrading N) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ _) zero_lt_one) :=
    Proj.instIsOpenImmersionAwayι _ _ _ _
  have he := Spec.map_injective ((cancel_mono
    (Proj.awayι (UniversalGrading N) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ _) zero_lt_one)).mp hp)
  refine ⟨w i / v i, ?_⟩
  ext j
  have hj := congrArg (fun f ↦ f.hom (chartCoordinate i j)) he
  change awayCoordinateEvaluation v i hvi (chartCoordinate i j) =
    awayCoordinateEvaluation w i hwi (chartCoordinate i j) at hj
  unfold chartCoordinate at hj
  rw [awayCoordinateEvaluation_mk (hr := MvPolynomial.isHomogeneous_X (ULift ℤ) j),
    awayCoordinateEvaluation_mk (hr := MvPolynomial.isHomogeneous_X (ULift ℤ) j)] at hj
  simp only [coordinateEvaluationHom_X, pow_one] at hj
  change w j = (w i / v i) * v j
  field_simp at hj ⊢
  linear_combination -hj

open ComplexProjectiveSpace in
/-- Analytic representatives of the same projective scheme point differ by an analytic unit.
Source: homogeneous coordinate ratios on standard projective charts. -/
theorem bh8_projective_lift_transition
    {n N : ℕ} {s t : (Fin n → ℂ) → CoordinateSpace N} {z : Fin n → ℂ}
    (hs : AnalyticAt ℂ s z) (ht : AnalyticAt ℂ t z)
    (hs0 : s z ≠ 0) (ht0 : t z ≠ 0)
    (he : ∀ᶠ w in 𝓝 z, ∃ (hsw : s w ≠ 0) (htw : t w ≠ 0),
      vectorToComplexPoint (s w) hsw = vectorToComplexPoint (t w) htw) :
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, t w = u w • s w := by
  apply bh8_analytic_unit_of_proportional hs ht hs0 ht0
  filter_upwards [he] with w hw
  obtain ⟨hsw, htw, hw⟩ := hw
  exact bh8_projective_coordinates_proportional (s w) (t w) hsw htw hw

/-- A zero-dimensional vector space has a constant nonzero homogeneous lift.
Source: the unique map to projective zero-space. -/
theorem bh8_projectiveAtlas_of_zero_dimension
    (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ)) (hn : n = 0) :
    Nonempty (bh8_ProjectiveAtlas n Λ) := by
  subst n
  refine ⟨{ N := 0
            U := fun _ ↦ univ
            s := fun _ _ _ ↦ 1
            open_U := fun _ ↦ isOpen_univ
            anchor := fun _ ↦ mem_univ _
            analytic := fun _ _ _ ↦ analyticAt_const
            nonzero := ?_
            immersion := ?_
            transition := ?_ }⟩
  · intro p z hz he
    exact one_ne_zero (congrFun he 0)
  · intro p z hz v c he
    exact Subsingleton.elim v 0
  · intro l p q z hz hzl
    refine ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, ?_⟩
    filter_upwards with w
    exact (one_smul ℂ (fun _ : Fin 1 ↦ (1 : ℂ))).symm

open scoped Manifold in
/-- The uniformization has injective differential in the smooth chart centered at its value.
Source: Birkenhake--Lange, section 1.1; `spec_isInvertible_mfderiv_complexExponential`. -/
theorem bh8_injective_fderiv_abelianExp_chart (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (z : Fin (dim X.left) → ℂ) :
    Function.Injective (fderiv ℂ
      (fun w ↦ localChart X (dim X.left) (abelianExp X z) (abelianExp X w)) z) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  have hi := spec_isInvertible_mfderiv_complexExponential X (dim X.left) z
  have hd := spec_mdifferentiable_complexExponential X (dim X.left) z
  rw [hd.mfderiv_abuse] at hi
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.comp_id,
    extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp,
    Set.range_id, id_eq, fderivWithin_univ] at hi
  obtain ⟨e, he⟩ := hi
  change e.toContinuousLinearMap = fderiv ℂ
    (fun w ↦ localChart X (dim X.left) (abelianExp X z) (abelianExp X w)) z at he
  rw [← he]
  exact e.injective

attribute [local instance] MvPolynomial.gradedAlgebra in
open ComplexProjectiveSpace in
/-- Pulling back the standard projective coordinate ratios gives analytic normalized vectors.
Source: Griffiths--Harris, Chapter 0, standard affine charts of projective space. -/
theorem bh8_analytic_normalized_projective_coordinates
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] {N : ℕ}
    (q : X.left ⟶ Proj (UniversalGrading N)) (i : Fin (N + 1))
    (z : Fin (dim X.left) → ℂ)
    (hz : abelianExp X z ∈ Point.overOpen
      (q ⁻¹ᵁ Proj.basicOpen (UniversalGrading N) (MvPolynomial.X i))) :
    let U := Proj.basicOpen (UniversalGrading N) (MvPolynomial.X i)
    let s := fun w j ↦ Point.evaluate (q ⁻¹ᵁ U)
      (q.app U ((Proj.awayToSection (UniversalGrading N) (MvPolynomial.X i))
        (chartCoordinate i j))) (abelianExp X w)
    AnalyticAt ℂ s z ∧ s z i = 1 ∧ s z ≠ 0 := by
  dsimp only
  refine ⟨AnalyticAt.pi (fun j ↦ bh8_analyticAt_evaluate_abelianExp X _ _ z hz), ?_⟩
  have hi : Point.evaluate (q ⁻¹ᵁ Proj.basicOpen (UniversalGrading N) (MvPolynomial.X i))
      (q.app _ ((Proj.awayToSection (UniversalGrading N) (MvPolynomial.X i))
        (chartCoordinate i i))) (abelianExp X z) = 1 := by
    rw [chartCoordinate_self, map_one, map_one]
    rw [Point.evaluate, dite_eq_left (show (abelianExp X z).underlying ∈
      q ⁻¹ᵁ Proj.basicOpen (UniversalGrading N) (MvPolynomial.X i) from hz), map_one, map_one]
  exact ⟨hi, fun h ↦ one_ne_zero (hi.symm.trans (congrFun h i))⟩

open ComplexProjectiveSpace in
/-- Local lifts of a periodic projective map have analytic unit transitions under periods.
Source: Griffiths--Harris, Chapter 0, changes of homogeneous coordinates. -/
theorem bh8_periodic_projective_lift_transition
    {n N : ℕ} (Λ : Submodule ℤ (Fin n → ℂ))
    (f : (Fin n → ℂ) → ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ))))
    (hf : ∀ (l : Λ) w, f (w + l) = f w)
    {U V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (s t : (Fin n → ℂ) → CoordinateSpace N)
    (hs : AnalyticOnNhd ℂ s U) (ht : AnalyticOnNhd ℂ t V)
    (hs0 : ∀ w ∈ U, s w ≠ 0) (ht0 : ∀ w ∈ V, t w ≠ 0)
    (hsf : ∀ w (hw : w ∈ U), vectorToComplexPoint (s w) (hs0 w hw) = f w)
    (htf : ∀ w (hw : w ∈ V), vectorToComplexPoint (t w) (ht0 w hw) = f w)
    (l : Λ) (z : Fin n → ℂ) (hz : z ∈ U) (hzl : z + l ∈ V) :
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, t (w + l) = u w • s w := by
  apply bh8_projective_lift_transition (hs z hz)
    ((ht (z + l) hzl).comp (f := fun w ↦ w + (l : Fin n → ℂ))
      (analyticAt_id.add analyticAt_const))
    (hs0 z hz) (ht0 (z + l) hzl)
  have hn : ∀ᶠ w in 𝓝 z, w + (l : Fin n → ℂ) ∈ V :=
    (continuous_id.add continuous_const).continuousAt (hV.mem_nhds hzl)
  filter_upwards [hU.mem_nhds hz, hn] with w hw hwl
  exact ⟨hs0 w hw, ht0 (w + l) hwl, (hsf w hw).trans
    ((hf l w).symm.trans (htf (w + l) hwl).symm)⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
open ComplexProjectiveSpace in
/-- Evaluation of the standard chart ring reconstructs the original projective point.
Source: the affine chart isomorphism for Proj and the local-ring description of scheme points. -/
theorem bh8_projective_chart_evaluation_recovers_point {N : ℕ}
    (q : Spec ↧ℂ ⟶ Proj (UniversalGrading N)) (i : Fin (N + 1))
    (hq : q (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen (UniversalGrading N) (MvPolynomial.X i)) :
    Spec.map (Proj.awayToSection (UniversalGrading N) (MvPolynomial.X i) ≫
      (Proj (UniversalGrading N)).presheaf.germ _ _ hq ≫
      Scheme.stalkClosedPointTo q) ≫
      Proj.awayι (UniversalGrading N) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ _) zero_lt_one = q := by
  let U := Proj.basicOpen (UniversalGrading N) (MvPolynomial.X i)
  rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    ← Scheme.Opens.fromSpecStalkOfMem_toSpecΓ U _ hq]
  change Spec.map (Scheme.stalkClosedPointTo q) ≫
    U.fromSpecStalkOfMem _ hq ≫
    (Proj.basicOpenIsoSpec (UniversalGrading N) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ _) zero_lt_one).hom ≫ _ = q
  simp only [Proj.awayι, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk q

attribute [local instance] MvPolynomial.gradedAlgebra in
open ComplexProjectiveSpace in
/-- The pulled-back regular coordinate ratios represent the original projective point.
Source: standard projective charts and functoriality of evaluation of regular functions. -/
theorem bh8_pullback_projective_coordinates_represent
    (X : Over (Spec ↧ℂ)) {N : ℕ}
    (q : X.left ⟶ Proj (UniversalGrading N)) (i : Fin (N + 1))
    (z : ComplexPoint X)
    (hz : z ∈ Point.overOpen
      (q ⁻¹ᵁ Proj.basicOpen (UniversalGrading N) (MvPolynomial.X i))) :
    let U := Proj.basicOpen (UniversalGrading N) (MvPolynomial.X i)
    let v := fun j ↦ Point.evaluate (q ⁻¹ᵁ U)
      (q.app U ((Proj.awayToSection (UniversalGrading N) (MvPolynomial.X i))
        (chartCoordinate i j))) z
    ∃ hv : v ≠ 0, chartIntegralProj v hv = z.left ≫ q := by
  let U := Proj.basicOpen (UniversalGrading N) (MvPolynomial.X i)
  let φ := Proj.awayToSection (UniversalGrading N) (MvPolynomial.X i) ≫
    (Proj (UniversalGrading N)).presheaf.germ U _ hz ≫
    Scheme.stalkClosedPointTo (z.left ≫ q)
  have he (j : Fin (N + 1)) :
      Point.evaluate (q ⁻¹ᵁ U)
        (q.app U ((Proj.awayToSection (UniversalGrading N) (MvPolynomial.X i))
          (chartCoordinate i j))) z = vectorOfAwayRingHom i φ.hom j := by
    rw [Point.evaluate, dite_eq_left (show z.underlying ∈ q ⁻¹ᵁ U from hz)]
    change _ = φ.hom (chartCoordinate i j)
    dsimp only [φ, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [Scheme.stalkClosedPointTo_comp]
    exact congrArg (fun r ↦ z.stalkHom r)
      (q.germ_stalkMap_apply U z.underlying hz
        ((Proj.awayToSection (UniversalGrading N) (MvPolynomial.X i))
          (chartCoordinate i j))).symm
  dsimp only
  rw [funext he]
  refine ⟨vectorOfAwayRingHom_ne_zero i φ.hom, ?_⟩
  rw [chartIntegralProj_eq_chartIntegralProjAt _ _ i
    ((vectorOfAwayRingHom_self i φ.hom).trans_ne one_ne_zero)]
  unfold chartIntegralProjAt
  rw [awayCoordinateEvaluation_vectorOfAwayRingHom]
  exact bh8_projective_chart_evaluation_recovers_point (z.left ≫ q) i hz

open ComplexProjectiveSpace in
/-- Normalized homogeneous vectors are unchanged by the standard affine chart parametrization.
Source: the coordinate-ratio formula for the standard projective chart. -/
theorem bh8_chartAffine_normalized {N : ℕ} (i : Fin (N + 1))
    (v : CoordinateSpace N) (hi : v i = 1) (hv : v ≠ 0) :
    chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (N + 1))).symm v) =
      vectorToComplexPoint v hv := by
  simpa only [vectorChartToAffinePoint, Function.comp_apply, vectorChartRatios,
    hi, inv_one, one_smul] using
    chartVectorToComplexPoint_eq i ⟨v, hi.trans_ne one_ne_zero⟩

open ComplexProjectiveSpace in
/-- Regular functions pulled back through a standard projective chart are analytic.
Source: analyticity of regular functions on affine complex space. -/
theorem bh8_analyticAt_evaluate_projective_chart {N : ℕ} (i : Fin (N + 1))
    (V : (ProjectiveSpace (Fin (N + 1)) (Spec ↧ℂ)).Opens)
    (r : Γ(ProjectiveSpace (Fin (N + 1)) (Spec ↧ℂ), V))
    (v : CoordinateSpace N)
    (hv : chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (N + 1))).symm v)
      ∈ Point.overOpen V) :
    AnalyticAt ℂ (fun w ↦ Point.evaluate V r
      (chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (N + 1))).symm w))) v := by
  let a : Over.mk (complexAffineSpace (Fin (N + 1)) ↘ Spec ↧ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ)) :=
    Over.homMk (chartAffineToProjectiveSpace i) (chartAffineToProjectiveSpace_over i)
  change AnalyticAt ℂ (fun w ↦ Point.evaluate V r
    (Point.map a ((affineSpaceEquiv (Fin (N + 1))).symm w))) v
  simp_rw [Point.evaluate_map]
  exact bh8_analyticAt_affine_evaluate (a.left ⁻¹ᵁ V) (a.left.app V r) v hv

open ComplexProjectiveSpace in
/-- A local lift of a projective closed immersion of the abelian cover has injective differential.
Source: lifting regular coordinates through a closed immersion and the analytic chain rule. -/
theorem bh8_injective_fderiv_projective_lift
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (P : ProjectiveSpace.Presentation X.hom)
    (i : Fin (P.ambientDimension + 1))
    (s : (Fin (dim X.left) → ℂ) → CoordinateSpace P.ambientDimension)
    (z : Fin (dim X.left) → ℂ) (hs : AnalyticAt ℂ s z)
    (he : ∀ᶠ w in 𝓝 z,
      chartAffineComplexPointMap i
          ((affineSpaceEquiv (Fin (P.ambientDimension + 1))).symm (s w)) =
        Point.map P.overImmersion (abelianExp X w)) :
    Function.Injective (fderiv ℂ s z) := by
  let D := localEtaleCoordinates X (dim X.left) (abelianExp X z)
  have hzD : (abelianExp X z).underlying ∈ D.ambientCoordinateOpen := by
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top,
      Point.overOpen, Set.mem_ofPred_eq] using
      mem_localEtaleCoordinates X (dim X.left) (abelianExp X z)
  let : IsClosedImmersion P.immersion := P.isClosedImmersion
  obtain ⟨V, _, hVD, hzV, r, hr⟩ := P.immersion.exists_affine_local_section_lifts
    D.ambientCoordinateOpen D.ambientCoordinateSection (abelianExp X z).underlying hzD
  let e := localChart X (dim X.left) (abelianExp X z)
  let L : CoordinateSpace P.ambientDimension → (Fin (dim X.left) → ℂ) :=
    fun v j ↦ Point.evaluate V (r j) (chartAffineComplexPointMap i
      ((affineSpaceEquiv (Fin (P.ambientDimension + 1))).symm v))
  have hL : AnalyticAt ℂ L (s z) := by
    apply AnalyticAt.pi
    intro j
    apply bh8_analyticAt_evaluate_projective_chart i V (r j) (s z)
    rw [he.self_of_nhds]
    exact hzV
  have hchart : ∀ᶠ w in 𝓝 z, abelianExp X w ∈ e.source :=
    (continuous_abelianExp X).continuousAt
      (e.open_source.mem_nhds (mem_localChart_source X _ _))
  have hV : ∀ᶠ w in 𝓝 z,
      Point.map P.overImmersion (abelianExp X w) ∈ Point.overOpen V :=
    ((Point.continuous_map P.overImmersion).comp (continuous_abelianExp X)).continuousAt
      ((Point.isOpen_overOpen (X := Over.mk (ProjectiveSpace.toBase
        (Fin (P.ambientDimension + 1)) (Spec ↧ℂ))) V).mem_nhds hzV)
  have hcomp : (L ∘ s) =ᶠ[𝓝 z] (fun w ↦ e (abelianExp X w)) := by
    filter_upwards [he, hchart, hV] with w hw hc hv
    funext j
    change Point.evaluate V (r j) (chartAffineComplexPointMap i
      ((affineSpaceEquiv (Fin (P.ambientDimension + 1))).symm (s w))) =
        e (abelianExp X w) j
    rw [hw, Point.evaluate_map]
    change Point.evaluate (P.immersion ⁻¹ᵁ V) (P.immersion.app V (r j))
      (abelianExp X w) = e (abelianExp X w) j
    rw [hr]
    rw [← Point.evaluate_res hVD (D.ambientCoordinateSection j) (abelianExp X w) hv]
    exact (localChart_apply_component_eq_evaluate X (dim X.left)
      (abelianExp X z) (abelianExp X w) hc j).symm
  have hd : (fderiv ℂ L (s z)).comp (fderiv ℂ s z) =
      fderiv ℂ (fun w ↦ e (abelianExp X w)) z := by
    rw [← fderiv_comp z hL.differentiableAt hs.differentiableAt]
    exact hcomp.fderiv_eq
  intro v w hvw
  apply bh8_injective_fderiv_abelianExp_chart X z
  change fderiv ℂ (fun w ↦ e (abelianExp X w)) z v =
    fderiv ℂ (fun w ↦ e (abelianExp X w)) z w
  rw [← hd]
  exact congrArg (fderiv ℂ L (s z)) hvw

attribute [local instance] MvPolynomial.gradedAlgebra in
open ComplexProjectiveSpace in
/-- Each point of the abelian cover has a normalized analytic lift of the projective presentation.
Source: the standard projective chart cover and regular coordinate ratios. -/
theorem bh8_exists_normalized_projective_lift
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (P : ProjectiveSpace.Presentation X.hom)
    (p : Fin (dim X.left) → ℂ) :
    ∃ (i : Fin (P.ambientDimension + 1))
      (U : Set (Fin (dim X.left) → ℂ))
      (s : (Fin (dim X.left) → ℂ) → CoordinateSpace P.ambientDimension),
      IsOpen U ∧ p ∈ U ∧ AnalyticOnNhd ℂ s U ∧
      (∀ z ∈ U, s z i = 1) ∧
      (∀ z ∈ U, ∃ hv : s z ≠ 0,
        vectorToComplexPoint (s z) hv = Point.map P.overImmersion (abelianExp X z)) := by
  let q := P.immersion ≫ Limits.pullback.snd
    (Limits.terminal.from (Spec ↧ℂ))
    (Limits.terminal.from (Proj (UniversalGrading P.ambientDimension)))
  obtain ⟨i, hi⟩ : ∃ i : Fin (P.ambientDimension + 1),
      q (abelianExp X p).underlying ∈
        Proj.basicOpen (UniversalGrading P.ambientDimension) (MvPolynomial.X i) := by
    have h : q (abelianExp X p).underlying ∈
        (⊤ : (Proj (UniversalGrading P.ambientDimension)).Opens) := trivial
    rw [← iSup_coordinateBasicOpen_eq_top P.ambientDimension, Opens.mem_iSup] at h
    exact h
  let V := Proj.basicOpen (UniversalGrading P.ambientDimension) (MvPolynomial.X i)
  let U := abelianExp X ⁻¹' Point.overOpen (q ⁻¹ᵁ V)
  let s := fun w j ↦ Point.evaluate (q ⁻¹ᵁ V)
    (q.app V ((Proj.awayToSection (UniversalGrading P.ambientDimension) (MvPolynomial.X i))
      (chartCoordinate i j))) (abelianExp X w)
  have hs (z) (hz : z ∈ U) : AnalyticAt ℂ s z ∧ s z i = 1 ∧ s z ≠ 0 :=
    bh8_analytic_normalized_projective_coordinates X q i z hz
  refine ⟨i, U, s, (Point.isOpen_overOpen _).preimage (continuous_abelianExp X),
    hi, fun z hz ↦ (hs z hz).1, fun z hz ↦ (hs z hz).2.1, ?_⟩
  intro z hz
  obtain ⟨hv, he⟩ := bh8_pullback_projective_coordinates_represent X q i (abelianExp X z) hz
  refine ⟨hv, ?_⟩
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · exact (vectorToProjectiveSpace_toBase (s z) hv).trans
      (Over.w (Point.map P.overImmersion (abelianExp X z))).symm
  · exact (vectorToProjectiveSpace_toProj (s z) hv).trans he

/-- Local homogeneous lifts of a projective embedding give a periodic projective immersion
of the abelian universal cover.
Source: Griffiths--Harris, Chapter 0, projective embeddings and analytic coordinates;
Birkenhake--Lange, second edition, section 4.3. -/
theorem bh8_projective_atlas_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : Nonempty (bh8_ProjectiveAtlas (dim X.left) (abelianPeriodLattice X)) := by
  classical
  let P : ProjectiveSpace.Presentation X.hom :=
    Classical.choice (IsProjective.nonempty_presentation (f := X.hom))
  choose i U s hopen hanchor hanalytic hnormalized hrep using
    bh8_exists_normalized_projective_lift X P
  have hn (p z) (hz : z ∈ U p) : s p z ≠ 0 := (hrep p z hz).choose
  have he (p z) (hz : z ∈ U p) :
      ComplexProjectiveSpace.vectorToComplexPoint (s p z) (hn p z hz) =
        Point.map P.overImmersion (abelianExp X z) := (hrep p z hz).choose_spec
  refine ⟨{ N := P.ambientDimension
            U := U
            s := s
            open_U := hopen
            anchor := hanchor
            analytic := hanalytic
            nonzero := hn
            immersion := ?_
            transition := ?_ }⟩
  · intro p z hz v c hv
    apply bh8_radial_immersion_of_normalized (hanalytic p z hz).differentiableAt (i p)
      (Filter.Eventually.mono ((hopen p).mem_nhds hz) (fun w hw ↦ hnormalized p w hw))
      (bh8_injective_fderiv_projective_lift X P (i p) (s p) z (hanalytic p z hz) ?_) v c hv
    filter_upwards [(hopen p).mem_nhds hz] with w hw
    exact (bh8_chartAffine_normalized (i p) (s p w) (hnormalized p w hw)
      (hn p w hw)).trans (he p w hw)
  · intro l p q z hz hzl
    exact bh8_periodic_projective_lift_transition (abelianPeriodLattice X)
      (fun w ↦ Point.map P.overImmersion (abelianExp X w))
      (fun l w ↦ congrArg (Point.map P.overImmersion) (abelianExp_add_lattice X w l))
      (hopen p) (hopen q) (s p) (s q) (hanalytic p) (hanalytic q)
      (hn p) (hn q) (he p) (he q) l z hz hzl

private theorem bh8_sum_normSq_pos {m : ℕ} (s : Fin m → ℂ) (hs : s ≠ 0) :
    0 < ∑ j, Complex.normSq (s j) := by
  obtain ⟨j, hj⟩ : ∃ j, s j ≠ 0 := by
    by_contra h
    apply hs
    ext j
    exact not_ne_iff.mp (not_exists.mp h j)
  exact Finset.sum_pos' (fun i _ ↦ Complex.normSq_nonneg (s i))
    ⟨j, Finset.mem_univ j, Complex.normSq_pos.mpr hj⟩

private theorem bh8_potential_smooth (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p z : Fin n → ℂ) (hz : z ∈ A.U p) :
    ContDiffAt ℝ ∞ (bh8_potential n Λ A p) z := by
  have hs : ContDiffAt ℝ ∞ (A.s p) z :=
    ((A.analytic p z hz).contDiffAt).restrict_scalars ℝ
  unfold bh8_potential
  refine ContDiffAt.log (f := fun w ↦ ∑ j, Complex.normSq (A.s p w j)) ?_
    (ne_of_gt (bh8_sum_normSq_pos _ (A.nonzero p z hz)))
  apply ContDiffAt.sum
  intro j _
  have hj : ContDiffAt ℝ ∞ (fun w ↦ A.s p w j) z :=
    (contDiffAt_pi.mp hs) j
  change ContDiffAt ℝ ∞ (fun w ↦ (A.s p w j).re * (A.s p w j).re +
    (A.s p w j).im * (A.s p w j).im) z
  exact ((Complex.reCLM.contDiff.contDiffAt.comp z hj).mul
    (Complex.reCLM.contDiff.contDiffAt.comp z hj)).add
    ((Complex.imCLM.contDiff.contDiffAt.comp z hj).mul (Complex.imCLM.contDiff.contDiffAt.comp z hj))

private theorem bh8_curvature_alternating (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p v : Fin n → ℂ) :
    bh8_curvature n Λ A p v v = 0 := by
  simp only [bh8_curvature, smul_apply,
    sub_apply, ContinuousLinearMap.flip_apply, sub_self, smul_zero]

private theorem bh8_curvature_type (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p : Fin n → ℂ) :
    IsTypeOneOne (fun v w ↦ bh8_curvature n Λ A p v w) := by
  have hs := (bh8_potential_smooth n Λ A p p (A.anchor p)).isSymmSndFDerivAt
    (by simp)
  intro v w
  let H := fderiv ℝ (fderiv ℝ (bh8_potential n Λ A p)) p
  change (1 / (4 * Real.pi)) *
    (H (Complex.I • w) (Complex.I • (Complex.I • v)) -
      H (Complex.I • v) (Complex.I • (Complex.I • w))) =
    (1 / (4 * Real.pi)) * (H w (Complex.I • v) - H v (Complex.I • w))
  simp only [smul_smul, Complex.I_mul_I, neg_smul, one_smul, map_neg]
  rw [show H (Complex.I • w) v = H v (Complex.I • w) from hs _ _,
    show H (Complex.I • v) w = H w (Complex.I • v) from hs _ _]
  ring


private def bh8_curvatureOperator (n : ℕ) :
    ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) →L[ℝ]
      ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) :=
  let F := (ContinuousLinearMap.flipₗᵢ ℝ (Fin n → ℂ) (Fin n → ℂ) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let C := (ContinuousLinearMap.compL ℝ (Fin n → ℂ) (Fin n → ℂ)
    ((Fin n → ℂ) →L[ℝ] ℝ)).flip (bh8_complexStructure n)
  (1 / (4 * Real.pi)) • (C.comp F - F.comp (C.comp F))

private theorem bh8_curvatureOperator_apply (n : ℕ)
    (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (v w : Fin n → ℂ) :
    bh8_curvatureOperator n H v w =
      (1 / (4 * Real.pi)) * (H w (Complex.I • v) - H v (Complex.I • w)) := rfl

private theorem bh8_local_curvature_smooth (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p z : Fin n → ℂ) (hz : z ∈ A.U p) :
    ContDiffAt ℝ ∞ (fun w ↦ bh8_curvatureOperator n
      (fderiv ℝ (fderiv ℝ (bh8_potential n Λ A p)) w)) z := by
  exact (bh8_curvatureOperator n).contDiff.contDiffAt.comp z
    (((bh8_potential_smooth n Λ A p z hz).fderiv_right (m := ∞) (by simp)).fderiv_right
      (by simp))

private theorem bh8_local_curvature_closed (n : ℕ) (φ : (Fin n → ℂ) → ℝ)
    (z : Fin n → ℂ) (hφ : ContDiffAt ℝ ∞ φ z) (u v w : Fin n → ℂ) :
    fderiv ℝ (fun x ↦ bh8_curvatureOperator n (fderiv ℝ (fderiv ℝ φ) x)) z u v w +
    fderiv ℝ (fun x ↦ bh8_curvatureOperator n (fderiv ℝ (fderiv ℝ φ) x)) z v w u +
    fderiv ℝ (fun x ↦ bh8_curvatureOperator n (fderiv ℝ (fderiv ℝ φ) x)) z w u v = 0 := by
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ φ) z := hφ.fderiv_right (by simp)
  have hDD : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ φ)) z := hD.fderiv_right (by simp)
  have hs := hD.isSymmSndFDerivAt (by simp)
  rw [show (fun x ↦ bh8_curvatureOperator n (fderiv ℝ (fderiv ℝ φ) x)) =
    (bh8_curvatureOperator n) ∘ (fderiv ℝ (fderiv ℝ φ)) from rfl]
  rw [fderiv_comp z (bh8_curvatureOperator n).differentiableAt
    (hDD.differentiableAt (by simp)), ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply, bh8_curvatureOperator_apply]
  rw [show fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z u w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z w u from hs u w,
    show fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z v u =
      fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z u v from hs v u,
    show fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z w v =
      fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z v w from hs w v]
  ring

private theorem bh8_hessian_re (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hf : AnalyticAt ℂ f z) (v w : Fin n → ℂ) :
    fderiv ℝ (fderiv ℝ (fun x ↦ (f x).re)) z v w =
      (fderiv ℂ (fderiv ℂ f) z v w).re := by
  have hr : ContDiffAt ℝ 2 f z := hf.contDiffAt.restrict_scalars ℝ
  have hc : ContDiffAt ℂ 2 f z := hf.contDiffAt
  have he := congrArg (fun T ↦ T ![v, w])
    (Complex.reCLM.iteratedFDeriv_comp_left hr (i := 2) le_rfl)
  have he' := congrArg (fun T ↦ T ![v, w])
    (hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ))
  simp only [Function.comp_apply, ContinuousMultilinearMap.coe_restrictScalars,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at he'
  change iteratedFDeriv ℝ 2 (fun x ↦ (f x).re) z ![v, w] =
    (iteratedFDeriv ℝ 2 f z ![v, w]).re at he
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, ← he'] using he

private theorem bh8_curvature_re_zero (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hf : AnalyticAt ℂ f z) :
    bh8_curvatureOperator n (fderiv ℝ (fderiv ℝ (fun x ↦ (f x).re)) z) = 0 := by
  ext v w
  rw [bh8_curvatureOperator_apply, bh8_hessian_re n f z hf,
    bh8_hessian_re n f z hf]
  have hs := hf.contDiffAt.isSymmSndFDerivAt (n := 2) (by simp)
  rw [map_smul, map_smul, hs w v, sub_self, mul_zero]
  rfl

private theorem bh8_log_normSq_pluriharmonic (n : ℕ) (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0) :
    bh8_curvatureOperator n
      (fderiv ℝ (fderiv ℝ (fun x ↦ Real.log (Complex.normSq (u x)))) z) = 0 := by
  let f := fun x ↦ (2 : ℂ) * Complex.log (u x / u z) +
    (Real.log (Complex.normSq (u z)) : ℂ)
  have hf : AnalyticAt ℂ f z := by
    apply AnalyticAt.add _ analyticAt_const
    apply AnalyticAt.mul analyticAt_const
    exact (hu.div_const (c := u z)).clog (by simpa only [div_self hu0] using Complex.one_mem_slitPlane)
  have he : (fun x ↦ Real.log (Complex.normSq (u x))) =ᶠ[𝓝 z]
      (fun x ↦ (f x).re) := by
    filter_upwards [hu.continuousAt.eventually_ne hu0] with x hx
    dsimp [f]
    simp only [Complex.mul_re]
    rw [Complex.log_re, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hu0),
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Real.log_pow, Real.log_pow]
    norm_num
    ring
  rw [(he.fderiv (𝕜 := ℝ)).fderiv_eq]
  exact bh8_curvature_re_zero n f z hf

private theorem bh8_hessian_add (n : ℕ) (f g : (Fin n → ℂ) → ℝ)
    (z : Fin n → ℂ) (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    fderiv ℝ (fderiv ℝ (fun x ↦ f x + g x)) z =
      fderiv ℝ (fderiv ℝ f) z + fderiv ℝ (fderiv ℝ g) z := by
  ext v w
  have he := congrArg (fun T ↦ T ![v, w]) (iteratedFDeriv_add_apply hf hg)
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, add_apply, Pi.add_def]
    using he

private theorem bh8_hessian_translate (n : ℕ) (f : (Fin n → ℂ) → ℝ)
    (z a : Fin n → ℂ) :
    fderiv ℝ (fderiv ℝ (fun x ↦ f (x + a))) z =
      fderiv ℝ (fderiv ℝ f) (z + a) := by
  ext v w
  have he := congrArg (fun T ↦ T ![v, w])
    (iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) 2 a z)
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using he

private theorem bh8_log_normSq_smooth (n : ℕ) (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0) :
    ContDiffAt ℝ ∞ (fun x ↦ Real.log (Complex.normSq (u x))) z := by
  have hs : ContDiffAt ℝ ∞ u z := hu.contDiffAt.restrict_scalars ℝ
  refine ContDiffAt.log (f := fun x ↦ Complex.normSq (u x)) ?_
    (ne_of_gt (Complex.normSq_pos.mpr hu0))
  change ContDiffAt ℝ ∞ (fun x ↦ (u x).re * (u x).re + (u x).im * (u x).im) z
  exact ((Complex.reCLM.contDiff.contDiffAt.comp z hs).mul
    (Complex.reCLM.contDiff.contDiffAt.comp z hs)).add
    ((Complex.imCLM.contDiff.contDiffAt.comp z hs).mul
      (Complex.imCLM.contDiff.contDiffAt.comp z hs))

private theorem bh8_chart_curvature_transition (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (l : Λ) (p q z : Fin n → ℂ)
    (hp : z ∈ A.U p) (hq : z + l ∈ A.U q) :
    bh8_curvatureOperator n (fderiv ℝ (fderiv ℝ (bh8_potential n Λ A q)) (z + l)) =
      bh8_curvatureOperator n (fderiv ℝ (fderiv ℝ (bh8_potential n Λ A p)) z) := by
  obtain ⟨u, hu, hu0, he⟩ := A.transition l p q z hp hq
  have hpot : (fun w ↦ bh8_potential n Λ A q (w + l)) =ᶠ[𝓝 z]
      (fun w ↦ Real.log (Complex.normSq (u w)) + bh8_potential n Λ A p w) := by
    filter_upwards [he, hu.continuousAt.eventually_ne hu0, (A.open_U p).mem_nhds hp]
      with w hw hw0 hwp
    unfold bh8_potential
    rw [hw]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← Finset.mul_sum]
    exact Real.log_mul (ne_of_gt (Complex.normSq_pos.mpr hw0))
      (ne_of_gt (bh8_sum_normSq_pos _ (A.nonzero p w hwp)))
  rw [← bh8_hessian_translate n (bh8_potential n Λ A q) z l,
    (hpot.fderiv (𝕜 := ℝ)).fderiv_eq,
    bh8_hessian_add n _ _ z
      ((bh8_log_normSq_smooth n u z hu hu0).of_le (by simp))
      ((bh8_potential_smooth n Λ A p z hp).of_le (by simp)),
    map_add, bh8_log_normSq_pluriharmonic n u z hu hu0, zero_add]

private theorem bh8_curvature_eq_chart (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p z : Fin n → ℂ) (hz : z ∈ A.U p) :
    bh8_curvature n Λ A z =
      bh8_curvatureOperator n (fderiv ℝ (fderiv ℝ (bh8_potential n Λ A p)) z) := by
  have he := bh8_chart_curvature_transition n Λ A 0 p z z hz
    (by simpa only [ZeroMemClass.coe_zero, add_zero] using A.anchor z)
  change bh8_curvatureOperator n (fderiv ℝ (fderiv ℝ (bh8_potential n Λ A z)) z) = _
  simpa only [ZeroMemClass.coe_zero, add_zero] using he

private theorem bh8_curvature_smooth (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) : ContDiff ℝ ∞ (bh8_curvature n Λ A) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  apply (bh8_local_curvature_smooth n Λ A z z (A.anchor z)).congr_of_eventuallyEq
  filter_upwards [(A.open_U z).mem_nhds (A.anchor z)] with w hw
  exact bh8_curvature_eq_chart n Λ A z w hw

private theorem bh8_curvature_periodic (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (l : Λ) (p : Fin n → ℂ) :
    bh8_curvature n Λ A (p + l) = bh8_curvature n Λ A p := by
  exact bh8_chart_curvature_transition n Λ A l p (p + l) p (A.anchor p) (A.anchor _)

private theorem bh8_curvature_closed (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p u v w : Fin n → ℂ) :
    fderiv ℝ (bh8_curvature n Λ A) p u v w +
    fderiv ℝ (bh8_curvature n Λ A) p v w u +
    fderiv ℝ (bh8_curvature n Λ A) p w u v = 0 := by
  have he : bh8_curvature n Λ A =ᶠ[𝓝 p]
      (fun z ↦ bh8_curvatureOperator n (fderiv ℝ (fderiv ℝ (bh8_potential n Λ A p)) z)) := by
    filter_upwards [(A.open_U p).mem_nhds (A.anchor p)] with z hz
    exact bh8_curvature_eq_chart n Λ A p z hz
  rw [he.fderiv_eq]
  exact bh8_local_curvature_closed n _ p (bh8_potential_smooth n Λ A p p (A.anchor p)) u v w

private theorem bh8_derivative_eval {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : (Fin n → ℂ) → F) (z v w : Fin n → ℂ)
    (hf : ContDiffAt ℝ 2 f z) :
    fderiv ℝ (fun x ↦ fderiv ℝ f x v) z w = fderiv ℝ (fderiv ℝ f) z w v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]

private theorem bh8_hessian_log (n : ℕ) (f : (Fin n → ℂ) → ℝ)
    (z v w : Fin n → ℂ) (hf : ContDiffAt ℝ 2 f z) (hf0 : f z ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun x ↦ Real.log (f x))) z w v =
      (f z)⁻¹ * fderiv ℝ (fderiv ℝ f) z w v -
        (f z ^ 2)⁻¹ * (fderiv ℝ f z w) * (fderiv ℝ f z v) := by
  have he : (fun x ↦ fderiv ℝ (fun y ↦ Real.log (f y)) x v) =ᶠ[𝓝 z]
      (fun x ↦ (f x)⁻¹ * fderiv ℝ f x v) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt.eventually_ne hf0] with x hx hx0
    rw [fderiv.log (hx.differentiableAt (by norm_num)) hx0]
    rfl
  rw [← bh8_derivative_eval n _ z v w (hf.log hf0), he.fderiv_eq]
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hi := (hasDerivAt_inv hf0).comp_hasFDerivAt z (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hm := (hi.mul (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v z))).fderiv
  simp only [Pi.mul_def, Function.comp_def] at hm
  rw [hm]
  simp only [add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  ring

private theorem bh8_hessian_norm_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (n : ℕ) (f : (Fin n → ℂ) → F) (z v w : Fin n → ℂ)
    (hf : ContDiffAt ℝ 2 f z) :
    fderiv ℝ (fderiv ℝ (fun x ↦ ‖f x‖ ^ 2)) z w v =
      2 * (inner ℝ (f z) (fderiv ℝ (fderiv ℝ f) z w v) +
        inner ℝ (fderiv ℝ f z w) (fderiv ℝ f z v)) := by
  have he : (fun x ↦ fderiv ℝ (fun y ↦ ‖f y‖ ^ 2) x v) =ᶠ[𝓝 z]
      (fun x ↦ 2 * inner ℝ (f x) (fderiv ℝ f x v)) := by
    filter_upwards [hf.eventually (by norm_num)] with x hx
    rw [(hx.differentiableAt (by norm_num)).hasFDerivAt.norm_sq.fderiv]
    simp only [smul_apply, ContinuousLinearMap.comp_apply]
    change (2 : ℕ) • inner ℝ (f x) (fderiv ℝ f x v) = _
    simp only [two_smul, two_mul]
  have hq : ContDiffAt ℝ 2 (fun x ↦ ‖f x‖ ^ 2) z :=
    (contDiff_norm_sq (𝕜 := ℝ)).contDiffAt.comp z hf
  rw [← bh8_derivative_eval n _ z v w hq, he.fderiv_eq]
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hv := hd.clm_apply (differentiableAt_const v)
  rw [fderiv_const_mul ((hf.differentiableAt (by norm_num)).inner ℝ hv) 2]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_inner_apply ℝ (hf.differentiableAt (by norm_num)) hv,
    bh8_derivative_eval n f z v w hf]

private theorem bh8_hessian_complex (n m : ℕ)
    (f : (Fin n → ℂ) → EuclideanSpace ℂ (Fin m)) (z v w : Fin n → ℂ)
    (hf : AnalyticAt ℂ f z) :
    fderiv ℝ (fderiv ℝ f) z v w = fderiv ℂ (fderiv ℂ f) z v w := by
  have hc : ContDiffAt ℂ 2 f z := hf.contDiffAt
  have he := congrArg (fun T ↦ T ![v, w])
    (hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ))
  simpa only [Function.comp_apply, ContinuousMultilinearMap.coe_restrictScalars,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using he.symm

private theorem bh8_norm_sq_derivative (n m : ℕ)
    (f : (Fin n → ℂ) → EuclideanSpace ℂ (Fin m)) (z v : Fin n → ℂ)
    (hf : AnalyticAt ℂ f z) :
    fderiv ℝ (fun x ↦ ‖f x‖ ^ 2) z v =
      2 * (inner ℂ (f z) (fderiv ℂ f z v)).re := by
  let := InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin m))
  rw [(hf.differentiableAt.restrictScalars ℝ).hasFDerivAt.norm_sq.fderiv,
    hf.differentiableAt.fderiv_restrictScalars ℝ]
  simp only [two_smul, two_mul]
  rfl

private theorem bh8_norm_sq_hessian_trace (n m : ℕ)
    (f : (Fin n → ℂ) → EuclideanSpace ℂ (Fin m)) (z v : Fin n → ℂ)
    (hf : AnalyticAt ℂ f z) :
    fderiv ℝ (fderiv ℝ (fun x ↦ ‖f x‖ ^ 2)) z v v +
    fderiv ℝ (fderiv ℝ (fun x ↦ ‖f x‖ ^ 2)) z (Complex.I • v) (Complex.I • v) =
      4 * ‖fderiv ℂ f z v‖ ^ 2 := by
  let := InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin m))
  have hr : ContDiffAt ℝ 2 f z := hf.contDiffAt.restrict_scalars ℝ
  rw [bh8_hessian_norm_sq n f z v v hr,
    bh8_hessian_norm_sq n f z (Complex.I • v) (Complex.I • v) hr,
    bh8_hessian_complex n m f z v v hf,
    bh8_hessian_complex n m f z (Complex.I • v) (Complex.I • v) hf,
    hf.differentiableAt.fderiv_restrictScalars ℝ]
  change 2 * (inner ℝ (f z) (fderiv ℂ (fderiv ℂ f) z v v) +
      inner ℝ (fderiv ℂ f z v) (fderiv ℂ f z v)) +
    2 * (inner ℝ (f z) (fderiv ℂ (fderiv ℂ f) z (Complex.I • v) (Complex.I • v)) +
      inner ℝ (fderiv ℂ f z (Complex.I • v)) (fderiv ℂ f z (Complex.I • v))) = _
  simp only [map_smul, smul_apply, smul_smul, Complex.I_mul_I, neg_smul, one_smul,
    inner_neg_right, real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  ring

private theorem bh8_strict_cauchy (m : ℕ) (x y : EuclideanSpace ℂ (Fin m))
    (hx : x ≠ 0) (hxy : ∀ c : ℂ, y ≠ c • x) :
    0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖inner ℂ x y‖ ^ 2 := by
  have hy : y ≠ 0 := by simpa only [zero_smul] using hxy 0
  have hlt : ‖inner ℂ x y‖ < ‖x‖ * ‖y‖ := by
    refine lt_of_le_of_ne (norm_inner_le_norm x y) ?_
    intro he
    obtain ⟨c, _, hc⟩ := (norm_inner_eq_norm_iff hx hy).mp he
    exact hxy c hc
  have hs := (sq_lt_sq₀ (norm_nonneg (inner ℂ x y))
    (mul_nonneg (norm_nonneg x) (norm_nonneg y))).mpr hlt
  nlinarith

private theorem bh8_log_norm_curvature_positive (n m : ℕ)
    (f : (Fin n → ℂ) → EuclideanSpace ℂ (Fin m)) (z v : Fin n → ℂ)
    (hf : AnalyticAt ℂ f z) (hf0 : f z ≠ 0)
    (hv : ∀ c : ℂ, fderiv ℂ f z v ≠ c • f z) :
    0 < bh8_curvatureOperator n
      (fderiv ℝ (fderiv ℝ (fun x ↦ Real.log (‖f x‖ ^ 2))) z) v (Complex.I • v) := by
  have hr : ContDiffAt ℝ 2 f z := hf.contDiffAt.restrict_scalars ℝ
  have hq : ContDiffAt ℝ 2 (fun x ↦ ‖f x‖ ^ 2) z :=
    (contDiff_norm_sq (𝕜 := ℂ)).contDiffAt.comp z hr
  have hq0 : ‖f z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hf0)
  have ht := bh8_norm_sq_hessian_trace n m f z v hf
  have hc := bh8_strict_cauchy m (f z) (fderiv ℂ f z v) hf0 hv
  have hn : ‖inner ℂ (f z) (fderiv ℂ f z v)‖ ^ 2 =
      (inner ℂ (f z) (fderiv ℂ f z v)).re ^ 2 +
        (inner ℂ (f z) (fderiv ℂ f z v)).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have he : bh8_curvatureOperator n
      (fderiv ℝ (fderiv ℝ (fun x ↦ Real.log (‖f x‖ ^ 2))) z) v (Complex.I • v) =
      (‖f z‖ ^ 2 * ‖fderiv ℂ f z v‖ ^ 2 -
        ‖inner ℂ (f z) (fderiv ℂ f z v)‖ ^ 2) / (Real.pi * (‖f z‖ ^ 2) ^ 2) := by
    rw [bh8_curvatureOperator_apply]
    simp only [smul_smul, Complex.I_mul_I, neg_smul, one_smul, map_neg, sub_neg_eq_add]
    rw [bh8_hessian_log n _ z (Complex.I • v) (Complex.I • v) hq hq0,
      bh8_hessian_log n _ z v v hq hq0,
      bh8_norm_sq_derivative n m f z (Complex.I • v) hf,
      bh8_norm_sq_derivative n m f z v hf]
    simp only [map_smul, inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub]
    rw [hn]
    field_simp
    nlinarith [ht]
  rw [he]
  exact div_pos hc (mul_pos Real.pi_pos (sq_pos_of_ne_zero hq0))

private theorem bh8_curvature_positive (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p v : Fin n → ℂ) (hv : v ≠ 0) :
    0 < bh8_curvature n Λ A p v (Complex.I • v) := by
  let e := (EuclideanSpace.equiv (Fin (A.N + 1)) ℂ).symm
  let f := fun z ↦ e (A.s p z)
  have hf : AnalyticAt ℂ f p := (e.toContinuousLinearMap.analyticAt (A.s p p)).comp (A.analytic p p (A.anchor p))
  have hf0 : f p ≠ 0 := by
    intro he
    exact A.nonzero p p (A.anchor p) (e.injective (he.trans (map_zero e).symm))
  have hd : fderiv ℂ f p = e.toContinuousLinearMap.comp (fderiv ℂ (A.s p) p) :=
    (e.toContinuousLinearMap.hasFDerivAt.comp p
      (A.analytic p p (A.anchor p)).differentiableAt.hasFDerivAt).fderiv
  have hrad (c : ℂ) : fderiv ℂ f p v ≠ c • f p := by
    intro hc
    apply hv
    apply A.immersion p p (A.anchor p) v c
    apply e.injective
    simpa only [hd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      map_smul, f] using hc
  have hpot : bh8_potential n Λ A p = (fun x ↦ Real.log (‖f x‖ ^ 2)) := by
    funext x
    unfold bh8_potential
    congr 1
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    exact Complex.normSq_eq_norm_sq (A.s p x j)
  change 0 < bh8_curvatureOperator n
    (fderiv ℝ (fderiv ℝ (bh8_potential n Λ A p)) p) v (Complex.I • v)
  rw [hpot]
  exact bh8_log_norm_curvature_positive n (A.N + 1) f p v hf hf0 hrad

/-- Normalized Fubini--Study curvature glues smoothly, is closed and periodic, and is positive
of type (1,1) on a projective immersion.
Source: Griffiths--Harris, Chapter 0, Hermitian differential geometry and the Fubini--Study metric. -/
theorem bh8_curvature_geometry_aux (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) :
    ContDiff ℝ ∞ (bh8_curvature n Λ A) ∧
    (∀ (l : Λ) p, bh8_curvature n Λ A (p + l) = bh8_curvature n Λ A p) ∧
    (∀ p v, bh8_curvature n Λ A p v v = 0) ∧
    (∀ p, IsTypeOneOne (fun v w ↦ bh8_curvature n Λ A p v w)) ∧
    (∀ p v, v ≠ 0 → 0 < bh8_curvature n Λ A p v (Complex.I • v)) ∧
    (∀ p u v w,
      fderiv ℝ (bh8_curvature n Λ A) p u v w +
      fderiv ℝ (bh8_curvature n Λ A) p v w u +
      fderiv ℝ (bh8_curvature n Λ A) p w u v = 0) := by
  exact ⟨bh8_curvature_smooth n Λ A, bh8_curvature_periodic n Λ A,
    bh8_curvature_alternating n Λ A, bh8_curvature_type n Λ A,
    bh8_curvature_positive n Λ A, bh8_curvature_closed n Λ A⟩

/-- A nonzero homogeneous representative has strictly positive squared norm. -/
theorem bh8_chern_normSq_pos {N : ℕ} (s : Fin (N + 1) → ℂ) (hs : s ≠ 0) :
    0 < ∑ j, Complex.normSq (s j) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, s j ≠ 0 := by
    by_contra h
    apply hs
    ext j
    exact not_ne_iff.mp (not_exists.mp h j)
  exact Finset.sum_pos' (fun j _ ↦ Complex.normSq_nonneg (s j))
    ⟨j, Finset.mem_univ j, Complex.normSq_pos.mpr hj⟩

/-- Multiplication of a homogeneous representative adds the logarithmic unit norm
 to its potential. -/
theorem bh8_chern_log_normSq_smul {N : ℕ} (s : Fin (N + 1) → ℂ)
    (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) :
    Real.log (∑ j, Complex.normSq ((u • s) j)) =
      Real.log (Complex.normSq u) + Real.log (∑ j, Complex.normSq (s j)) := by
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← Finset.mul_sum]
  exact Real.log_mul (Complex.normSq_pos.mpr hu).ne'
    (bh8_chern_normSq_pos s hs).ne'

/-- The atlas transition supplies the local change of logarithmic potentials. -/
theorem bh8_chern_potential_transition (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (l : Λ) (p q z : Fin n → ℂ)
    (hp : z ∈ A.U p) (hq : z + l ∈ A.U q) :
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, bh8_potential n Λ A q (w + l) =
        Real.log (Complex.normSq (u w)) + bh8_potential n Λ A p w := by
  obtain ⟨u, hu, hu0, he⟩ := A.transition l p q z hp hq
  refine ⟨u, hu, hu0, ?_⟩
  have hn : ∀ᶠ w in 𝓝 z, u w ≠ 0 := hu.continuousAt.eventually_ne hu0
  filter_upwards [he, hn, (A.open_U p).mem_nhds hp] with w hw hwu hwp
  unfold bh8_potential
  rw [hw]
  exact bh8_chern_log_normSq_smul (A.s p w) (A.nonzero p w hwp) (u w) hwu

/-- Scalars relating a nonzero homogeneous representative are unique. -/
theorem bh8_chern_transition_unique {N : ℕ} (s : Fin (N + 1) → ℂ)
    (hs : s ≠ 0) {u v : ℂ} (h : u • s = v • s) : u = v := by
  exact (smul_left_injective ℂ hs) h

/-- The three transition values at a common point satisfy the cocycle equation. -/
theorem bh8_chern_transition_cocycle {N : ℕ}
    (s t r : Fin (N + 1) → ℂ) (hs : s ≠ 0) (u v w : ℂ)
    (hst : t = u • s) (htr : r = v • t) (hsr : r = w • s) : w = v * u := by
  apply bh8_chern_transition_unique s hs
  rw [← hsr, htr, hst, mul_smul]

/-- A nonvanishing analytic unit has an analytic logarithm near the chosen point. -/
theorem bh8_chern_local_log {n : ℕ} (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0) :
    ∃ g : (Fin n → ℂ) → ℂ, AnalyticAt ℂ g z ∧
      ∀ᶠ w in 𝓝 z, Complex.exp (g w) = u w := by
  let g := fun w ↦ Complex.log (u w / u z) + Complex.log (u z)
  have hdiv : AnalyticAt ℂ (fun w ↦ u w / u z) z := hu.div_const
  have hg : AnalyticAt ℂ g z :=
    (hdiv.clog (by simp only [div_self hu0]; exact Complex.one_mem_slitPlane)).add
      analyticAt_const
  refine ⟨g, hg, ?_⟩
  filter_upwards [hu.continuousAt.eventually_ne hu0] with w hw
  dsimp [g]
  rw [Complex.exp_add, Complex.exp_log (div_ne_zero hw hu0), Complex.exp_log hu0,
    div_mul_cancel₀ _ hu0]

/-- A logarithm expresses the logarithmic squared norm as twice its real part. -/
theorem bh8_chern_log_normSq_exp (g : ℂ) :
    Real.log (Complex.normSq (Complex.exp g)) = 2 * g.re := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, Real.log_pow, Real.log_exp]
  norm_num

/-- Local potential differences are real parts of holomorphic logarithms. -/
theorem bh8_chern_potential_transition_log (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (l : Λ) (p q z : Fin n → ℂ)
    (hp : z ∈ A.U p) (hq : z + l ∈ A.U q) :
    ∃ g : (Fin n → ℂ) → ℂ, AnalyticAt ℂ g z ∧
      ∀ᶠ w in 𝓝 z, bh8_potential n Λ A q (w + l) =
        2 * (g w).re + bh8_potential n Λ A p w := by
  obtain ⟨u, hu, hu0, he⟩ := bh8_chern_potential_transition n Λ A l p q z hp hq
  obtain ⟨g, hg, hexp⟩ := bh8_chern_local_log u z hu hu0
  refine ⟨g, hg, ?_⟩
  filter_upwards [he, hexp] with w hw hwexp
  rw [hw, ← hwexp, bh8_chern_log_normSq_exp]

/-- The real differential of a holomorphic real part on a complex-rotated vector. -/
theorem bh8_chern_fderiv_re_I {n : ℕ} (g : (Fin n → ℂ) → ℂ)
    (z v : Fin n → ℂ) (hg : DifferentiableAt ℂ g z) :
    fderiv ℝ (fun w ↦ (g w).re) z (Complex.I • v) =
      -(fderiv ℂ g z v).im := by
  have hd := Complex.reCLM.hasFDerivAt.comp z (hg.hasFDerivAt.restrictScalars ℝ)
  simp only [Function.comp_def, Complex.reCLM_apply] at hd
  rw [hd.fderiv]
  change (fderiv ℂ g z (Complex.I • v)).re = -(fderiv ℂ g z v).im
  simp only [map_smul, smul_eq_mul,
    Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]

/-- The normalized connection change of a logarithmic unit is its phase differential. -/
theorem bh8_chern_unit_connection {n : ℕ} (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0) :
    ∃ g : (Fin n → ℂ) → ℂ, AnalyticAt ℂ g z ∧
      (∀ᶠ w in 𝓝 z, Complex.exp (g w) = u w) ∧
      ∀ v, -(fderiv ℝ (fun w ↦ Real.log (Complex.normSq (u w))) z
        (Complex.I • v)) / (4 * Real.pi) =
          (fderiv ℂ g z v).im / (2 * Real.pi) := by
  obtain ⟨g, hg, he⟩ := bh8_chern_local_log u z hu hu0
  refine ⟨g, hg, he, fun v ↦ ?_⟩
  have hpot : (fun w ↦ Real.log (Complex.normSq (u w))) =ᶠ[𝓝 z]
      (fun w ↦ 2 * (g w).re) := by
    filter_upwards [he] with w hw
    rw [← hw, bh8_chern_log_normSq_exp]
  have hgre : DifferentiableAt ℝ (fun w ↦ (g w).re) z :=
    (Complex.reCLM.hasFDerivAt.comp z
      (hg.differentiableAt.hasFDerivAt.restrictScalars ℝ)).differentiableAt
  rw [hpot.fderiv_eq, fderiv_const_mul hgre]
  simp only [smul_apply, smul_eq_mul,
    bh8_chern_fderiv_re_I g z v hg.differentiableAt]
  ring

/-- Every fixed atlas potential is smooth on its chart. -/
theorem bh8_chern_potential_contDiffAt (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p z : Fin n → ℂ) (hz : z ∈ A.U p) :
    ContDiffAt ℝ ∞ (bh8_potential n Λ A p) z := by
  have hs : ContDiffAt ℝ ∞ (A.s p) z :=
    ((A.analytic p z hz).contDiffAt).restrict_scalars ℝ
  have hc (j : Fin (A.N + 1)) : ContDiffAt ℝ ∞ (fun w ↦ A.s p w j) z :=
    contDiffAt_pi.mp hs j
  have hn : ContDiffAt ℝ ∞ (fun w ↦ ∑ j, Complex.normSq (A.s p w j)) z := by
    apply ContDiffAt.sum
    intro j _
    change ContDiffAt ℝ ∞
      (fun w ↦ (A.s p w j).re * (A.s p w j).re +
        (A.s p w j).im * (A.s p w j).im) z
    have hr : ContDiffAt ℝ ∞ (fun w ↦ (A.s p w j).re) z :=
      Complex.reCLM.contDiff.contDiffAt.comp z (hc j)
    have hi : ContDiffAt ℝ ∞ (fun w ↦ (A.s p w j).im) z :=
      Complex.imCLM.contDiff.contDiffAt.comp z (hc j)
    exact (hr.mul hr).add (hi.mul hi)
  exact hn.log (bh8_chern_normSq_pos (A.s p z) (A.nonzero p z hz)).ne'

/-- Differentiating a fixed directional derivative evaluates the real Hessian. -/
theorem bh8_chern_fderiv_direction {n : ℕ} (P : (Fin n → ℂ) → ℝ)
    (z v w : Fin n → ℂ) (hP : DifferentiableAt ℝ (fderiv ℝ P) z) :
    fderiv ℝ (fun p ↦ fderiv ℝ P p w) z v = fderiv ℝ (fderiv ℝ P) z v w := by
  rw [fderiv_clm_apply hP (differentiableAt_const w)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]

/-- The curvature is the exterior derivative of the normalized chart connection
 at its anchor point. -/
theorem bh8_chern_curvature_primitive (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (z v w : Fin n → ℂ) :
    bh8_curvature n Λ A z v w =
      fderiv ℝ (fun p ↦ -(1 / (4 * Real.pi)) *
        fderiv ℝ (bh8_potential n Λ A z) p (Complex.I • w)) z v -
      fderiv ℝ (fun p ↦ -(1 / (4 * Real.pi)) *
        fderiv ℝ (bh8_potential n Λ A z) p (Complex.I • v)) z w := by
  have hP : DifferentiableAt ℝ (fderiv ℝ (bh8_potential n Λ A z)) z :=
    ((bh8_chern_potential_contDiffAt n Λ A z z (A.anchor z)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd (u : Fin n → ℂ) :
      DifferentiableAt ℝ (fun p ↦ fderiv ℝ (bh8_potential n Λ A z) p u) z :=
    hP.clm_apply (differentiableAt_const u)
  rw [fderiv_const_mul (hd _), fderiv_const_mul (hd _)]
  simp only [smul_apply, smul_eq_mul, bh8_chern_fderiv_direction _ _ _ _ hP]
  simp only [bh8_curvature, bh8_complexStructure, smul_apply,
    sub_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply]
  change (1 / (4 * Real.pi)) *
    (fderiv ℝ (fderiv ℝ (bh8_potential n Λ A z)) z w (Complex.I • v) -
      fderiv ℝ (fderiv ℝ (bh8_potential n Λ A z)) z v (Complex.I • w)) = _
  ring

/-- The imaginary part commutes with real differentiation of a holomorphic function. -/
theorem bh8_chern_fderiv_im {n : ℕ} (g : (Fin n → ℂ) → ℂ)
    (z v : Fin n → ℂ) (hg : DifferentiableAt ℂ g z) :
    fderiv ℝ (fun w ↦ (g w).im) z v = (fderiv ℂ g z v).im := by
  have hd := Complex.imCLM.hasFDerivAt.comp z (hg.hasFDerivAt.restrictScalars ℝ)
  simp only [Function.comp_def, Complex.imCLM_apply] at hd
  rw [hd.fderiv]
  rfl

/-- The real part of a holomorphic function has zero complex-antisymmetrized Hessian. -/
theorem bh8_chern_pluriharmonic {n : ℕ} (g : (Fin n → ℂ) → ℂ)
    (z v w : Fin n → ℂ) (hg : AnalyticAt ℂ g z) :
    fderiv ℝ (fderiv ℝ (fun p ↦ (g p).re)) z v (Complex.I • w) =
      fderiv ℝ (fderiv ℝ (fun p ↦ (g p).re)) z w (Complex.I • v) := by
  have hgr : ContDiffAt ℝ ∞ (fun p ↦ (g p).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z (hg.contDiffAt.restrict_scalars ℝ)
  have hgi : ContDiffAt ℝ ∞ (fun p ↦ (g p).im) z :=
    Complex.imCLM.contDiff.contDiffAt.comp z (hg.contDiffAt.restrict_scalars ℝ)
  have hdr : DifferentiableAt ℝ (fderiv ℝ (fun p ↦ (g p).re)) z :=
    (hgr.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdi : DifferentiableAt ℝ (fderiv ℝ (fun p ↦ (g p).im)) z :=
    (hgi.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he (u : Fin n → ℂ) :
      (fun p ↦ fderiv ℝ (fun q ↦ (g q).re) p (Complex.I • u)) =ᶠ[𝓝 z]
        (fun p ↦ -fderiv ℝ (fun q ↦ (g q).im) p u) := by
    filter_upwards [hg.eventually_analyticAt] with p hp
    rw [bh8_chern_fderiv_re_I g p u hp.differentiableAt,
      bh8_chern_fderiv_im g p u hp.differentiableAt]
  have hh (u t : Fin n → ℂ) :
      fderiv ℝ (fderiv ℝ (fun p ↦ (g p).re)) z t (Complex.I • u) =
        -fderiv ℝ (fderiv ℝ (fun p ↦ (g p).im)) z t u := by
    rw [← bh8_chern_fderiv_direction _ z t _ hdr, (he u).fderiv_eq,
      fderiv_fun_neg]
    simp only [neg_apply, bh8_chern_fderiv_direction _ z t u hdi]
  rw [hh, hh, (hgi.isSymmSndFDerivAt (by norm_num)).eq v w]

/-- Compatible exponential transition values give an integral corner contribution. -/
theorem bh8_chern_corner_integer (a b c d : ℂ)
    (h : Complex.exp a * Complex.exp b = Complex.exp c * Complex.exp d) :
    ∃ k : ℤ, (a.im + b.im - c.im - d.im) / (2 * Real.pi) = k := by
  rw [← Complex.exp_add, ← Complex.exp_add] at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨k, ?_⟩
  have hi := congrArg Complex.im hk
  norm_num [Complex.mul_im, Complex.mul_re] at hi
  apply (div_eq_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)).mpr
  linarith

/-- Green's formula on the parameter square, retaining its coordinate Lebesgue measure. -/
theorem bh8_chern_green_square (f g : (Fin 2 → ℝ) → ℝ)
    (hf : ∀ x ∈ Icc (0 : Fin 2 → ℝ) 1, ContDiffAt ℝ 1 f x)
    (hg : ∀ x ∈ Icc (0 : Fin 2 → ℝ) 1, ContDiffAt ℝ 1 g x) :
    (∫ t in Icc (0 : Fin 2 → ℝ) 1,
      fderiv ℝ g t (Pi.single 0 1) - fderiv ℝ f t (Pi.single 1 1)) =
      ((∫ t in Icc (0 : Fin 1 → ℝ) 1, g ![1, t 0]) -
        ∫ t in Icc (0 : Fin 1 → ℝ) 1, g ![0, t 0]) -
      ((∫ t in Icc (0 : Fin 1 → ℝ) 1, f ![t 0, 1]) -
        ∫ t in Icc (0 : Fin 1 → ℝ) 1, f ![t 0, 0]) := by
  let F : Fin 2 → (Fin 2 → ℝ) → ℝ := ![g, -f]
  let F' : Fin 2 → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ :=
    ![fderiv ℝ g, fun x ↦ -fderiv ℝ f x]
  have hcf : ContinuousOn f (Icc (0 : Fin 2 → ℝ) 1) :=
    fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hcg : ContinuousOn g (Icc (0 : Fin 2 → ℝ) 1) :=
    fun x hx ↦ (hg x hx).continuousAt.continuousWithinAt
  have hcdf : ContinuousOn (fderiv ℝ f) (Icc (0 : Fin 2 → ℝ) 1) :=
    fun x hx ↦ ((hf x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hcdg : ContinuousOn (fderiv ℝ g) (Icc (0 : Fin 2 → ℝ) 1) :=
    fun x hx ↦ ((hg x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hdiv : ∀ x, (∑ i, F' i x (Pi.single i 1)) =
      fderiv ℝ g x (Pi.single 0 1) - fderiv ℝ f x (Pi.single 1 1) := by
    intro x
    simp only [Fin.sum_univ_two, F', Matrix.cons_val_zero, Matrix.cons_val_one,
      neg_apply, sub_eq_add_neg]
  have hi : MeasureTheory.IntegrableOn (fun x ↦ ∑ i, F' i x (Pi.single i 1))
      (Icc (0 : Fin 2 → ℝ) 1) := by
    simp only [hdiv]
    exact ((hcdg.clm_apply continuousOn_const).sub
      (hcdf.clm_apply continuousOn_const)).integrableOn_Icc
  have hG := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin 2 → ℝ) 1 (by intro i; norm_num) F F' ∅ Set.countable_empty
    (fun i ↦ by fin_cases i; exact hcg; exact hcf.neg)
    (fun x hx i ↦ by
      have hx' : x ∈ Icc (0 : Fin 2 → ℝ) 1 := by
        constructor
        · intro j; exact (hx.1 j (Set.mem_univ j)).1.le
        · intro j; exact (hx.1 j (Set.mem_univ j)).2.le
      fin_cases i
      · exact ((hg x hx').differentiableAt (by norm_num)).hasFDerivAt
      · exact ((hf x hx').differentiableAt (by norm_num)).hasFDerivAt.neg) hi
  simp only [hdiv] at hG
  have h0 (c : ℝ) (t : Fin 1 → ℝ) : (0 : Fin 2).insertNth c t = ![c, t 0] := by
    ext i
    fin_cases i <;> simp [Fin.insertNth]
  have h1 (c : ℝ) (t : Fin 1 → ℝ) : (1 : Fin 2).insertNth c t = ![t 0, c] := by
    ext i
    fin_cases i
    · exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 2 ↦ ℝ) (1 : Fin 2) c t (0 : Fin 1)
    · exact Fin.insertNth_apply_same (α := fun _ : Fin 2 ↦ ℝ) (1 : Fin 2) c t
  simpa [Fin.sum_univ_two, F, h0, h1, MeasureTheory.integral_neg,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hG

/-- Green's formula for a potential pulled back along an affine square. -/
theorem bh8_chern_green_potential {n : ℕ} (P : (Fin n → ℂ) → ℝ)
    (z : Fin n → ℂ) (L : (Fin 2 → ℝ) →L[ℝ] (Fin n → ℂ))
    (hP : ∀ t ∈ Icc (0 : Fin 2 → ℝ) 1, ContDiffAt ℝ ∞ P (z + L t)) :
    let v := L (Pi.single 0 1)
    let w := L (Pi.single 1 1)
    let C := fun u t ↦ -(1 / (4 * Real.pi)) * fderiv ℝ P (z + L t) (Complex.I • u)
    (∫ t in Icc (0 : Fin 2 → ℝ) 1,
      (fderiv ℝ (fderiv ℝ P) (z + L t) w (Complex.I • v) -
        fderiv ℝ (fderiv ℝ P) (z + L t) v (Complex.I • w)) / (4 * Real.pi)) =
      ((∫ t in Icc (0 : Fin 1 → ℝ) 1, C w ![1, t 0]) -
        ∫ t in Icc (0 : Fin 1 → ℝ) 1, C w ![0, t 0]) -
      ((∫ t in Icc (0 : Fin 1 → ℝ) 1, C v ![t 0, 1]) -
        ∫ t in Icc (0 : Fin 1 → ℝ) 1, C v ![t 0, 0]) := by
  let C := fun (u : Fin n → ℂ) (t : Fin 2 → ℝ) ↦
    -(1 / (4 * Real.pi)) * fderiv ℝ P (z + L t) (Complex.I • u)
  have hS (t : Fin 2 → ℝ) : HasFDerivAt (fun t ↦ z + L t) L t :=
    L.hasFDerivAt.const_add z
  have hSC (t : Fin 2 → ℝ) : ContDiffAt ℝ ∞ (fun t ↦ z + L t) t :=
    contDiffAt_const.add L.contDiff.contDiffAt
  have hC (u : Fin n → ℂ) (t : Fin 2 → ℝ) (ht : t ∈ Icc 0 1) :
      ContDiffAt ℝ 1 (C u) t := by
    have hD : ContDiffAt ℝ 1 (fderiv ℝ P) (z + L t) :=
      (hP t ht).fderiv_right (by norm_num)
    have hA : ContDiffAt ℝ 1
        (fun t ↦ fderiv ℝ P (z + L t) (Complex.I • u)) t :=
      (hD.comp t ((hSC t).of_le (by norm_num))).clm_apply contDiffAt_const
    exact contDiffAt_const.mul hA
  have hdC (u : Fin n → ℂ) (t a : Fin 2 → ℝ) (ht : t ∈ Icc 0 1) :
      fderiv ℝ (C u) t a = -(1 / (4 * Real.pi)) *
        fderiv ℝ (fderiv ℝ P) (z + L t) (L a) (Complex.I • u) := by
    have hD : DifferentiableAt ℝ (fderiv ℝ P) (z + L t) :=
      ((hP t ht).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hE : HasFDerivAt (fun p ↦ fderiv ℝ P p (Complex.I • u))
        ((fderiv ℝ (fderiv ℝ P) (z + L t)).flip (Complex.I • u)) (z + L t) := by
      simpa only [ContinuousLinearMap.comp_zero, zero_add] using
        hD.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • u) (z + L t))
    have h := (hE.comp t (hS t)).const_mul (-(1 / (4 * Real.pi)))
    change fderiv ℝ (fun t ↦ -(1 / (4 * Real.pi)) *
      fderiv ℝ P (z + L t) (Complex.I • u)) t a = _
    simp only [Function.comp_def] at h
    rw [h.fderiv]
    rfl
  have hG := bh8_chern_green_square (C (L (Pi.single 0 1)))
    (C (L (Pi.single 1 1))) (hC _) (hC _)
  refine Eq.trans ?_ hG
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [hdC _ _ _ ht, hdC _ _ _ ht]
  ring

/-- The real Hessian is additive for smooth potentials. -/
theorem bh8_chern_hessian_add {n : ℕ} (P Q : (Fin n → ℂ) → ℝ)
    (z v w : Fin n → ℂ) (hP : ContDiffAt ℝ ∞ P z) (hQ : ContDiffAt ℝ ∞ Q z) :
    fderiv ℝ (fderiv ℝ (fun p ↦ P p + Q p)) z v w =
      fderiv ℝ (fderiv ℝ P) z v w + fderiv ℝ (fderiv ℝ Q) z v w := by
  have he : fderiv ℝ (fun p ↦ P p + Q p) =ᶠ[𝓝 z]
      (fun p ↦ fderiv ℝ P p + fderiv ℝ Q p) := by
    filter_upwards [(hP.of_le (show (2 : ℕ∞ω) ≤ ∞ by norm_num)).eventually (by norm_num),
      (hQ.of_le (show (2 : ℕ∞ω) ≤ ∞ by norm_num)).eventually (by norm_num)] with p hp hq
    exact fderiv_add (hp.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num))
  have hp : DifferentiableAt ℝ (fderiv ℝ P) z :=
    (hP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hq : DifferentiableAt ℝ (fderiv ℝ Q) z :=
    (hQ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [he.fderiv_eq, fderiv_fun_add hp hq]
  rfl

/-- Adding a holomorphic real part leaves the complex-antisymmetrized Hessian unchanged. -/
theorem bh8_chern_hessian_gauge {n : ℕ} (P Q : (Fin n → ℂ) → ℝ)
    (g : (Fin n → ℂ) → ℂ) (z v w : Fin n → ℂ)
    (hP : ContDiffAt ℝ ∞ P z) (hg : AnalyticAt ℂ g z)
    (he : Q =ᶠ[𝓝 z] (fun p ↦ P p + (g p).re)) :
    fderiv ℝ (fderiv ℝ Q) z w (Complex.I • v) -
      fderiv ℝ (fderiv ℝ Q) z v (Complex.I • w) =
    fderiv ℝ (fderiv ℝ P) z w (Complex.I • v) -
      fderiv ℝ (fderiv ℝ P) z v (Complex.I • w) := by
  have hgr : ContDiffAt ℝ ∞ (fun p ↦ (g p).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z (hg.contDiffAt.restrict_scalars ℝ)
  rw [(he.fderiv (𝕜 := ℝ)).fderiv_eq]
  rw [bh8_chern_hessian_add _ _ _ _ _ hP hgr,
    bh8_chern_hessian_add _ _ _ _ _ hP hgr,
    bh8_chern_pluriharmonic g z w v hg]
  ring

/-- On a chart the anchored curvature equals the Hessian formula in that fixed chart. -/
theorem bh8_chern_curvature_in_chart (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p z v w : Fin n → ℂ) (hz : z ∈ A.U p) :
    bh8_curvature n Λ A z v w =
      (fderiv ℝ (fderiv ℝ (bh8_potential n Λ A p)) z w (Complex.I • v) -
        fderiv ℝ (fderiv ℝ (bh8_potential n Λ A p)) z v (Complex.I • w)) /
        (4 * Real.pi) := by
  obtain ⟨g, hg, he⟩ := bh8_chern_potential_transition_log n Λ A 0 p z z hz
    (by simpa only [Submodule.coe_zero, add_zero] using A.anchor z)
  have he' : bh8_potential n Λ A z =ᶠ[𝓝 z]
      (fun q ↦ bh8_potential n Λ A p q + (2 * g q).re) := by
    filter_upwards [he] with q hq
    simpa [Complex.mul_re, add_comm] using hq
  have h := bh8_chern_hessian_gauge (bh8_potential n Λ A p)
    (bh8_potential n Λ A z) (fun q ↦ 2 * g q) z v w
    (bh8_chern_potential_contDiffAt n Λ A p z hz) (analyticAt_const.mul hg) he'
  simp only [bh8_curvature, bh8_complexStructure, smul_apply,
    sub_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]
  change (1 / (4 * Real.pi)) *
    (fderiv ℝ (fderiv ℝ (bh8_potential n Λ A z)) z w (Complex.I • v) -
      fderiv ℝ (fderiv ℝ (bh8_potential n Λ A z)) z v (Complex.I • w)) = _
  rw [h]
  ring

/-- The actual curvature period satisfies Green's formula when the square lies in one chart. -/
theorem bh8_chern_surfacePeriod_in_chart (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p z l m : Fin n → ℂ)
    (hchart : ∀ t ∈ Icc (0 : Fin 2 → ℝ) 1, z + t 0 • l + t 1 • m ∈ A.U p) :
    let C := fun u q ↦ -(1 / (4 * Real.pi)) *
      fderiv ℝ (bh8_potential n Λ A p) q (Complex.I • u)
    bh8_surfacePeriod n (bh8_curvature n Λ A) z l m =
      ((∫ t in Icc (0 : Fin 1 → ℝ) 1, C m (z + l + t 0 • m)) -
        ∫ t in Icc (0 : Fin 1 → ℝ) 1, C m (z + t 0 • m)) -
      ((∫ t in Icc (0 : Fin 1 → ℝ) 1, C l (z + t 0 • l + m)) -
        ∫ t in Icc (0 : Fin 1 → ℝ) 1, C l (z + t 0 • l)) := by
  let L : (Fin 2 → ℝ) →L[ℝ] (Fin n → ℂ) :=
    (ContinuousLinearMap.proj 0).smulRight l + (ContinuousLinearMap.proj 1).smulRight m
  have hL (t : Fin 2 → ℝ) : L t = t 0 • l + t 1 • m := rfl
  have h0 : L (Pi.single 0 1) = l := by simp [hL]
  have h1 : L (Pi.single 1 1) = m := by simp [hL]
  have hP (t : Fin 2 → ℝ) (ht : t ∈ Icc 0 1) :
      ContDiffAt ℝ ∞ (bh8_potential n Λ A p) (z + L t) := by
    apply bh8_chern_potential_contDiffAt
    simpa only [hL, ← add_assoc] using hchart t ht
  have hG := bh8_chern_green_potential (bh8_potential n Λ A p) z L hP
  dsimp only at hG ⊢
  simp only [h0, h1, hL, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_smul, zero_smul, add_zero, zero_add, ← add_assoc] at hG
  refine Eq.trans ?_ hG
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro t ht
  exact bh8_chern_curvature_in_chart n Λ A p _ l m (hchart t ht)

/-- The one-coordinate face measure agrees with the ordinary unit-interval integral. -/
theorem bh8_chern_face_integral (f : ℝ → ℝ) :
    (∫ t in Icc (0 : Fin 1 → ℝ) 1, f (t 0)) = ∫ t in (0 : ℝ)..1, f t := by
  have hpre : (MeasurableEquiv.piUnique (fun _ : Fin 1 ↦ ℝ)) ⁻¹' Icc (0 : ℝ) 1 =
      Icc (0 : Fin 1 → ℝ) 1 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Icc, MeasurableEquiv.piUnique_apply]
    constructor
    · intro ht
      constructor
      · intro i; fin_cases i; exact ht.1
      · intro i; fin_cases i; exact ht.2
    · intro ht
      exact ⟨ht.1 0, ht.2 0⟩
  have h := (MeasureTheory.volume_preserving_piUnique (fun _ : Fin 1 ↦ ℝ)).setIntegral_preimage_emb
    (MeasurableEquiv.piUnique (fun _ : Fin 1 ↦ ℝ)).measurableEmbedding f (Icc (0 : ℝ) 1)
  rw [hpre] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact h

/-- An analytic logarithm's phase differential integrates to its endpoint increment. -/
theorem bh8_chern_phase_edge {n : ℕ} (g : (Fin n → ℂ) → ℂ) (z v : Fin n → ℂ)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ g (z + t • v)) :
    (∫ t in Icc (0 : Fin 1 → ℝ) 1,
      (fderiv ℂ g (z + t 0 • v) v).im / (2 * Real.pi)) =
        ((g (z + v)).im - (g z).im) / (2 * Real.pi) := by
  rw [bh8_chern_face_integral (fun t : ℝ ↦
    (fderiv ℂ g (z + t • v) v).im / (2 * Real.pi)), intervalIntegral.integral_div]
  congr 1
  have hpath (t : ℝ) : HasDerivAt (fun t : ℝ ↦ z + t • v) v t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add z
  have hd (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (fun t : ℝ ↦ (g (z + t • v)).im)
        (fderiv ℂ g (z + t • v) v).im t := by
    have h := (Complex.imCLM.hasFDerivAt.comp (z + t • v)
      ((hg t ht).differentiableAt.hasFDerivAt.restrictScalars ℝ)).comp_hasDerivAt t (hpath t)
    convert h using 1 <;> rfl
  have hc : ContinuousOn (fun t : ℝ ↦ (fderiv ℂ g (z + t • v) v).im) (Icc 0 1) := by
    intro t ht
    have hcg : ContDiffAt ℂ 1 g (z + t • v) := (hg t ht).contDiffAt
    have hD := (hcg.continuousAt_fderiv (by norm_num)).comp (x := t) (hpath t).continuousAt
    exact (Complex.continuous_im.continuousAt.comp
      (hD.clm_apply continuousAt_const)).continuousWithinAt
  have hi : IntervalIntegrable (fun t : ℝ ↦ (fderiv ℂ g (z + t • v) v).im)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hd t (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)) hi
  simpa only [one_smul, zero_smul, add_zero] using h

/-- Local logarithms can be chosen to retain the actual homogeneous-lift transition. -/
theorem bh8_chern_lift_transition_log (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (l : Λ) (p q z : Fin n → ℂ)
    (hp : z ∈ A.U p) (hq : z + l ∈ A.U q) :
    ∃ g : (Fin n → ℂ) → ℂ, AnalyticAt ℂ g z ∧
      ∀ᶠ w in 𝓝 z, A.s q (w + l) = Complex.exp (g w) • A.s p w := by
  obtain ⟨u, hu, hu0, he⟩ := A.transition l p q z hp hq
  obtain ⟨g, hg, hexp⟩ := bh8_chern_local_log u z hu hu0
  refine ⟨g, hg, ?_⟩
  filter_upwards [he, hexp] with w hw hwexp
  rw [hw, hwexp]

/-- Four compatible lift transitions produce an integral logarithmic corner sum. -/
theorem bh8_chern_lift_corner_integer {N : ℕ}
    (s₀₀ s₁₀ s₀₁ s₁₁ : Fin (N + 1) → ℂ) (hs : s₀₀ ≠ 0) (a b c d : ℂ)
    (h10 : s₁₀ = Complex.exp a • s₀₀) (h11 : s₁₁ = Complex.exp b • s₁₀)
    (h01 : s₀₁ = Complex.exp c • s₀₀) (h11' : s₁₁ = Complex.exp d • s₀₁) :
    ∃ k : ℤ, (a.im + b.im - c.im - d.im) / (2 * Real.pi) = k := by
  apply bh8_chern_corner_integer
  apply bh8_chern_transition_unique s₀₀ hs
  rw [mul_comm (Complex.exp a), mul_comm (Complex.exp c), mul_smul, mul_smul,
    ← h10, ← h01, ← h11, ← h11']

/-- A uniform parameter-space radius makes every small part of an affine square
lie in a single atlas chart. -/
theorem bh8_chern_chart_radius (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (z l m : Fin n → ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : Fin 2 → ℝ) 1,
      ∃ p, ∀ u : Fin 2 → ℝ, dist u t < δ →
        z + u 0 • l + u 1 • m ∈ A.U p := by
  let F : (Fin 2 → ℝ) → (Fin n → ℂ) := fun t ↦ z + t 0 • l + t 1 • m
  have hF : Continuous F :=
    (continuous_const.add ((continuous_apply 0).smul continuous_const)).add
      ((continuous_apply 1).smul continuous_const)
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric
    (isCompact_Icc : IsCompact (Icc (0 : Fin 2 → ℝ) 1))
    (fun p ↦ (A.open_U p).preimage hF)
    (show Icc (0 : Fin 2 → ℝ) 1 ⊆ ⋃ p, F ⁻¹' A.U p from
      fun t _ ↦ mem_iUnion.mpr ⟨F t, A.anchor (F t)⟩)
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  obtain ⟨p, hp⟩ := hcover t ht
  exact ⟨p, fun u hu ↦ hp hu⟩

/-- A sufficiently fine uniform grid places each closed subsquare in one chart. -/
theorem bh8_chern_chart_grid (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (z l m : Fin n → ℂ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i j : Fin N, ∃ p,
      ∀ u : Fin 2 → ℝ,
        u ∈ Icc ![(i : ℝ) / N, (j : ℝ) / N]
          ![((i : ℝ) + 1) / N, ((j : ℝ) + 1) / N] →
        z + u 0 • l + u 1 • m ∈ A.U p := by
  obtain ⟨δ, hδ, hcover⟩ := bh8_chern_chart_radius n Λ A z l m
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hδ
  let N := M + 1
  have hN : (0 : ℝ) < N := by positivity
  have hmesh : 1 / (N : ℝ) < δ := by exact_mod_cast hM
  refine ⟨N, Nat.succ_pos _, ?_⟩
  intro i j
  let t : Fin 2 → ℝ := ![(i : ℝ) / N, (j : ℝ) / N]
  have ht : t ∈ Icc (0 : Fin 2 → ℝ) 1 := by
    constructor
    · intro k
      fin_cases k <;> dsimp [t] <;> positivity
    · intro k
      fin_cases k
      · exact (div_le_one hN).mpr (by exact_mod_cast i.isLt.le)
      · exact (div_le_one hN).mpr (by exact_mod_cast j.isLt.le)
  obtain ⟨p, hp⟩ := hcover t ht
  refine ⟨p, fun u hu ↦ hp u ?_⟩
  apply (dist_pi_lt_iff hδ).mpr
  intro k
  have hlo := hu.1 k
  have hhi := hu.2 k
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hbound : u k - t k ≤ 1 / (N : ℝ) := by
    fin_cases k <;> dsimp [t] at * <;> rw [add_div] at hhi <;> linarith
  exact hbound.trans_lt hmesh

/-- In affine coordinates each cell of a sufficiently fine grid lies in a chart. -/
theorem bh8_chern_chart_grid_affine (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (z l m : Fin n → ℂ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i j : Fin N, ∃ p,
      ∀ t ∈ Icc (0 : Fin 2 → ℝ) 1,
        (z + ((i : ℝ) / N) • l + ((j : ℝ) / N) • m) +
          t 0 • ((N : ℝ)⁻¹ • l) + t 1 • ((N : ℝ)⁻¹ • m) ∈ A.U p := by
  obtain ⟨N, hN, hgrid⟩ := bh8_chern_chart_grid n Λ A z l m
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨N, hN, ?_⟩
  intro i j
  obtain ⟨p, hp⟩ := hgrid i j
  refine ⟨p, ?_⟩
  intro t ht
  let u : Fin 2 → ℝ := ![((i : ℝ) + t 0) / N, ((j : ℝ) + t 1) / N]
  have hu : u ∈ Icc ![(i : ℝ) / N, (j : ℝ) / N]
      ![((i : ℝ) + 1) / N, ((j : ℝ) + 1) / N] := by
    constructor
    · intro k
      fin_cases k <;> dsimp [u]
      · exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (ht.1 0)) hNr.le
      · exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (ht.1 1)) hNr.le
    · intro k
      fin_cases k <;> dsimp [u]
      · exact div_le_div_of_nonneg_right (add_le_add_right (show t 0 ≤ 1 from ht.2 0) _) hNr.le
      · exact div_le_div_of_nonneg_right (add_le_add_right (show t 1 ≤ 1 from ht.2 1) _) hNr.le
  have he : z + u 0 • l + u 1 • m =
      (z + ((i : ℝ) / N) • l + ((j : ℝ) / N) • m) +
        t 0 • ((N : ℝ)⁻¹ • l) + t 1 • ((N : ℝ)⁻¹ • m) := by
    dsimp [u]
    simp only [div_eq_mul_inv, add_mul, add_smul, smul_smul]
    abel
  exact he ▸ hp u hu

/-- A logarithmic gauge change shifts the normalized connection by the phase differential. -/
theorem bh8_chern_connection_gauge {n : ℕ} (P Q : (Fin n → ℂ) → ℝ)
    (g : (Fin n → ℂ) → ℂ) (a z v : Fin n → ℂ)
    (hP : DifferentiableAt ℝ P z) (hg : AnalyticAt ℂ g z)
    (he : (fun w ↦ Q (w + a)) =ᶠ[𝓝 z] (fun w ↦ P w + 2 * (g w).re)) :
    -(1 / (4 * Real.pi)) * fderiv ℝ Q (z + a) (Complex.I • v) -
      (-(1 / (4 * Real.pi)) * fderiv ℝ P z (Complex.I • v)) =
        (fderiv ℂ g z v).im / (2 * Real.pi) := by
  have hgr : DifferentiableAt ℝ (fun w ↦ (g w).re) z :=
    (Complex.reCLM.hasFDerivAt.comp z
      (hg.differentiableAt.hasFDerivAt.restrictScalars ℝ)).differentiableAt
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp_add_right, fderiv_fun_add hP (hgr.const_mul 2),
    fderiv_const_mul hgr] at hd
  rw [hd]
  simp only [add_apply, smul_apply, smul_eq_mul,
    bh8_chern_fderiv_re_I g z v hg.differentiableAt]
  ring

/-- The pointwise scalar between two atlas lifts is a single analytic nonvanishing
function on their translated overlap. -/
theorem bh8_chern_overlap_unit (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (a : Λ) (p q : Fin n → ℂ) :
    ∃ u : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ u (A.U p ∩ (fun w ↦ w + a) ⁻¹' A.U q) ∧
      ∀ z ∈ A.U p ∩ (fun w ↦ w + a) ⁻¹' A.U q,
        u z ≠ 0 ∧ A.s q (z + a) = u z • A.s p z := by
  classical
  have hv (z : Fin n → ℂ) : ∃ c : ℂ,
      z ∈ A.U p ∩ (fun w ↦ w + a) ⁻¹' A.U q →
        c ≠ 0 ∧ A.s q (z + a) = c • A.s p z := by
    by_cases hz : z ∈ A.U p ∩ (fun w ↦ w + a) ⁻¹' A.U q
    · obtain ⟨u, _, hu0, he⟩ := A.transition a p q z hz.1 hz.2
      exact ⟨u z, fun _ ↦ ⟨hu0, he.self_of_nhds⟩⟩
    · exact ⟨1, fun h ↦ (hz h).elim⟩
  choose u hu using hv
  refine ⟨u, ?_, hu⟩
  intro z hz
  obtain ⟨v, hv, _, he⟩ := A.transition a p q z hz.1 hz.2
  have hopen : IsOpen (A.U p ∩ (fun w ↦ w + a) ⁻¹' A.U q) :=
    (A.open_U p).inter ((A.open_U q).preimage (continuous_id.add continuous_const))
  have huv : u =ᶠ[𝓝 z] v := by
    filter_upwards [hopen.mem_nhds hz, he] with w hw hew
    exact bh8_chern_transition_unique (A.s p w) (A.nonzero p w hw.1)
      ((hu w hw).2.symm.trans hew)
  exact hv.congr huv.symm

/-- On an overlap one logarithm controls both the lift transition and the connection change. -/
theorem bh8_chern_connection_transition (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (a : Λ) (p q z : Fin n → ℂ)
    (hp : z ∈ A.U p) (hq : z + a ∈ A.U q) :
    ∃ g : (Fin n → ℂ) → ℂ, AnalyticAt ℂ g z ∧
      (∀ᶠ w in 𝓝 z, A.s q (w + a) = Complex.exp (g w) • A.s p w) ∧
      ∀ v, -(1 / (4 * Real.pi)) *
          fderiv ℝ (bh8_potential n Λ A q) (z + a) (Complex.I • v) -
        (-(1 / (4 * Real.pi)) *
          fderiv ℝ (bh8_potential n Λ A p) z (Complex.I • v)) =
        (fderiv ℂ g z v).im / (2 * Real.pi) := by
  obtain ⟨g, hg, he⟩ := bh8_chern_lift_transition_log n Λ A a p q z hp hq
  refine ⟨g, hg, he, fun v ↦ ?_⟩
  apply bh8_chern_connection_gauge
    (bh8_potential n Λ A p) (bh8_potential n Λ A q) g a z v
    ((bh8_chern_potential_contDiffAt n Λ A p z hp).differentiableAt (by norm_num)) hg
  filter_upwards [he, (A.open_U p).mem_nhds hp] with w hw hwp
  unfold bh8_potential
  rw [hw, bh8_chern_log_normSq_smul _ (A.nonzero p w hwp) _ (Complex.exp_ne_zero _),
    bh8_chern_log_normSq_exp]
  exact add_comm _ _

/-- A continuous nonvanishing function on a closed edge has a continuous logarithm. -/
theorem bh8_chern_edge_log (q : ℝ → ℂ)
    (hq : ContinuousOn q (Icc (0 : ℝ) 1))
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, q t ≠ 0) :
    ∃ L : ℝ → ℂ, Continuous L ∧ ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = q t := by
  let p : ℝ → ℝ := fun t ↦ (projIcc (0 : ℝ) 1 (by norm_num) t : ℝ)
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpm (t : ℝ) : p t ∈ Icc (0 : ℝ) 1 := (projIcc 0 1 (by norm_num) t).property
  have hF : Continuous (fun t ↦ q (p t)) := hq.comp_continuous hp hpm
  obtain ⟨L, hL, _⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    ⟨fun t ↦ q (p t), hF⟩ (a₀ := 0) (Complex.exp_log (hn (p 0) (hpm 0)))
    (fun t ↦ hn (p t) (hpm t))
  refine ⟨L, L.continuous, ?_⟩
  intro t ht
  have he := congr_fun hL.2 t
  simpa only [Function.comp_apply, ContinuousMap.coe_mk, p, projIcc_of_mem (by norm_num) ht] using he

/-- The logarithmic derivative on an edge integrates to an increment of a continuous logarithm. -/
theorem bh8_chern_edge_log_integral (q q' : ℝ → ℂ)
    (hq : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt q (q' t) t)
    (hc : ContinuousOn q' (Icc (0 : ℝ) 1))
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, q t ≠ 0) :
    ∃ L : ℝ → ℂ, Continuous L ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = q t) ∧
      (∫ t in (0 : ℝ)..1, (q' t / q t).im / (2 * Real.pi)) =
        ((L 1).im - (L 0).im) / (2 * Real.pi) := by
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1) :=
    fun t ht ↦ (hq t ht).continuousAt.continuousWithinAt
  obtain ⟨L, hL, he⟩ := bh8_chern_edge_log q hqc hn
  refine ⟨L, hL, he, ?_⟩
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt L (q' t / q t) t := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have he' : (fun s ↦ Complex.exp (L s)) =ᶠ[𝓝 t] q := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs using he s hs
    let B : ℂ →L[ℝ] ℂ := (Complex.exp (L t))⁻¹ • (1 : ℂ →L[ℝ] ℂ)
    have hdiff : DifferentiableAt ℝ L t :=
      (HasFDerivAt.of_comp_of_leftInverse (f'symm := B) hL.continuousAt
        (Complex.hasStrictFDerivAt_exp_real (L t)).hasFDerivAt
        (hq t ht').hasFDerivAt he' (fun v ↦ by simp [B])).differentiableAt
    have hder := hdiff.hasDerivAt.cexp
    have hval : q' t = Complex.exp (L t) * deriv L t :=
      (hq t ht').unique (hder.congr_of_eventuallyEq he'.symm)
    have heq : q' t / q t = deriv L t := by
      rw [hval, he t ht', mul_div_cancel_left₀ _ (hn t ht')]
    exact heq ▸ hdiff.hasDerivAt
  have hcont : ContinuousOn (fun t ↦ (q' t / q t).im) (Icc (0 : ℝ) 1) :=
    Complex.continuous_im.comp_continuousOn (hc.div hqc hn)
  have hi : IntervalIntegrable (fun t ↦ (q' t / q t).im) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcont
  rw [intervalIntegral.integral_div]
  congr 1
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by norm_num)
    (Complex.continuous_im.comp hL).continuousOn
  · intro t ht
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hd t ht)
    exact h.hasDerivWithinAt
  · exact hi

/-- The connection change can be expressed directly through the transition unit,
independently of the chosen local logarithm. -/
theorem bh8_chern_connection_unit {n : ℕ} (P Q : (Fin n → ℂ) → ℝ)
    (u : (Fin n → ℂ) → ℂ) (a z v : Fin n → ℂ)
    (hP : DifferentiableAt ℝ P z) (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0)
    (he : (fun w ↦ Q (w + a)) =ᶠ[𝓝 z]
      (fun w ↦ P w + Real.log (Complex.normSq (u w)))) :
    -(1 / (4 * Real.pi)) * fderiv ℝ Q (z + a) (Complex.I • v) -
      (-(1 / (4 * Real.pi)) * fderiv ℝ P z (Complex.I • v)) =
        (fderiv ℂ u z v / u z).im / (2 * Real.pi) := by
  obtain ⟨g, hg, hexp⟩ := bh8_chern_local_log u z hu hu0
  have hpot : (fun w ↦ Q (w + a)) =ᶠ[𝓝 z] (fun w ↦ P w + 2 * (g w).re) := by
    filter_upwards [he, hexp] with w hw hew
    rw [hw, ← hew, bh8_chern_log_normSq_exp]
  rw [bh8_chern_connection_gauge P Q g a z v hP hg hpot]
  change (fun w ↦ Complex.exp (g w)) =ᶠ[𝓝 z] u at hexp
  have hd : fderiv ℂ u z v = u z * fderiv ℂ g z v := by
    rw [← hexp.fderiv_eq, hg.differentiableAt.hasFDerivAt.cexp.fderiv]
    simp only [smul_apply, smul_eq_mul, hexp.self_of_nhds]
  rw [hd, mul_div_cancel_left₀ _ hu0]

/-- Integrating a transition unit along an affine edge gives logarithms of its two endpoint values. -/
theorem bh8_chern_unit_edge {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z v : Fin n → ℂ)
    (hu : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ u (z + t • v))
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, u (z + t • v) ≠ 0) :
    ∃ a b : ℂ, Complex.exp a = u z ∧ Complex.exp b = u (z + v) ∧
      (∫ t in Icc (0 : Fin 1 → ℝ) 1,
        (fderiv ℂ u (z + t 0 • v) v / u (z + t 0 • v)).im / (2 * Real.pi)) =
        (b.im - a.im) / (2 * Real.pi) := by
  have hpath (t : ℝ) : HasDerivAt (fun t : ℝ ↦ z + t • v) v t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add z
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ u (z + t • v)) (fderiv ℂ u (z + t • v) v) t := by
    have h := ((hu t ht).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hpath t)
    convert h using 1 <;> rfl
  have hc : ContinuousOn (fun t : ℝ ↦ fderiv ℂ u (z + t • v) v) (Icc (0 : ℝ) 1) := by
    intro t ht
    have hD := ((hu t ht).contDiffAt (n := 1)).continuousAt_fderiv (by norm_num)
    exact ((hD.comp (x := t) (hpath t).continuousAt).clm_apply
      continuousAt_const).continuousWithinAt
  obtain ⟨L, _, he, hi⟩ := bh8_chern_edge_log_integral
    (fun t : ℝ ↦ u (z + t • v)) (fun t : ℝ ↦ fderiv ℂ u (z + t • v) v) hd hc hn
  refine ⟨L 0, L 1, ?_, ?_, ?_⟩
  · simpa only [zero_smul, add_zero] using he 0 ⟨le_rfl, zero_le_one⟩
  · simpa only [one_smul] using he 1 ⟨zero_le_one, le_rfl⟩
  · rw [bh8_chern_face_integral (fun t : ℝ ↦
      (fderiv ℂ u (z + t • v) v / u (z + t • v)).im / (2 * Real.pi))]
    exact hi

/-- The difference of chart connections along a translated overlap edge is an
endpoint logarithmic increment of the actual homogeneous-lift transition. -/
theorem bh8_chern_overlap_edge (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (a : Λ) (p q z v : Fin n → ℂ)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, z + t • v ∈ A.U p)
    (hq : ∀ t ∈ Icc (0 : ℝ) 1, z + t • v + a ∈ A.U q) :
    ∃ b c : ℂ,
      A.s q (z + a) = Complex.exp b • A.s p z ∧
      A.s q (z + v + a) = Complex.exp c • A.s p (z + v) ∧
      (∫ t in Icc (0 : Fin 1 → ℝ) 1,
        -(1 / (4 * Real.pi)) *
            fderiv ℝ (bh8_potential n Λ A q) (z + t 0 • v + a) (Complex.I • v) -
          (-(1 / (4 * Real.pi)) *
            fderiv ℝ (bh8_potential n Λ A p) (z + t 0 • v) (Complex.I • v))) =
        (c.im - b.im) / (2 * Real.pi) := by
  obtain ⟨u, hu, he⟩ := bh8_chern_overlap_unit n Λ A a p q
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      z + t • v ∈ A.U p ∩ (fun w ↦ w + a) ⁻¹' A.U q := ⟨hp t ht, hq t ht⟩
  obtain ⟨b, c, hb, hc, hi⟩ := bh8_chern_unit_edge u z v
    (fun t ht ↦ hu _ (hmem t ht)) (fun t ht ↦ (he _ (hmem t ht)).1)
  refine ⟨b, c, ?_, ?_, ?_⟩
  · have h := (he _ (hmem 0 ⟨le_rfl, zero_le_one⟩)).2
    simpa only [zero_smul, add_zero, ← hb] using h
  · have h := (he _ (hmem 1 ⟨zero_le_one, le_rfl⟩)).2
    simpa only [one_smul, ← hc] using h
  · refine Eq.trans ?_ hi
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have ht' : t 0 ∈ Icc (0 : ℝ) 1 := ⟨ht.1 0, ht.2 0⟩
    apply bh8_chern_connection_unit
      (bh8_potential n Λ A p) (bh8_potential n Λ A q) u a (z + t 0 • v) v
      ((bh8_chern_potential_contDiffAt n Λ A p _ (hp _ ht')).differentiableAt (by norm_num))
      (hu _ (hmem _ ht')) (he _ (hmem _ ht')).1
    have hopen : IsOpen (A.U p ∩ (fun w ↦ w + a) ⁻¹' A.U q) :=
      (A.open_U p).inter ((A.open_U q).preimage (continuous_id.add continuous_const))
    filter_upwards [hopen.mem_nhds (hmem _ ht')] with w hw
    unfold bh8_potential
    rw [(he w hw).2, bh8_chern_log_normSq_smul _ (A.nonzero p w hw.1) _ (he w hw).1]
    exact add_comm _ _

/-- A chart connection is integrable along every closed affine edge in its chart. -/
theorem bh8_chern_connection_edge_integrable (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p z v w : Fin n → ℂ)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, z + t • v ∈ A.U p) :
    MeasureTheory.IntegrableOn (fun t : Fin 1 → ℝ ↦
      -(1 / (4 * Real.pi)) *
        fderiv ℝ (bh8_potential n Λ A p) (z + t 0 • v) (Complex.I • w))
      (Icc (0 : Fin 1 → ℝ) 1) := by
  apply ContinuousOn.integrableOn_Icc
  intro t ht
  have hP := bh8_chern_potential_contDiffAt n Λ A p (z + t 0 • v)
    (hp (t 0) ⟨ht.1 0, ht.2 0⟩)
  have hd := hP.continuousAt_fderiv (by norm_num)
  have hpath : Continuous (fun t : Fin 1 → ℝ ↦ z + t 0 • v) :=
    continuous_const.add ((continuous_apply 0).smul continuous_const)
  exact (continuousAt_const.mul
    ((hd.comp (x := t) hpath.continuousAt).clm_apply continuousAt_const)).continuousWithinAt

/-- Opposite-edge transitions prove integrality whenever a period square lies in one chart. -/
theorem bh8_chern_periods_in_chart (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p z : Fin n → ℂ) (l m : Λ)
    (hchart : ∀ t ∈ Icc (0 : Fin 2 → ℝ) 1,
      z + t 0 • (l : Fin n → ℂ) + t 1 • (m : Fin n → ℂ) ∈ A.U p) :
    ∃ k : ℤ, bh8_surfacePeriod n (bh8_curvature n Λ A) z l m = k := by
  have hbox (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
      ![s, t] ∈ Icc (0 : Fin 2 → ℝ) 1 := by
    constructor
    · intro i; fin_cases i; exact hs.1; exact ht.1
    · intro i; fin_cases i; exact hs.2; exact ht.2
  have hL (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z + t • (m : Fin n → ℂ) ∈ A.U p := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, add_zero] using
      hchart ![0, t] (hbox 0 t ⟨le_rfl, zero_le_one⟩ ht)
  have hR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z + t • (m : Fin n → ℂ) + l ∈ A.U p := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, add_right_comm] using
      hchart ![1, t] (hbox 1 t ⟨zero_le_one, le_rfl⟩ ht)
  have hB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z + t • (l : Fin n → ℂ) ∈ A.U p := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, add_zero] using
      hchart ![t, 0] (hbox t 0 ht ⟨le_rfl, zero_le_one⟩)
  have hT (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z + t • (l : Fin n → ℂ) + m ∈ A.U p := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul] using
      hchart ![t, 1] (hbox t 1 ht ⟨zero_le_one, le_rfl⟩)
  obtain ⟨a, b, ha, hb, hV⟩ := bh8_chern_overlap_edge n Λ A l p p z m hL hR
  obtain ⟨c, d, hc, hd, hH⟩ := bh8_chern_overlap_edge n Λ A m p p z l hB hT
  have hz : z ∈ A.U p := by simpa only [zero_smul, add_zero] using hL 0 ⟨le_rfl, zero_le_one⟩
  obtain ⟨k, hk⟩ := bh8_chern_lift_corner_integer
    (A.s p z) (A.s p (z + l)) (A.s p (z + m)) (A.s p (z + l + m))
    (A.nonzero p z hz) a d c b ha hd hc (by simpa only [add_right_comm] using hb)
  have hiL := bh8_chern_connection_edge_integrable n Λ A p z m m hL
  have hiB := bh8_chern_connection_edge_integrable n Λ A p z l l hB
  have hiR := bh8_chern_connection_edge_integrable n Λ A p (z + l) m m
    (fun t ht ↦ by simpa only [add_right_comm] using hR t ht)
  have hiT := bh8_chern_connection_edge_integrable n Λ A p (z + m) l l
    (fun t ht ↦ by simpa only [add_right_comm] using hT t ht)
  have hiR' : MeasureTheory.IntegrableOn (fun t : Fin 1 → ℝ ↦
      -(1 / (4 * Real.pi)) * fderiv ℝ (bh8_potential n Λ A p)
        (z + t 0 • (m : Fin n → ℂ) + l) (Complex.I • (m : Fin n → ℂ)))
      (Icc (0 : Fin 1 → ℝ) 1) := by
    simpa only [add_right_comm] using hiR
  have hiT' : MeasureTheory.IntegrableOn (fun t : Fin 1 → ℝ ↦
      -(1 / (4 * Real.pi)) * fderiv ℝ (bh8_potential n Λ A p)
        (z + t 0 • (l : Fin n → ℂ) + m) (Complex.I • (l : Fin n → ℂ)))
      (Icc (0 : Fin 1 → ℝ) 1) := by
    simpa only [add_right_comm] using hiT
  rw [MeasureTheory.integral_sub hiR' hiL] at hV
  rw [MeasureTheory.integral_sub hiT' hiB] at hH
  have hG := bh8_chern_surfacePeriod_in_chart n Λ A p z l m hchart
  dsimp only at hG
  have hV' := hV
  simp only [add_right_comm] at hV' hG
  rw [hV'] at hG
  have hH' := hH
  simp only [add_right_comm] at hH'
  rw [hH'] at hG
  refine ⟨-k, ?_⟩
  rw [hG, Int.cast_neg, ← hk]
  ring

/-- Cousin trivialization glues the homogeneous representatives to an entire nonvanishing lift.
The only external analytic inputs are the independent stage-seven logarithmic lifting and
additive Cousin statements. -/
theorem bh8_chern_global_lift (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) :
    ∃ (S : (Fin n → ℂ) → (Fin (A.N + 1) → ℂ))
      (v : (Fin n → ℂ) → (Fin n → ℂ) → ℂ),
      AnalyticOnNhd ℂ S univ ∧
      (∀ p, AnalyticOnNhd ℂ (v p) (A.U p)) ∧
      (∀ p z, z ∈ A.U p → v p z ≠ 0) ∧
      (∀ p z, z ∈ A.U p → S z = v p z • A.s p z) := by
  classical
  have hunit (p q : Fin n → ℂ) : ∃ u : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ u (A.U p ∩ A.U q) ∧
      ∀ z ∈ A.U p ∩ A.U q, u z ≠ 0 ∧ A.s p z = u z • A.s q z := by
    obtain ⟨u, hu, he⟩ := bh8_chern_overlap_unit n Λ A 0 q p
    refine ⟨u, fun z hz ↦ hu z ⟨hz.2, ?_⟩, ?_⟩
    · simpa only [mem_preimage, Submodule.coe_zero, add_zero] using hz.1
    · intro z hz
      have h := he z ⟨hz.2, by simpa only [mem_preimage, Submodule.coe_zero, add_zero] using hz.1⟩
      simpa only [Submodule.coe_zero, add_zero] using h
  choose u hu he using hunit
  have hd (p z : Fin n → ℂ) (hz : z ∈ A.U p) : u p p z = 1 := by
    apply bh8_chern_transition_unique (A.s p z) (A.nonzero p z hz)
    rw [← (he p p z ⟨hz, hz⟩).2, one_smul]
  have hc (p q r z : Fin n → ℂ) (hz : z ∈ A.U p ∩ A.U q ∩ A.U r) :
      u p q z * u q r z = u p r z := by
    apply bh8_chern_transition_unique (A.s r z) (A.nonzero r z hz.2)
    rw [mul_smul, ← (he q r z ⟨hz.1.2, hz.2⟩).2,
      ← (he p q z hz.1).2, ← (he p r z ⟨hz.1.1, hz.2⟩).2]
  obtain ⟨v, hv, hv0, hvc⟩ := bh7_cousin_trivialization_aux n A.U A.open_U A.anchor u hu
    (fun p q z hz ↦ (he p q z hz).1) hd hc
  let S := fun z ↦ v z z • A.s z z
  have hS (p z : Fin n → ℂ) (hz : z ∈ A.U p) : S z = v p z • A.s p z := by
    dsimp [S]
    rw [(he z p z ⟨A.anchor z, hz⟩).2, smul_smul,
      hvc z p z ⟨A.anchor z, hz⟩]
  refine ⟨S, v, ?_, hv, hv0, hS⟩
  intro z _
  have hg := (hv z z (A.anchor z)).smul (A.analytic z z (A.anchor z))
  apply hg.congr
  filter_upwards [(A.open_U z).mem_nhds (A.anchor z)] with w hw
  exact (hS z w hw).symm

/-- Multiplication by a nonvanishing analytic scalar preserves immersion modulo the radial line. -/
theorem bh8_chern_gauge_immersion {n N : ℕ}
    (s : (Fin n → ℂ) → (Fin (N + 1) → ℂ)) (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hs : DifferentiableAt ℂ s z) (hu : DifferentiableAt ℂ u z)
    (hu0 : u z ≠ 0)
    (hi : ∀ (v : Fin n → ℂ) (c : ℂ), fderiv ℂ s z v = c • s z → v = 0) :
    ∀ (v : Fin n → ℂ) (c : ℂ), fderiv ℂ (fun w ↦ u w • s w) z v = c • (u z • s z) → v = 0 := by
  intro v c h
  rw [fderiv_fun_smul hu hs] at h
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_smul] at h
  have he : u z • fderiv ℂ s z v = (c * u z - fderiv ℂ u z v) • s z := by
    rw [sub_smul, eq_sub_iff_add_eq]
    exact h
  have he' := congrArg (fun x ↦ (u z)⁻¹ • x) he
  simp only [smul_smul, inv_mul_cancel₀ hu0, one_smul] at he'
  exact hi v _ he'

/-- The entire lift gives an atlas with a global chart and the original curvature. -/
theorem bh8_chern_global_atlas (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) :
    ∃ B : bh8_ProjectiveAtlas n Λ,
      (∀ p, B.U p = univ) ∧ bh8_curvature n Λ B = bh8_curvature n Λ A := by
  obtain ⟨S, v, hS, hv, hv0, hloc⟩ := bh8_chern_global_lift n Λ A
  have hlocal (p z : Fin n → ℂ) (hz : z ∈ A.U p) :
      S =ᶠ[𝓝 z] (fun w ↦ v p w • A.s p w) := by
    filter_upwards [(A.open_U p).mem_nhds hz] with w hw using hloc p w hw
  have hn (z : Fin n → ℂ) : S z ≠ 0 := by
    rw [hloc z z (A.anchor z)]
    exact smul_ne_zero (hv0 z z (A.anchor z)) (A.nonzero z z (A.anchor z))
  have himm (z w : Fin n → ℂ) (c : ℂ) (he : fderiv ℂ S z w = c • S z) : w = 0 := by
    rw [(hlocal z z (A.anchor z)).fderiv_eq, hloc z z (A.anchor z)] at he
    exact bh8_chern_gauge_immersion (A.s z) (v z) z
      (A.analytic z z (A.anchor z)).differentiableAt
      (hv z z (A.anchor z)).differentiableAt (hv0 z z (A.anchor z))
      (A.immersion z z (A.anchor z)) w c he
  have htrans (a : Λ) (z : Fin n → ℂ) :
      ∃ e : (Fin n → ℂ) → ℂ, AnalyticAt ℂ e z ∧ e z ≠ 0 ∧
        ∀ᶠ w in 𝓝 z, S (w + a) = e w • S w := by
    obtain ⟨e, he, he0, heq⟩ := A.transition a z (z + a) z (A.anchor z) (A.anchor (z + a))
    let e' := fun w ↦ v (z + a) (w + a) * e w / v z w
    have hvq : AnalyticAt ℂ (fun w ↦ v (z + a) (w + a)) z :=
      (hv (z + a) (z + a) (A.anchor (z + a))).comp
        (f := fun w ↦ w + (a : Fin n → ℂ)) (x := z) (analyticAt_id.add analyticAt_const)
    have hvp := hv z z (A.anchor z)
    refine ⟨e', (hvq.mul he).div hvp (hv0 z z (A.anchor z)),
      div_ne_zero (mul_ne_zero (hv0 (z + a) (z + a) (A.anchor (z + a))) he0)
        (hv0 z z (A.anchor z)), ?_⟩
    have hq : ∀ᶠ w in 𝓝 z, w + (a : Fin n → ℂ) ∈ A.U (z + a) :=
      (show Continuous (fun w : Fin n → ℂ ↦ w + (a : Fin n → ℂ)) from
        continuous_id.add continuous_const).continuousAt.eventually
        ((A.open_U (z + a)).mem_nhds (A.anchor (z + a)))
    filter_upwards [heq, (A.open_U z).mem_nhds (A.anchor z), hq] with w hw hp hq
    rw [hloc (z + a) (w + a) hq, hloc z w hp, hw]
    dsimp [e']
    rw [smul_smul, smul_smul, div_mul_cancel₀ _ (hv0 z w hp)]
  let B : bh8_ProjectiveAtlas n Λ :=
    { N := A.N
      U := fun _ ↦ univ
      s := fun _ ↦ S
      open_U := fun _ ↦ isOpen_univ
      anchor := fun _ ↦ mem_univ _
      analytic := fun _ ↦ hS
      nonzero := fun _ z _ ↦ hn z
      immersion := fun _ z _ w c ↦ himm z w c
      transition := fun a _ _ z _ _ ↦ htrans a z }
  refine ⟨B, fun _ ↦ rfl, ?_⟩
  funext z
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro t
  obtain ⟨g, hg, he⟩ := bh8_chern_local_log (v z) z
    (hv z z (A.anchor z)) (hv0 z z (A.anchor z))
  have hpot : bh8_potential n Λ B z =ᶠ[𝓝 z]
      (fun x ↦ bh8_potential n Λ A z x + (2 * g x).re) := by
    filter_upwards [(A.open_U z).mem_nhds (A.anchor z), he] with x hx hexp
    change Real.log (∑ j, Complex.normSq (S x j)) =
      Real.log (∑ j, Complex.normSq (A.s z x j)) + (2 * g x).re
    rw [hloc z x hx, bh8_chern_log_normSq_smul _ (A.nonzero z x hx) _ (hv0 z x hx),
      ← hexp, bh8_chern_log_normSq_exp]
    simp [Complex.mul_re, add_comm]
  have hH := bh8_chern_hessian_gauge (bh8_potential n Λ A z)
    (bh8_potential n Λ B z) (fun x ↦ 2 * g x) z w t
    (bh8_chern_potential_contDiffAt n Λ A z z (A.anchor z))
    (analyticAt_const.mul hg) hpot
  rw [bh8_chern_curvature_in_chart n Λ B z z w t (mem_univ _),
    bh8_chern_curvature_in_chart n Λ A z z w t (A.anchor z), hH]

/-- The normalized curvature has integral periods on every lattice parallelogram.
The integer comes from the transition functions of O(1), before translation averaging.
Source: Griffiths--Harris, Chapter 1, section 1, first Chern class and curvature;
Birkenhake--Lange, section 2.1, integral alternating forms. -/
theorem bh8_chern_periods_aux (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (z : Fin n → ℂ) (l m : Λ) :
    ∃ k : ℤ, bh8_surfacePeriod n (bh8_curvature n Λ A) z l m = k := by
  obtain ⟨B, hB, hcurv⟩ := bh8_chern_global_atlas n Λ A
  rw [← hcurv]
  apply bh8_chern_periods_in_chart n Λ B z z l m
  intro t _
  rw [hB z]
  exact mem_univ _

private theorem bh8_average_integrable (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (b : Module.Basis (Fin (2 * n)) ℤ Λ)
    (form : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) :
    IntegrableOn (fun t : Fin (2 * n) → ℝ ↦ form (∑ j, t j • (b j : Fin n → ℂ)))
      (Icc 0 1) := by
  apply Continuous.integrableOn_Icc
  exact hform.continuous.comp (continuous_finset_sum _ fun j _ ↦
    continuous_apply j |>.smul continuous_const)

private theorem bh8_average_alternating (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (b : Module.Basis (Fin (2 * n)) ℤ Λ)
    (form : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) (halt : ∀ p v, form p v v = 0) :
    ∀ v, bh8_average n Λ b form v v = 0 := by
  intro v
  have hi := bh8_average_integrable n Λ b form hform
  have hiv : IntegrableOn (fun t : Fin (2 * n) → ℝ ↦
      form (∑ j, t j • (b j : Fin n → ℂ)) v) (Icc 0 1) := by
    exact (ContinuousLinearMap.apply ℝ _ v).integrable_comp hi
  rw [bh8_average, ContinuousLinearMap.integral_apply hi v,
    ContinuousLinearMap.integral_apply hiv v]
  simp only [halt, integral_zero]

private theorem bh8_average_type_one_one (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (b : Module.Basis (Fin (2 * n)) ℤ Λ)
    (form : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form)
    (h11 : ∀ p, IsTypeOneOne (fun v w ↦ form p v w)) :
    IsTypeOneOne (fun v w ↦ bh8_average n Λ b form v w) := by
  intro v w
  simp only [bh8_average]
  have hi := bh8_average_integrable n Λ b form hform
  rw [ContinuousLinearMap.integral_apply hi (Complex.I • v),
    ContinuousLinearMap.integral_apply hi v]
  have hiIv : IntegrableOn (fun t : Fin (2 * n) → ℝ ↦
      form (∑ j, t j • (b j : Fin n → ℂ)) (Complex.I • v)) (Icc 0 1) := by
    exact (ContinuousLinearMap.apply ℝ _ (Complex.I • v)).integrable_comp hi
  have hiv : IntegrableOn (fun t : Fin (2 * n) → ℝ ↦
      form (∑ j, t j • (b j : Fin n → ℂ)) v) (Icc 0 1) := by
    exact (ContinuousLinearMap.apply ℝ _ v).integrable_comp hi
  rw [ContinuousLinearMap.integral_apply hiIv (Complex.I • w),
    ContinuousLinearMap.integral_apply hiv w]
  apply integral_congr_ae
  filter_upwards with t
  exact h11 _ v w

private theorem bh8_average_positive (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (b : Module.Basis (Fin (2 * n)) ℤ Λ)
    (form : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form)
    (hpos : ∀ p v, v ≠ 0 → 0 < form p v (Complex.I • v)) :
    ∀ v, v ≠ 0 → 0 < bh8_average n Λ b form v (Complex.I • v) := by
  intro v hv
  have hi := bh8_average_integrable n Λ b form hform
  have hiv : IntegrableOn (fun t : Fin (2 * n) → ℝ ↦
      form (∑ j, t j • (b j : Fin n → ℂ)) v) (Icc 0 1) := by
    exact (ContinuousLinearMap.apply ℝ _ v).integrable_comp hi
  have his : IntegrableOn (fun t : Fin (2 * n) → ℝ ↦
      form (∑ j, t j • (b j : Fin n → ℂ)) v (Complex.I • v)) (Icc 0 1) := by
    exact (ContinuousLinearMap.apply ℝ _ (Complex.I • v)).integrable_comp hiv
  rw [bh8_average, ContinuousLinearMap.integral_apply hi v,
    ContinuousLinearMap.integral_apply hiv (Complex.I • v)]
  rw [integral_pos_iff_support_of_nonneg (fun t ↦ (hpos _ v hv).le) his]
  have hs : Function.support (fun t : Fin (2 * n) → ℝ ↦
      form (∑ j, t j • (b j : Fin n → ℂ)) v (Complex.I • v)) = Set.univ := by
    ext t
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    exact (hpos _ v hv).ne'
  rw [hs]
  simp only [Measure.restrict_apply_univ, Real.volume_Icc_pi, Pi.one_apply, Pi.zero_apply,
    sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, zero_lt_one]

/-- The flux of a closed two-form through an affine parameter cube vanishes. -/
theorem bh8_average_closed_cube {n : ℕ}
    (form : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form)
    (hclosed : ∀ p u v w,
      fderiv ℝ form p u v w + fderiv ℝ form p v w u + fderiv ℝ form p w u v = 0)
    (z : Fin n → ℂ) (L : (Fin 3 → ℝ) →L[ℝ] (Fin n → ℂ)) :
    let v := fun i : Fin 3 ↦ L (Pi.single i 1)
    let F := fun i t ↦ form (z + L t) (v (i + 1)) (v (i + 2))
    (∑ i : Fin 3,
      ((∫ t in Icc (0 : Fin 2 → ℝ) 1, F i (i.insertNth 1 t)) -
        ∫ t in Icc (0 : Fin 2 → ℝ) 1, F i (i.insertNth 0 t))) = 0 := by
  let v := fun i : Fin 3 ↦ L (Pi.single i 1)
  let F := fun (i : Fin 3) (t : Fin 3 → ℝ) ↦
    form (z + L t) (v (i + 1)) (v (i + 2))
  have hS : ContDiff ℝ ∞ (fun t ↦ z + L t) := contDiff_const.add L.contDiff
  have hF (i : Fin 3) : ContDiff ℝ ∞ (F i) :=
    ((hform.comp hS).clm_apply contDiff_const).clm_apply contDiff_const
  have hd (i : Fin 3) (t a : Fin 3 → ℝ) :
      fderiv ℝ (F i) t a =
        fderiv ℝ form (z + L t) (L a) (v (i + 1)) (v (i + 2)) := by
    have h := ((hform.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp t
      (L.hasFDerivAt.const_add z)).clm_apply (hasFDerivAt_const (v (i + 1)) t)
    have h' := h.clm_apply (hasFDerivAt_const (v (i + 2)) t)
    simp only [Function.comp_def, ContinuousLinearMap.comp_zero, zero_add] at h'
    rw [h'.fderiv]
    rfl
  have hz (t : Fin 3 → ℝ) :
      (∑ i : Fin 3, fderiv ℝ (F i) t (Pi.single i 1)) = 0 := by
    simp only [hd, Fin.sum_univ_three]
    exact hclosed (z + L t) (v 0) (v 1) (v 2)
  have hG := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin 3 → ℝ) 1 (by intro i; norm_num) F (fun i ↦ fderiv ℝ (F i))
    ∅ Set.countable_empty
    (fun i ↦ (hF i).continuous.continuousOn)
    (fun x _ i ↦ ((hF i).differentiable (by norm_num)).differentiableAt.hasFDerivAt)
    (by simp only [hz]; exact integrableOn_zero)
  simpa only [hz, integral_zero, Pi.one_apply, Pi.zero_apply, Fin.removeNth, Function.comp_def, F, v, Pi.zero_def, Pi.one_def] using hG.symm

/-- Moving the base point of a lattice parallelogram leaves its period unchanged. -/
theorem bh8_average_period_translate {n : ℕ} (Λ : Submodule ℤ (Fin n → ℂ))
    (form : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form)
    (hperiodic : ∀ (l : Λ) p, form (p + l) = form p)
    (hclosed : ∀ p u v w,
      fderiv ℝ form p u v w + fderiv ℝ form p v w u + fderiv ℝ form p w u v = 0)
    (z a : Fin n → ℂ) (l m : Λ) :
    bh8_surfacePeriod n form (z + a) l m = bh8_surfacePeriod n form z l m := by
  let L : (Fin 3 → ℝ) →L[ℝ] (Fin n → ℂ) :=
    (ContinuousLinearMap.proj 0).smulRight a +
      (ContinuousLinearMap.proj 1).smulRight (l : Fin n → ℂ) +
      (ContinuousLinearMap.proj 2).smulRight (m : Fin n → ℂ)
  have hL (t : Fin 3 → ℝ) : L t = t 0 • a + t 1 • (l : Fin n → ℂ) +
      t 2 • (m : Fin n → ℂ) := rfl
  have hv0 : L (Pi.single 0 1) = a := by simp [hL, Pi.single_apply]
  have hv1 : L (Pi.single 1 1) = (l : Fin n → ℂ) := by simp [hL, Pi.single_apply]
  have hv2 : L (Pi.single 2 1) = (m : Fin n → ℂ) := by simp [hL, Pi.single_apply]
  have h0 (c : ℝ) (t : Fin 2 → ℝ) : (0 : Fin 3).insertNth c t = ![c, t 0, t 1] := by
    ext i; fin_cases i <;> rfl
  have h1 (c : ℝ) (t : Fin 2 → ℝ) : (1 : Fin 3).insertNth c t = ![t 0, c, t 1] := by
    ext i; fin_cases i <;> rfl
  have h2 (c : ℝ) (t : Fin 2 → ℝ) : (2 : Fin 3).insertNth c t = ![t 0, t 1, c] := by
    ext i; fin_cases i <;> rfl
  have hG := bh8_average_closed_cube form hform hclosed z L
  dsimp only at hG
  simp only [Fin.sum_univ_three] at hG
  norm_num only [show (0 : Fin 3) + 1 = 1 from rfl,
    show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl,
    show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl,
    show (2 : Fin 3) + 2 = 1 from rfl] at hG
  simp only [hv0, hv1, hv2, h0, h1, h2, hL, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, one_smul, zero_smul, zero_add, add_zero] at hG
  have hl (t : Fin 2 → ℝ) :
      form (z + (t 0 • a + (l : Fin n → ℂ) + t 1 • (m : Fin n → ℂ))) =
        form (z + (t 0 • a + t 1 • (m : Fin n → ℂ))) := by
    rw [show z + (t 0 • a + (l : Fin n → ℂ) + t 1 • (m : Fin n → ℂ)) =
      (z + (t 0 • a + t 1 • (m : Fin n → ℂ))) + l by abel, hperiodic]
  have hm (t : Fin 2 → ℝ) :
      form (z + (t 0 • a + t 1 • (l : Fin n → ℂ) + (m : Fin n → ℂ))) =
        form (z + (t 0 • a + t 1 • (l : Fin n → ℂ))) := by
    rw [← add_assoc, hperiodic]
  dsimp at hG
  simp only [one_smul, zero_smul, add_zero, hl, hm, sub_self, add_zero] at hG
  apply sub_eq_zero.mp
  simpa only [bh8_surfacePeriod, add_assoc] using hG

/-- Translating a periodic function does not change its integral over the unit cube. -/
theorem bh8_average_cube_translate {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ∀ (k : Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))) t,
      f (t + k) = f t) (a : Fin d → ℝ) :
    (∫ t in Icc (0 : Fin d → ℝ) 1, f (a + t)) =
      ∫ t in Icc (0 : Fin d → ℝ) 1, f t := by
  let B := Pi.basisFun ℝ (Fin d)
  have hD := ZSpan.isAddFundamentalDomain B (volume : Measure (Fin d → ℝ))
  have hbox : parallelepiped B = Icc (0 : Fin d → ℝ) 1 := by
    ext t
    simp only [parallelepiped_basis_eq, Set.mem_setOf_eq, B, Pi.basisFun_repr,
      Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
    exact forall_and
  have hDC : ZSpan.fundamentalDomain B =ᵐ[volume] Icc (0 : Fin d → ℝ) 1 := by
    rw [← hbox]
    exact ZSpan.fundamentalDomain_ae_parallelepiped B volume
  rw [← setIntegral_congr_set hDC, ← setIntegral_congr_set hDC]
  letI : VAddInvariantMeasure (Submodule.span ℤ (Set.range B)) (Fin d → ℝ) volume :=
    inferInstanceAs (VAddInvariantMeasure (Submodule.span ℤ (Set.range B)).toAddSubgroup
      (Fin d → ℝ) volume)
  have he := hD.setIntegral_eq (hD.vadd_of_comm a) (f := f)
    (fun k t ↦ by change f ((k : Fin d → ℝ) + t) = f t; rw [add_comm]; exact hf k t)
  have hi := (measurePreserving_add_left volume a).setIntegral_image_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding f (ZSpan.fundamentalDomain B)
  exact hi.symm.trans he.symm

/-- The lattice-coordinate mean of a periodic function is invariant under translation. -/
theorem bh8_average_lattice_translate (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin (2 * n)) ℤ Λ) (f : (Fin n → ℂ) → ℝ)
    (hf : ∀ (l : Λ) p, f (p + l) = f p) (a : Fin n → ℂ) :
    (∫ t in Icc (0 : Fin (2 * n) → ℝ) 1,
      f (a + ∑ j, t j • (b j : Fin n → ℂ))) =
    ∫ t in Icc (0 : Fin (2 * n) → ℝ) 1, f (∑ j, t j • (b j : Fin n → ℂ)) := by
  classical
  let B := b.ofZLatticeBasis ℝ
  let x := B.equivFun a
  have hx : (∑ j, x j • (b j : Fin n → ℂ)) = a := by
    simpa only [x, Module.Basis.equivFun_apply, B, Module.Basis.ofZLatticeBasis_apply]
      using B.sum_repr a
  have hp (k : Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin (2 * n)))))
      (t : Fin (2 * n) → ℝ) :
      f (∑ j, (t + k) j • (b j : Fin n → ℂ)) = f (∑ j, t j • (b j : Fin n → ℂ)) := by
    have hk : ∀ j, ∃ c : ℤ, (c : ℝ) = (k : Fin (2 * n) → ℝ) j :=
      ((Pi.basisFun ℝ (Fin (2 * n))).mem_span_iff_repr_mem ℤ k).mp k.property
    choose c hc using hk
    have he : (∑ j, (k : Fin (2 * n) → ℝ) j • (b j : Fin n → ℂ)) =
        ((∑ j, c j • b j : Λ) : Fin n → ℂ) := by
      simp only [← hc, Int.cast_smul_eq_zsmul, Submodule.coe_sum, Submodule.coe_smul]
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, he]
    exact hf (∑ j, c j • b j) _
  have h := bh8_average_cube_translate (fun t ↦ f (∑ j, t j • (b j : Fin n → ℂ))) hp x
  simpa only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hx] using h

/-- The constant lattice average evaluates to the original lattice periods. -/
theorem bh8_average_periods (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin (2 * n)) ℤ Λ)
    (form : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) (hperiodic : ∀ (l : Λ) p, form (p + l) = form p)
    (hclosed : ∀ p u v w,
      fderiv ℝ form p u v w + fderiv ℝ form p v w u + fderiv ℝ form p w u v = 0)
    (l m : Λ) : bh8_average n Λ b form l m = bh8_surfacePeriod n form 0 l m := by
  let C := fun t : Fin (2 * n) → ℝ ↦ ∑ j, t j • (b j : Fin n → ℂ)
  let P := fun s : Fin 2 → ℝ ↦ s 0 • (l : Fin n → ℂ) + s 1 • (m : Fin n → ℂ)
  let f := fun s t ↦ form (P s + C t) l m
  have hC : Continuous C := continuous_finsetSum _ fun j _ ↦
    (continuous_apply j).smul continuous_const
  have hP : Continuous P :=
    ((continuous_apply 0).smul continuous_const).add
      ((continuous_apply 1).smul continuous_const)
  have hfc : Continuous (Function.uncurry f) :=
    ((hform.continuous.comp ((hP.comp continuous_fst).add
      (hC.comp continuous_snd))).clm_apply continuous_const).clm_apply continuous_const
  have hi : Integrable (Function.uncurry f)
      ((volume.restrict (Icc (0 : Fin 2 → ℝ) 1)).prod
        (volume.restrict (Icc (0 : Fin (2 * n) → ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hfc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hav (s : Fin 2 → ℝ) :
      (∫ t in Icc (0 : Fin (2 * n) → ℝ) 1, f s t) = bh8_average n Λ b form l m := by
    have h := bh8_average_lattice_translate n Λ b (fun p ↦ form p l m)
      (fun k p ↦ congrArg (fun B ↦ B l m) (hperiodic k p)) (P s)
    have hiB := bh8_average_integrable n Λ b form hform
    have hil : IntegrableOn (fun t : Fin (2 * n) → ℝ ↦
        form (∑ j, t j • (b j : Fin n → ℂ)) l) (Icc 0 1) := by
      exact (ContinuousLinearMap.apply ℝ _ (l : Fin n → ℂ)).integrable_comp hiB
    rw [bh8_average, ContinuousLinearMap.integral_apply hiB l,
      ContinuousLinearMap.integral_apply hil m]
    exact h
  have hper (t : Fin (2 * n) → ℝ) :
      (∫ s in Icc (0 : Fin 2 → ℝ) 1, f s t) = bh8_surfacePeriod n form 0 l m := by
    have h := bh8_average_period_translate Λ form hform hperiodic hclosed 0 (C t) l m
    rw [zero_add] at h
    refine Eq.trans ?_ h
    apply setIntegral_congr_fun measurableSet_Icc
    intro s _
    dsimp [f, P]
    rw [add_comm (_ + _) (C t), add_assoc]
  have hunit (d : ℕ) (r : ℝ) : (∫ _ in Icc (0 : Fin d → ℝ) 1, r) = r := by
    simp only [setIntegral_const, measureReal_def, Real.volume_Icc_pi,
      Pi.one_apply, Pi.zero_apply, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one,
      ENNReal.toReal_one, one_smul]
  have hswap := integral_integral_swap hi
  simp only [hav, hper, hunit] at hswap
  exact hswap

/-- Translation averaging preserves periods, type and strict positivity of a closed form.
Source: Birkenhake--Lange, section 4.3, invariant positive integral forms on a complex torus;
Stokes' theorem applied to translated period parallelograms. -/
theorem bh8_averaging_aux (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin (2 * n)) ℤ Λ)
    (form : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) (hperiodic : ∀ (l : Λ) p, form (p + l) = form p)
    (halt : ∀ p v, form p v v = 0)
    (h11 : ∀ p, IsTypeOneOne (fun v w ↦ form p v w))
    (hpos : ∀ p v, v ≠ 0 → 0 < form p v (Complex.I • v))
    (hclosed : ∀ p u v w,
      fderiv ℝ form p u v w + fderiv ℝ form p v w u + fderiv ℝ form p w u v = 0) :
    (∀ l m : Λ, bh8_average n Λ b form l m = bh8_surfacePeriod n form 0 l m) ∧
    (∀ v, bh8_average n Λ b form v v = 0) ∧
    IsTypeOneOne (fun v w ↦ bh8_average n Λ b form v w) ∧
    (∀ v, v ≠ 0 → 0 < bh8_average n Λ b form v (Complex.I • v)) := by
  exact ⟨bh8_average_periods n Λ b form hform hperiodic hclosed,
    bh8_average_alternating n Λ b form hform halt,
    bh8_average_type_one_one n Λ b form hform h11,
    bh8_average_positive n Λ b form hform hpos⟩

/-- Exact stage-five projective Riemann-form endpoint, through curvature, Chern periods and averaging.
Source: Birkenhake--Lange, second edition, section 4.3, Riemann's projectivity criterion. -/
theorem bh8_projective_riemann_form_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    ∃ (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
      (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
      (∀ l, E l l = 0) ∧ (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
      IsTypeOneOne (fun v w ↦ B v w) ∧ (∀ v, v ≠ 0 → 0 < B v (Complex.I • v)) := by
  obtain ⟨A⟩ := bh8_projective_atlas_aux X
  obtain ⟨hform, hper, halt, h11, hp, hc⟩ :=
    bh8_curvature_geometry_aux (dim X.left) (abelianPeriodLattice X) A
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  letI : DiscreteTopology (abelianPeriodLattice X) :=
    discrete_complexExponentialLattice X (dim X.left)
  letI : IsZLattice ℝ (abelianPeriodLattice X) :=
    isZLattice_complexExponentialLattice X (dim X.left)
  obtain ⟨hperiod, ha, ht, hpos⟩ := bh8_averaging_aux (dim X.left)
    (abelianPeriodLattice X) (abelianLatticeBasis X) (bh8_curvature _ _ A)
    hform hper halt h11 hp hc
  let B := bh8_bilinear (dim X.left)
    (bh8_average (dim X.left) (abelianPeriodLattice X) (abelianLatticeBasis X)
      (bh8_curvature _ _ A))
  have hi (l m : abelianPeriodLattice X) : ∃ k : ℤ, B l m = k := by
    obtain ⟨k, hk⟩ := bh8_chern_periods_aux (dim X.left) (abelianPeriodLattice X) A 0 l m
    exact ⟨k, (hperiod l m).trans hk⟩
  let E := bh8_integralRestriction (dim X.left) (abelianPeriodLattice X) B hi
  have he (l m : abelianPeriodLattice X) : B l m = (E l m : ℝ) := by
    obtain ⟨k, hk⟩ := hi l m
    change B l m = (⌊B l m⌋ : ℝ)
    rw [hk, Int.floor_intCast]
  refine ⟨E, B, ?_, he, ht, hpos⟩
  intro l
  have h : (E l l : ℝ) = 0 := (he l l).symm.trans (ha l)
  exact_mod_cast h

/-- Positive Appell--Humbert data on the projective abelian variety.
Source: `spec_exists_datumOfX_of_riemann`; Birkenhake--Lange, Lemma 1.3.1 and Theorem 2.2.3. -/
theorem bh8_polarization_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : ∃ A₀ : bh4_AHData X, A₀.H.IsPositiveDefinite := by
  obtain ⟨E, B, hE, hB, h11, hp⟩ := bh8_projective_riemann_form_aux X
  obtain ⟨H, hi, hHB, chi, hc, _⟩ := spec_exists_datumOfX_of_riemann X E hE B hB h11
  refine ⟨⟨H, E, hi, chi, hc⟩, ?_⟩
  intro v hv
  have he : (H.toFun v v).re = B v (Complex.I • v) := by
    rw [spec_hermitian_toFun_eq_imaginary H v v]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, hHB]
  exact he.symm ▸ hp v hv

end HodgeLean.Adapters

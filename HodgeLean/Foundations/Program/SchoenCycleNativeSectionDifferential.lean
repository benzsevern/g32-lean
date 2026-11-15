import HodgeLean.Foundations.Program.SchoenCycleRegularChartAnalytic

/-! # Differentials of regular sections in the native scheme chart -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A regular section is analytic in the centered native chart in every smooth dimension.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
HodgeConjecture, ComplexPoint.analyticAt_localChart_symm_evaluate. -/
theorem s2e_native_section_analytic
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (s : Γ(X.left, U)) :
    AnalyticAt ℂ (fun z : Fin d → ℂ => Point.evaluate U s
      ((ComplexPoint.localChart X d p).symm
        (ComplexPoint.localChart X d p p + z))) 0 := by
  let e := ComplexPoint.localChart X d p
  have he : p ∈ e.source := ComplexPoint.mem_localChart_source X d p
  have hV : e.symm (e p) ∈ Point.overOpen U := by
    rw [e.left_inv he]
    exact hp
  have ha := ComplexPoint.analyticAt_localChart_symm_evaluate X d p
    (e.map_source he) U s hV
  have hb : AnalyticAt ℂ (fun z : Fin d → ℂ => e p + z) 0 :=
    analyticAt_const.add analyticAt_id
  have ha' : AnalyticAt ℂ (fun v => Point.evaluate U s (e.symm v))
      ((fun z : Fin d → ℂ => e p + z) 0) := by
    simpa only [add_zero] using ha
  exact ha'.comp hb

/-- The native differential of regular sections obeys the algebraic Leibniz rule at the point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_native_section_differential_mul
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (s t : Γ(X.left, U)) :
    let v := fun z : Fin d → ℂ => (ComplexPoint.localChart X d p).symm
      (ComplexPoint.localChart X d p p + z)
    fderiv ℂ (fun z => Point.evaluate U (s * t) (v z)) 0 =
      Point.evaluate U s p • fderiv ℂ (fun z => Point.evaluate U t (v z)) 0 +
      Point.evaluate U t p • fderiv ℂ (fun z => Point.evaluate U s (v z)) 0 := by
  dsimp only
  let e := ComplexPoint.localChart X d p
  let v := fun z : Fin d → ℂ => e.symm (e p + z)
  have he : p ∈ e.source := ComplexPoint.mem_localChart_source X d p
  have hmul : (fun z => Point.evaluate U (s * t) (v z)) =
      (fun z => Point.evaluate U s (v z) * Point.evaluate U t (v z)) := by
    funext z
    by_cases hz : (v z).underlying ∈ U
    · simp [Point.evaluate, hz]
    · simp [Point.evaluate, hz]
  change fderiv ℂ (fun z => Point.evaluate U (s * t) (v z)) 0 = _
  rw [hmul, fderiv_fun_mul
    (s2e_native_section_analytic X d p U hp s).differentiableAt
    (s2e_native_section_analytic X d p U hp t).differentiableAt]
  simp only [add_zero, (ComplexPoint.localChart X d p).left_inv
    (ComplexPoint.mem_localChart_source X d p)]

/-- The actual regular coordinate sections give the coordinate differential basis in the native chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_native_coordinate_section_differential
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (i : Fin d) :
    fderiv ℂ (fun z : Fin d → ℂ => Point.evaluate
      (ComplexPoint.localEtaleCoordinates X d p).ambientCoordinateOpen
      ((ComplexPoint.localEtaleCoordinates X d p).ambientCoordinateSection i)
      ((ComplexPoint.localChart X d p).symm
        (ComplexPoint.localChart X d p p + z))) 0 =
      (ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ) := by
  let e := ComplexPoint.localChart X d p
  have he : p ∈ e.source := ComplexPoint.mem_localChart_source X d p
  have ht : Tendsto (fun z : Fin d → ℂ => e p + z) (𝓝 0) (𝓝 (e p)) := by
    have hc : Continuous (fun z : Fin d → ℂ => e p + z) :=
      continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : Fin d → ℂ)
  have htarget : ∀ᶠ z : Fin d → ℂ in 𝓝 0, e p + z ∈ e.target :=
    ht (e.open_target.mem_nhds (e.map_source he))
  have heq : (fun z : Fin d → ℂ => Point.evaluate
      (ComplexPoint.localEtaleCoordinates X d p).ambientCoordinateOpen
      ((ComplexPoint.localEtaleCoordinates X d p).ambientCoordinateSection i)
      (e.symm (e p + z))) =ᶠ[𝓝 0] (fun z => e p i + z i) := by
    filter_upwards [htarget] with z hz
    rw [← ComplexPoint.localChart_apply_component_eq_evaluate X d p
      (e.symm (e p + z)) (e.map_target hz) i]
    change e (e.symm (e p + z)) i = _
    rw [e.right_inv hz]
    rfl
  rw [heq.fderiv_eq]
  exact ((ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ).hasFDerivAt.const_add
    (e p i)).fderiv

/-- The native differential is additive on actual regular sections.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_native_section_differential_add
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (s t : Γ(X.left, U)) :
    let v := fun z : Fin d → ℂ => (ComplexPoint.localChart X d p).symm
      (ComplexPoint.localChart X d p p + z)
    fderiv ℂ (fun z => Point.evaluate U (s + t) (v z)) 0 =
      fderiv ℂ (fun z => Point.evaluate U s (v z)) 0 +
      fderiv ℂ (fun z => Point.evaluate U t (v z)) 0 := by
  dsimp only
  let v := fun z : Fin d → ℂ => (ComplexPoint.localChart X d p).symm
    (ComplexPoint.localChart X d p p + z)
  have hadd : (fun z => Point.evaluate U (s + t) (v z)) =
      (fun z => Point.evaluate U s (v z) + Point.evaluate U t (v z)) := by
    funext z
    by_cases hz : (v z).underlying ∈ U
    · simp [Point.evaluate, hz]
    · simp [Point.evaluate, hz]
  change fderiv ℂ (fun z => Point.evaluate U (s + t) (v z)) 0 = _
  rw [hadd, fderiv_fun_add
    (s2e_native_section_analytic X d p U hp s).differentiableAt
    (s2e_native_section_analytic X d p U hp t).differentiableAt]

/-- The chosen etale polynomial coordinate and its ambient regular section have identical point evaluations.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_native_coordinate_section_evaluation
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p q : ComplexPoint X) (i : Fin d) :
    let D := ComplexPoint.localEtaleCoordinates X d p
    Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X i)) q =
      Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection i) q := by
  let D := ComplexPoint.localEtaleCoordinates X d p
  have he := ComplexPoint.evaluate_eq (Y := X) D.neighborhood.ι_image_top.symm
    (D.coordinateAlgHom (MvPolynomial.X i)) q
  change Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X i)) q =
    Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection i) q
  dsimp only [LocalEtaleCoordinates.ambientCoordinateSection]
  rw [Scheme.Opens.ι_appIso]
  change Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X i)) q =
    Point.evaluate D.ambientCoordinateOpen
      (D.neighborhood.topIso.inv (D.coordinateAlgHom (MvPolynomial.X i))) q
  exact he

/-- The original etale polynomial coordinate sections differentiate to the native coordinate projections.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_native_etale_coordinate_differential
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (i : Fin d) :
    let D := ComplexPoint.localEtaleCoordinates X d p
    fderiv ℂ (fun z : Fin d → ℂ =>
      Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X i))
        ((ComplexPoint.localChart X d p).symm
          (ComplexPoint.localChart X d p p + z))) 0 =
      (ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ) := by
  have heq : (fun z : Fin d → ℂ => Point.evaluate
      (ComplexPoint.localEtaleCoordinates X d p).neighborhood
      ((ComplexPoint.localEtaleCoordinates X d p).coordinateAlgHom (MvPolynomial.X i))
      ((ComplexPoint.localChart X d p).symm
        (ComplexPoint.localChart X d p p + z))) =
      (fun z : Fin d → ℂ => Point.evaluate
        (ComplexPoint.localEtaleCoordinates X d p).ambientCoordinateOpen
        ((ComplexPoint.localEtaleCoordinates X d p).ambientCoordinateSection i)
        ((ComplexPoint.localChart X d p).symm
          (ComplexPoint.localChart X d p p + z))) := by
    funext z
    exact s2e_native_coordinate_section_evaluation X d p _ i
  dsimp only
  rw [heq]
  exact s2e_native_coordinate_section_differential X d p i

/-- Restriction to a smaller neighbourhood preserves the native differential of an actual section germ.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_native_section_differential_restrict
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U W : X.left.Opens) (hWU : W ≤ U)
    (hpW : p.underlying ∈ W) (s : Γ(X.left, U)) :
    fderiv ℂ (fun z : Fin d → ℂ =>
      Point.evaluate W (X.left.presheaf.map (homOfLE hWU).op s)
        ((ComplexPoint.localChart X d p).symm
          (ComplexPoint.localChart X d p p + z))) 0 =
      fderiv ℂ (fun z : Fin d → ℂ => Point.evaluate U s
        ((ComplexPoint.localChart X d p).symm
          (ComplexPoint.localChart X d p p + z))) 0 := by
  let C := ComplexPoint.localChart X d p
  have hC : p ∈ C.source := ComplexPoint.mem_localChart_source X d p
  have hct : AnalyticAt ℂ (fun z : Fin d → ℂ => C p + z) 0 :=
    analyticAt_const.add analyticAt_id
  have hcx : ContinuousAt (fun z : Fin d → ℂ => C.symm (C p + z)) 0 := by
    have hc : ContinuousAt C.symm ((fun z : Fin d → ℂ => C p + z) 0) := by
      simpa only [add_zero] using C.continuousAt_symm (C.map_source hC)
    exact hc.comp hct.continuousAt
  have hsource : C.symm (C p + (0 : Fin d → ℂ)) ∈ Point.overOpen W := by
    rw [add_zero, C.left_inv hC]
    exact hpW
  have hmem : ∀ᶠ z : Fin d → ℂ in 𝓝 0,
      C.symm (C p + z) ∈ Point.overOpen W :=
    hcx ((Point.isOpen_overOpen W).mem_nhds hsource)
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hmem] with z hz
  exact (Point.evaluate_res hWU s (C.symm (C p + z)) hz).symm

end HodgeLean.Foundations.Program

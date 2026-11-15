import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticGerms
import HodgeLean.Foundations.Program.SchoenCycleRegularChartAnalytic

/-! # Native analytic germs of actual regular sections -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- A regular section is analytic in the actual centered local chart in every
smooth relative dimension.
Source: HodgeConjecture,
AlgebraicGeometry.ComplexPoint.analyticAt_localChart_symm_evaluate. -/
theorem s2e_regular_section_centered_chart_analytic
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (s : Γ(X.left, U)) :
    AnalyticAt ℂ (fun z : Fin d → ℂ => Point.evaluate U s
      ((ComplexPoint.localChart X d p).symm (ComplexPoint.localChart X d p p + z))) 0 := by
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

#print axioms s2e_regular_section_centered_chart_analytic
/-- The inverse of the actual centered chart tends to its specified complex
point as its coordinate tends to zero.
Source: Mathlib, OpenPartialHomeomorph.continuousAt_symm and left_inv. -/
theorem s2e_centered_localChart_tendsto
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) :
    Tendsto (fun z : Fin d → ℂ => (ComplexPoint.localChart X d p).symm
      (ComplexPoint.localChart X d p p + z)) (nhds 0) (nhds p) := by
  let e := ComplexPoint.localChart X d p
  have he : p ∈ e.source := ComplexPoint.mem_localChart_source X d p
  have h1 : ContinuousAt e.symm (e p + 0) := by
    simpa only [add_zero] using e.continuousAt_symm (e.map_source he)
  have h2 : ContinuousAt (fun z : Fin d → ℂ => e p + z) 0 :=
    continuous_const.continuousAt.add continuous_id.continuousAt
  have h3 := h1.comp h2
  simpa only [Function.comp_apply, add_zero, e.left_inv he, e, Function.comp_def] using h3.tendsto

#print axioms s2e_centered_localChart_tendsto
/-- Evaluation in the actual centered chart sends regular sections to native
analytic germs as a unital ring homomorphism.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6;
Hartshorne, Algebraic Geometry, II.2. -/
def s2e_regularSection_nativeAnalyticGerm
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U) :
    Γ(X.left, U) →+* s2e_nativeAnalyticGermRing d := by
  let q := fun z : Fin d → ℂ => (ComplexPoint.localChart X d p).symm
    (ComplexPoint.localChart X d p p + z)
  have hU : ∀ᶠ z in nhds 0, (q z).underlying ∈ U :=
    s2e_centered_localChart_tendsto X d p ((Point.isOpen_overOpen U).mem_nhds hp)
  refine
    { toFun := fun s => ⟨Filter.Germ.ofFun (fun z => Point.evaluate U s (q z)),
        ⟨_, s2e_regular_section_centered_chart_analytic X d p U hp s, rfl⟩⟩
      map_zero' := ?_
      map_one' := ?_
      map_add' := ?_
      map_mul' := ?_ }
  · apply Subtype.ext
    change Filter.Germ.ofFun (fun z => Point.evaluate U 1 (q z)) = Filter.Germ.ofFun (fun _ => (1 : ℂ))
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    simp only [Point.evaluate, dif_pos hz, map_one]
  · intro s t
    apply Subtype.ext
    change Filter.Germ.ofFun (fun z => Point.evaluate U (s * t) (q z)) =
      Filter.Germ.ofFun (fun z => Point.evaluate U s (q z) * Point.evaluate U t (q z))
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    simp only [Point.evaluate, dif_pos hz, map_mul]
  · apply Subtype.ext
    change Filter.Germ.ofFun (fun z => Point.evaluate U 0 (q z)) = Filter.Germ.ofFun (fun _ => (0 : ℂ))
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    simp only [Point.evaluate, dif_pos hz, map_zero]
  · intro s t
    apply Subtype.ext
    change Filter.Germ.ofFun (fun z => Point.evaluate U (s + t) (q z)) =
      Filter.Germ.ofFun (fun z => Point.evaluate U s (q z) + Point.evaluate U t (q z))
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    simp only [Point.evaluate, dif_pos hz, map_add]

#print axioms s2e_regularSection_nativeAnalyticGerm
/-- The native analytic germ map of regular sections commutes with
restriction to any smaller neighborhood of the specified point.
Source: Hartshorne, Algebraic Geometry, II.2;
HodgeConjecture, AlgebraicGeometry.Point.evaluate_res. -/
theorem s2e_regularSection_nativeAnalyticGerm_restrict
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U V : X.left.Opens) (hVU : V ≤ U)
    (hp : p.underlying ∈ V) (s : Γ(X.left, U)) :
    s2e_regularSection_nativeAnalyticGerm X d p U (hVU hp) s =
      s2e_regularSection_nativeAnalyticGerm X d p V hp
        (X.left.presheaf.map (homOfLE hVU).op s) := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have hV := s2e_centered_localChart_tendsto X d p
    ((Point.isOpen_overOpen V).mem_nhds hp)
  filter_upwards [hV] with z hz
  exact Point.evaluate_res hVU s _ hz

#print axioms s2e_regularSection_nativeAnalyticGerm_restrict
/-- The value of a regular section's native analytic germ at the origin is
its algebraic evaluation at the specified complex point.
Source: HodgeConjecture, AlgebraicGeometry.Point.evaluate;
Mathlib, OpenPartialHomeomorph.left_inv. -/
theorem s2e_regularSection_nativeAnalyticGerm_value
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (s : Γ(X.left, U)) :
    s2e_nativeAnalyticGerm_value d (s2e_regularSection_nativeAnalyticGerm X d p U hp s) =
      Point.evaluate U s p := by
  change Point.evaluate U s ((ComplexPoint.localChart X d p).symm
    (ComplexPoint.localChart X d p p + 0)) = _
  rw [add_zero, (ComplexPoint.localChart X d p).left_inv
    (ComplexPoint.mem_localChart_source X d p)]

#print axioms s2e_regularSection_nativeAnalyticGerm_value
/-- The actual centered-chart unit relation identifies the principal ideals
of the two regular sections inside the native analytic germ ring.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6. -/
theorem s2e_nativeAnalyticGerm_unit_principal_ideals
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (s t : Γ(X.left, U)) (η : (Fin d → ℂ) → ℂ)
    (hη : AnalyticAt ℂ η 0) (hη0 : η 0 ≠ 0)
    (he : (fun z => Point.evaluate U s ((ComplexPoint.localChart X d p).symm
        (ComplexPoint.localChart X d p p + z))) =ᶠ[nhds 0]
      (fun z => η z * Point.evaluate U t ((ComplexPoint.localChart X d p).symm
        (ComplexPoint.localChart X d p p + z)))) :
    Ideal.span {s2e_regularSection_nativeAnalyticGerm X d p U hp s} =
      Ideal.span {s2e_regularSection_nativeAnalyticGerm X d p U hp t} := by
  let u : s2e_nativeAnalyticGermRing d := ⟨Filter.Germ.ofFun η, ⟨η, hη, rfl⟩⟩
  have hu : IsUnit u := s2e_nativeAnalyticGerm_isUnit_of_nonzero d η hη hη0
  have h : s2e_regularSection_nativeAnalyticGerm X d p U hp s =
      u * s2e_regularSection_nativeAnalyticGerm X d p U hp t := by
    apply Subtype.ext
    exact Filter.Germ.coe_eq.mpr he
  rw [h]
  exact Ideal.span_singleton_mul_left_unit hu _

#print axioms s2e_nativeAnalyticGerm_unit_principal_ideals
end HodgeLean.Foundations.Program

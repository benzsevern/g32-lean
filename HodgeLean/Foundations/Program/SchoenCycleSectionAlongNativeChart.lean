import HodgeLean.Foundations.Program.SchoenCycleNativeStalkGerms

/-! # Actual regular sections along an analytic native chart map -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

/-- Actual regular sections are analytic along any map analytic in the specified native chart and tending to its centre.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
theorem s2e_regular_section_analytic_along_native_chart
    (X : Over (Spec ↧ℂ)) (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (q : (Fin k → ℂ) → ComplexPoint X)
    (hq : Tendsto q (𝓝 0) (𝓝 p)) (hq0 : q 0 = p)
    (hqa : AnalyticAt ℂ (fun z => ComplexPoint.localChart X d p (q z)) 0)
    (U : X.left.Opens) (hp : p.underlying ∈ U) (s : Γ(X.left, U)) :
    AnalyticAt ℂ (fun z => Point.evaluate U s (q z)) 0 := by
  let C := ComplexPoint.localChart X d p
  have hpC : p ∈ C.source := ComplexPoint.mem_localChart_source X d p
  have hF : AnalyticAt ℂ (fun w => Point.evaluate U s (C.symm w)) (C p) := by
    apply ComplexPoint.analyticAt_localChart_symm_evaluate X d p (C.map_source hpC) U s
    change C.symm (C p) ∈ Point.overOpen U
    rw [C.left_inv hpC]
    exact hp
  have ha := hF.comp_of_eq hqa (show C (q 0) = C p by rw [hq0])
  apply ha.congr
  filter_upwards [hq (C.open_source.mem_nhds hpC)] with z hz
  dsimp only [Function.comp_def]
  rw [C.left_inv hz]

/-- Pullback of the native analytic germ agrees with actual regular evaluation along the specified chart map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
theorem s2e_nativeSectionGermHom_pullback_along_chart
    (X : Over (Spec ↧ℂ)) (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (q : (Fin k → ℂ) → ComplexPoint X)
    (hq : Tendsto q (𝓝 0) (𝓝 p)) (hq0 : q 0 = p)
    (hqa : AnalyticAt ℂ (fun z => ComplexPoint.localChart X d p (q z)) 0)
    (U : X.left.Opens) (hp : p.underlying ∈ U) (s : Γ(X.left, U)) :
    s2e_analyticGermPullback
      (fun z => ComplexPoint.localChart X d p (q z) - ComplexPoint.localChart X d p p)
      (hqa.sub analyticAt_const) (by rw [hq0]; exact sub_self _)
      (s2e_nativeSectionGermHom X d p U hp s) =
        (⟨Filter.Germ.ofFun (fun z => Point.evaluate U s (q z)),
          (fun z => Point.evaluate U s (q z)),
          s2e_regular_section_analytic_along_native_chart X d k p q hq hq0 hqa U hp s,
          rfl⟩ : AnalyticGermAt k 0) := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  let C := ComplexPoint.localChart X d p
  have hpC : p ∈ C.source := ComplexPoint.mem_localChart_source X d p
  filter_upwards [hq (C.open_source.mem_nhds hpC)] with z hz
  change Point.evaluate U s (C.symm (C p + (C (q z) - C p))) = Point.evaluate U s (q z)
  have hv : C p + (C (q z) - C p) = C (q z) := by abel
  rw [hv, C.left_inv hz]

/-- Realize the actual algebraic stalk along a map analytic in the native chart and tending to its centre.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
def s2e_stalkGermAlongNativeChart
    (X : Over (Spec ↧ℂ)) (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (q : (Fin k → ℂ) → ComplexPoint X)
    (_hq : Tendsto q (𝓝 0) (𝓝 p)) (hq0 : q 0 = p)
    (hqa : AnalyticAt ℂ (fun z => ComplexPoint.localChart X d p (q z)) 0)
    (U : X.left.affineOpens) (hp : p.underlying ∈ U.1) :
    X.left.presheaf.stalk p.underlying →+* AnalyticGermAt k 0 :=
  (s2e_analyticGermPullback
    (fun z => ComplexPoint.localChart X d p (q z) - ComplexPoint.localChart X d p p)
    (hqa.sub analyticAt_const) (by rw [hq0]; exact sub_self _)).comp
      (s2e_nativeStalkGermHom X d p U hp)

/-- Realization along a native chart map evaluates every regular representative on its actual open domain.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
theorem s2e_stalkGermAlongNativeChart_germ
    (X : Over (Spec ↧ℂ)) (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (q : (Fin k → ℂ) → ComplexPoint X)
    (hq : Tendsto q (𝓝 0) (𝓝 p)) (hq0 : q 0 = p)
    (hqa : AnalyticAt ℂ (fun z => ComplexPoint.localChart X d p (q z)) 0)
    (U : X.left.affineOpens) (hp : p.underlying ∈ U.1)
    (V : X.left.Opens) (hpV : p.underlying ∈ V) (s : Γ(X.left, V)) :
    s2e_stalkGermAlongNativeChart X d k p q hq hq0 hqa U hp
      (X.left.presheaf.germ V p.underlying hpV s) =
        (⟨Filter.Germ.ofFun (fun z => Point.evaluate V s (q z)),
          (fun z => Point.evaluate V s (q z)),
          s2e_regular_section_analytic_along_native_chart X d k p q hq hq0 hqa V hpV s,
          rfl⟩ : AnalyticGermAt k 0) := by
  unfold s2e_stalkGermAlongNativeChart
  rw [RingHom.comp_apply, s2e_nativeStalkGermHom_germ_on_open]
  exact s2e_nativeSectionGermHom_pullback_along_chart X d k p q hq hq0 hqa V hpV s

/-- Realization of an actual pulled-back regular germ agrees with evaluation after the morphism.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
theorem s2e_stalkGermAlongNativeChart_pullback_germ
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (q : (Fin k → ℂ) → ComplexPoint X)
    (hq : Tendsto q (𝓝 0) (𝓝 p)) (hq0 : q 0 = p)
    (hqa : AnalyticAt ℂ (fun z => ComplexPoint.localChart X d p (q z)) 0)
    (U : X.left.affineOpens) (hp : p.underlying ∈ U.1)
    (V : Y.left.Opens) (hpV : (Point.map f p).underlying ∈ V) (s : Γ(Y.left, V)) :
    (s2e_stalkGermAlongNativeChart X d k p q hq hq0 hqa U hp
      (f.left.stalkMap p.underlying
        (Y.left.presheaf.germ V (Point.map f p).underlying hpV s))).val =
      Filter.Germ.ofFun (fun z => Point.evaluate V s (Point.map f (q z))) := by
  change (s2e_stalkGermAlongNativeChart X d k p q hq hq0 hqa U hp
    (f.left.stalkMap p.underlying (Y.left.presheaf.germ V
      (f.left p.underlying) hpV s))).val = _
  rw [f.left.germ_stalkMap_apply,
    s2e_stalkGermAlongNativeChart_germ]
  apply Filter.Germ.coe_eq.mpr
  exact Eventually.of_forall (fun z => (Point.evaluate_map f V s (q z)).symm)

end HodgeLean.Foundations.Program

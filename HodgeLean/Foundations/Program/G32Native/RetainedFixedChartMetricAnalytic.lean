import HodgeLean.Foundations.Program.G32Native.RetainedFrameQuotientKernel
import HodgeLean.Foundations.Program.G32Native.MetricNormalFamilyRegularity
import HodgeLean.Foundations.TubularEuler.ChartMetricOperatorHelpers
import HodgeLean.Foundations.TubularEuler.RegularEquationHilbertHelpers
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Metric representatives in a fixed ambient chart -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- The original metric representatives have analytic coefficients in a
fixed ambient chart and the specified algebraic conormal frame. -/
theorem retained_fixed_chart_metric_analytic
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (m d k : ℕ) [SmoothOfRelativeDimension m Y.hom]
    [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (U : Y.left.Opens) (hU : U ≤ j.left ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (g : ChartHermitianMetric (ComplexPoint X) d)
    (σ : (Fin m → ℂ) → ComplexPoint Y) (b : Fin m → ℂ) (z : ComplexPoint X)
    (hσ : ContMDiffAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω σ b)
    (hdom : ∀ c, σ c ∈ Point.overOpen U ∧
      Point.map j (σ c) ∈ (chartAt (Fin d → ℂ) z).source)
    (L : ∀ c, i1_normalFibre j.left (σ c) →ₗ[ℂ] (Fin d → ℂ))
    (heval : ∀ c u a, retainedAffineConormalDifferential X Y j d A hA
      (σ c) (hU (hdom c).1) z (hdom c).2 a (L c u) = u a)
    (horth : ∀ c u v, (∀ a, retainedAffineConormalDifferential X Y j d A hA
      (σ c) (hU (hdom c).1) z (hdom c).2 a v = 0) →
      g.coefficient z ((chartAt (Fin d → ℂ) z) (Point.map j (σ c))) (L c u) v = 0)
    (H : EuclideanSpace ℂ (Fin d) ≃L[ℂ] (Fin d → ℂ))
    (R : EuclideanSpace ℂ (Fin k) ≃L[ℂ] (Fin k → ℂ))
    (w : Fin k → ℂ) :
    AnalyticAt ℝ (fun p : (Fin m → ℂ) × (Fin k → ℂ) =>
      L p.1 ((i1_conormalFrameBasis j.left k U E (σ p.1) (hdom p.1).1).dualBasis.equivFun.symm p.2))
      (b, w) := by
  let HR := complexContinuousLinearEquivReal H
  let Q := fun c => retainedFrameQuotientOperator X Y j d k A hA U hU E z (σ c)
  let T := fun c => (R.symm.toContinuousLinearMap.comp
    ((Q c).comp H.toContinuousLinearMap)).restrictScalars ℝ
  let a := fun c => H.symm ((chartAt (Fin d → ℂ) z) (Point.map j (σ c)))
  let P := fun c => chartMetricOperator g HR z (a c)
  let v := fun p : (Fin m → ℂ) × EuclideanSpace ℂ (Fin k) =>
    H.symm (L p.1 ((i1_conormalFrameBasis j.left k U E (σ p.1) (hdom p.1).1).dualBasis.equivFun.symm (R p.2)))
  have hQ : AnalyticAt ℂ Q b := retained_frame_quotient_analytic
    X Y j m d k A hA U hU E σ b z hσ (hdom b).1 (hdom b).2
  have hTc : AnalyticAt ℂ (fun c => R.symm.toContinuousLinearMap.comp
      ((Q c).comp H.toContinuousLinearMap)) b :=
    ((contDiffAt_const.clm_comp (hQ.contDiffAt.clm_comp contDiffAt_const))).analyticAt
  let S : ((EuclideanSpace ℂ (Fin d)) →L[ℂ] (EuclideanSpace ℂ (Fin k))) →L[ℝ]
      ((EuclideanSpace ℂ (Fin d)) →L[ℝ] (EuclideanSpace ℂ (Fin k))) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ _ _ ℝ ℝ).toContinuousLinearMap
  have hTr : AnalyticAt ℝ (fun c => R.symm.toContinuousLinearMap.comp
      ((Q c).comp H.toContinuousLinearMap)) b := hTc.restrictScalars
  have hT : AnalyticAt ℝ T b := (S.analyticAt _).comp hTr
  have hJ : ContMDiff 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (Point.map j) :=
    (HodgeLean.Foundations.Analytic.f4_isHom_iff_contMDiff (d := m) (e := d) _).mp
      (HodgeLean.Foundations.Analytic.f4_map_isHom j)
  have hcoord : AnalyticAt ℂ
      (fun c => (chartAt (Fin d → ℂ) z) (Point.map j (σ c))) b := (((contMDiffOn_chart (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) (x := z)).contMDiffAt
    ((chartAt (Fin d → ℂ) z).open_source.mem_nhds (hdom b).2)).comp b
      (hJ.contMDiffAt.comp b hσ)).contDiffAt.analyticAt
  have ha : AnalyticAt ℝ a b :=
    ((H.symm.toContinuousLinearMap.analyticAt _).comp hcoord).restrictScalars
  have htarget (c) : HR (a c) ∈ (chartAt (Fin d → ℂ) z).target := by
    change H (H.symm _) ∈ _
    rw [H.apply_symm_apply]
    exact (chartAt (Fin d → ℂ) z).map_source (hdom c).2
  have hP : AnalyticAt ℝ P b :=
    (((chartMetricOperator_contDiffOn g HR z).contDiffAt
      (((chartAt (Fin d → ℂ) z).open_target.preimage HR.continuous).mem_nhds (htarget b))).analyticAt).comp ha
  have hsection (c) (t : EuclideanSpace ℂ (Fin k)) : T c (v (c, t)) = t := by
    apply R.injective
    change R (R.symm (Q c (H (H.symm _)))) = R t
    rw [R.apply_symm_apply, H.apply_symm_apply]
    dsimp only [Q]
    rw [retainedFrameQuotientOperator_eq X Y j d k A hA U hU E z (σ c) (hdom c).1 (hdom c).2]
    funext i
    change retainedAffineConormalDifferential X Y j d A hA (σ c) (hU (hdom c).1) z
      (hdom c).2 (i1_conormalFrameBasis j.left k U E (σ c) (hdom c).1 i) (L c _) = R t i
    rw [heval, ← Module.Basis.dualBasis_equivFun _ _ i,
      LinearEquiv.apply_symm_apply]
  have hv : AnalyticAt ℝ v (b, R.symm w) := by
    have hfst : ContinuousAt (Prod.fst : (Fin m → ℂ) × EuclideanSpace ℂ (Fin k) → (Fin m → ℂ))
      (b, R.symm w) := continuous_fst.continuousAt
    apply metric_normal_vector_family_analytic
      (fun p => P p.1) (fun p => T p.1) Prod.snd v (b, R.symm w)
      (hP.comp (f := Prod.fst) (x := (b, R.symm w)) analyticAt_fst)
      (hT.comp (f := Prod.fst) (x := (b, R.symm w)) analyticAt_fst) analyticAt_snd
    · exact Filter.Eventually.of_forall (fun p => chartMetricOperator_positive g HR z (a p.1) (htarget p.1))
    · exact Filter.Eventually.of_forall (fun p t => ⟨v (p.1, t), hsection p.1 t⟩)
    · apply Filter.Eventually.of_forall
      intro p
      refine ⟨hsection p.1 p.2, ?_⟩
      intro t ht
      rw [chartMetricOperator_inner]
      change g.coefficient z (H (a p.1)) (H (v p)) (H t) = 0
      dsimp only [a, v]
      rw [H.apply_symm_apply, H.apply_symm_apply]
      apply horth
      intro u
      have ht' : Q p.1 (H t) = 0 := by
        have hh : R.symm (Q p.1 (H t)) = 0 := ht
        exact R.symm.injective (hh.trans (map_zero R.symm).symm)
      exact retainedFrameQuotientOperator_kernel X Y j d k A hA U hU E z (σ p.1)
        (hdom p.1).1 (hdom p.1).2 (H t) ht' u

  have hparam : AnalyticAt ℝ
      (fun p : (Fin m → ℂ) × (Fin k → ℂ) => (p.1, R.symm p.2)) (b, w) :=
    (analyticAt_fst : AnalyticAt ℝ (Prod.fst : (Fin m → ℂ) × (Fin k → ℂ) → (Fin m → ℂ)) (b, w)).prod
      (((R.symm.toContinuousLinearMap.restrictScalars ℝ).analyticAt _).comp analyticAt_snd)
  have hv' := hv.comp
    (f := (fun p : (Fin m → ℂ) × (Fin k → ℂ) => (p.1, R.symm p.2)))
    (x := (b, w)) hparam
  have hh := ((H.toContinuousLinearMap.restrictScalars ℝ).analyticAt _).comp
    (f := (fun p : (Fin m → ℂ) × (Fin k → ℂ) => v (p.1, R.symm p.2)))
    (x := (b, w)) hv'
  change AnalyticAt ℝ (fun p : (Fin m → ℂ) × (Fin k → ℂ) => H (v (p.1, R.symm p.2))) (b, w) at hh
  simpa only [v, H.apply_symm_apply, R.apply_symm_apply] using hh

#print axioms retained_fixed_chart_metric_analytic
end HodgeLean.Foundations.TubularEuler

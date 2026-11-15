import HodgeLean.Foundations.Program.G32Native.RetainedFixedChartMetricAnalytic
import HodgeLean.Foundations.Program.G32Native.ComplexRealManifoldRegularity
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Differentiated embedding vectors in fixed ambient coordinates -/

noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

theorem retained_fixed_chart_euclidean_analytic
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
    (n : ℕ) (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (w : Fin k → ℂ) :
    AnalyticAt ℝ (fun p : (Fin m → ℂ) × (Fin k → ℂ) =>
      fderiv ℝ (fun a => emb ((chartAt (Fin d → ℂ) z).symm a))
        ((chartAt (Fin d → ℂ) z) (Point.map j (σ p.1)))
        (L p.1 ((i1_conormalFrameBasis j.left k U E (σ p.1) (hdom p.1).1).dualBasis.equivFun.symm p.2)))
      (b, w) := by
  have hV := retained_fixed_chart_metric_analytic X Y j m d k A hA U hU E g σ b z
    hσ hdom L heval horth (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin d))
    (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin k)) w
  have hJ : ContMDiff 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (Point.map j) :=
    (HodgeLean.Foundations.Analytic.f4_isHom_iff_contMDiff (d := m) (e := d) _).mp
      (HodgeLean.Foundations.Analytic.f4_map_isHom j)
  have hcoord : AnalyticAt ℝ
      (fun c => (chartAt (Fin d → ℂ) z) (Point.map j (σ c))) b :=
    ((((contMDiffOn_chart (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) (x := z)).contMDiffAt
      ((chartAt (Fin d → ℂ) z).open_source.mem_nhds (hdom b).2)).comp b
        (hJ.contMDiffAt.comp b hσ)).contDiffAt.analyticAt).restrictScalars
  have htarget := (chartAt (Fin d → ℂ) z).map_source (hdom b).2
  have hInv := contMDiffAt_real_of_complex
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) (x := z)).contMDiffAt
      ((chartAt (Fin d → ℂ) z).open_target.mem_nhds htarget))
  have hEmb : AnalyticAt ℝ (fun a => emb ((chartAt (Fin d → ℂ) z).symm a))
      ((chartAt (Fin d → ℂ) z) (Point.map j (σ b))) :=
    (hemb.contMDiffAt.comp _ hInv).contDiffAt.analyticAt
  have hDer := hEmb.fderiv.comp
    (f := (fun c : Fin m → ℂ => (chartAt (Fin d → ℂ) z) (Point.map j (σ c))))
    (x := b) hcoord
  have hDer' := hDer.comp (f := (Prod.fst : (Fin m → ℂ) × (Fin k → ℂ) → (Fin m → ℂ)))
    (x := (b, w)) analyticAt_fst
  have hEval : AnalyticAt ℝ
      (fun p : ((Fin d → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin n)) × (Fin d → ℂ) => p.1 p.2)
      (fderiv ℝ (fun a => emb ((chartAt (Fin d → ℂ) z).symm a))
        ((chartAt (Fin d → ℂ) z) (Point.map j (σ b))),
        L b ((i1_conormalFrameBasis j.left k U E (σ b) (hdom b).1).dualBasis.equivFun.symm w)) :=
    isBoundedBilinearMap_apply.contDiff.contDiffAt.analyticAt
  exact hEval.comp₂ hDer' hV

#print axioms retained_fixed_chart_euclidean_analytic
end HodgeLean.Foundations.TubularEuler

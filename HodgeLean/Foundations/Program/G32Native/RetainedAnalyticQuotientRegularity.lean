import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanParameterAnalytic
import HodgeLean.Foundations.Program.G32Native.RetainedHolomorphicBaseInverse
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanSectionAgreement
import HodgeLean.Foundations.Program.G32Native.ComplexRealManifoldRegularity
import HodgeLean.Foundations.Program.G32Native.NormalFrameAdditionAnalytic
import HodgeLean.Foundations.BundleThom.NormalAtlasConstructionHelpers
import HodgeLean.Foundations.Program.G32Native.AnalyticQuotientFromEquations
import HodgeLean.Foundations.Program.G32Native.MetricNormalFamilyRegularity
import HodgeLean.Foundations.Program.G32Native.MetricNormalEuclideanAnalytic
import HodgeLean.Foundations.Program.G32Native.OriginalAffineEquationFrameCoefficients

/-! # Analytic regularity of the intrinsic metric quotient

The representatives are supplied pointwise on the original dual conormal.
The conclusion concerns their regularity, rather than selecting representatives.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Bundle
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler
open BundleThom HodgeLean.Adapters

private local instance normalFibreTop {Y : Over (Spec ↧ℂ)} {X : Scheme}
    (j : Y.left ⟶ X) (x : ComplexPoint Y) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop {Y : Over (Spec ↧ℂ)} {X : Scheme}
    (j : Y.left ⟶ X) (k : ℕ) :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- Pointwise metric representatives of an intrinsic conormal quotient vary
analytically in local algebraic normal frames. Their differentiated images
are continuous on the supplied algebraic frame domain in the original total
topology. This is the local inverse
Gram formula for the quotient of an analytic frame by an analytic subframe;
uniqueness identifies the formulas on overlaps.
Source: Hartshorne, Algebraic Geometry, II.8.17, conormal sequence for smooth
immersions; Lee, Introduction to Smooth Manifolds, second edition, Theorem
6.24, normal bundle construction; the analytic inverse-Gram calculation
`metricNormalLift_analyticAt` and `analyticAt_quotient_of_equation_coefficients`.
-/
theorem retained_analytic_quotient_regularity_aux
    (X Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : Y ⟶ X) [IsClosedImmersion j.left]
    (m k : ℕ) [SmoothOfRelativeDimension m Y.hom]
    [SmoothOfRelativeDimension (m + k) X.hom]
    (g : ChartHermitianMetric (ComplexPoint X) (m + k))
    (L : ∀ x : ComplexPoint Y, i1_normalFibre j.left x →ₗ[ℂ] (Fin (m + k) → ℂ))
    (hL : ∀ (A : X.left.Opens) (hA : IsAffineOpen A)
      (x : ComplexPoint Y) (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)),
      (∀ u a, retainedAffineConormalDifferential X Y j (m + k) A hA x hx
        (Point.map j x) (mem_chart_source _ _) a (L x u) = u a) ∧
      (∀ u w, (∀ a, retainedAffineConormalDifferential X Y j (m + k) A hA x hx
        (Point.map j x) (mem_chart_source _ _) a w = 0) →
        g.coefficient (Point.map j x)
          ((chartAt (Fin (m + k) → ℂ) (Point.map j x)) (Point.map j x)) (L x u) w = 0))
    (U : Y.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (n : ℕ) (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (m + k) → ℂ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb) :
    let δ := fun p : TotalSpace (Fin k → ℂ) (i1_normalFibre j.left) =>
      fderiv ℝ (fun c => emb ((chartAt (Fin (m + k) → ℂ)
        (Point.map j p.proj)).symm c))
        ((chartAt (Fin (m + k) → ℂ) (Point.map j p.proj)) (Point.map j p.proj))
        (L p.proj p.2)
    let e := i1_normalFrameTrivialization j.left k U E
    ContinuousOn δ e.source ∧
      ∀ (b : OpenPartialHomeomorph (ComplexPoint Y) (Fin m → ℂ)),
        a3b4_IsHolChart Y.hom (b.trans
          ((Homeomorph.prodUnique (Fin m → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph)) →
        ∀ y ∈ b.source,
          zeroSection (Fin k → ℂ) (i1_normalFibre j.left) y ∈ e.source →
          let P := e.toOpenPartialHomeomorph.trans
            (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
          AnalyticAt ℝ (fun q => δ (P.symm q)) (b y, 0) := by
  let δ := retainedEuclideanDisplacement X Y j (m + k) k n emb L
  let e := i1_normalFrameTrivialization j.left k U E
  constructor
  · change ContinuousOn δ e.source
    intro p hp
    apply ContinuousAt.continuousWithinAt
    let b := chartAt (Fin m → ℂ) p.proj
    let P := e.toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
    have hy : p.proj ∈ b.source := mem_chart_source _ _
    have hproj : (e p).1 = p.proj := e.proj_toFun p hp
    have hpP : p ∈ P.source := by
      refine ⟨hp, ?_⟩
      change (e p).1 ∈ b.source ∧ (e p).2 ∈ Set.univ
      rw [hproj]
      exact ⟨hy, Set.mem_univ _⟩
    have hσ := (contMDiffOn_chart_symm (I := 𝓘(ℂ, Fin m → ℂ)) (n := ω)
      (x := p.proj)).contMDiffAt (b.open_target.mem_nhds (b.map_source hy))
    have hU : b.symm (b p.proj) ∈ Point.overOpen U := by
      rw [b.left_inv hy]
      exact hp
    have ha := retained_euclidean_parameter_analytic X Y j m (m + k) k g L hL U E
      n emb hemb b.symm (b p.proj) hσ hU (e p).2
    have hPp : P p = (b p.proj, (e p).2) := by
      change (b (e p).1, (e p).2) = _
      rw [hproj]
    have hmodel : AnalyticAt ℝ (fun q => δ (P.symm q)) (P p) := by
      rw [hPp]
      exact ha
    have hc : ContinuousAt (fun t => δ (P.symm (P t))) p :=
      hmodel.continuousAt.comp (P.continuousAt hpP)
    apply hc.congr_of_eventuallyEq
    filter_upwards [P.open_source.mem_nhds hpP] with t ht
    exact congrArg δ (P.left_inv ht).symm
  · intro b hb y hy hye
    have hσ := (retained_holomorphic_base_inverse Y m b hb).contMDiffAt
      (b.open_target.mem_nhds (b.map_source hy))
    have hU : b.symm (b y) ∈ Point.overOpen U := by
      rw [b.left_inv hy]
      exact hye
    have ha := retained_euclidean_parameter_analytic X Y j m (m + k) k g L hL U E
      n emb hemb b.symm (b y) hσ hU (0 : Fin k → ℂ)
    exact ha

#print axioms retained_analytic_quotient_regularity_aux
end HodgeLean.Foundations.TubularEuler

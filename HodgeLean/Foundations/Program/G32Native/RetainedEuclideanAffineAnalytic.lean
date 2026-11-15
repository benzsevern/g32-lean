import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanDisplacement
import HodgeLean.Foundations.Program.G32Native.RetainedFixedChartEuclideanAnalytic
import HodgeLean.Foundations.Program.G32Native.RetainedConormalInjective
import HodgeLean.Foundations.Program.G32Native.RetainedFrameInverseCoordinates
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanSectionAgreement

/-! # Analytic Euclidean displacement in the original algebraic normal frame -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Filter Topology Bundle
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler
open BundleThom HodgeLean.Adapters

private local instance normalTotalTop {Y : Over (Spec ↧ℂ)} {X : Scheme}
    (j : Y.left ⟶ X) (k : ℕ) :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

theorem retained_euclidean_affine_parameter_analytic
    (X Y : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : Y ⟶ X) [IsClosedImmersion j.left]
    (m d k : ℕ) [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    (g : ChartHermitianMetric (ComplexPoint X) d)
    (L : ∀ x : ComplexPoint Y, i1_normalFibre j.left x →ₗ[ℂ] (Fin d → ℂ))
    (hL : ∀ (A : X.left.Opens) (hA : IsAffineOpen A)
      (x : ComplexPoint Y) (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)),
      (∀ u a, retainedAffineConormalDifferential X Y j d A hA x hx
        (Point.map j x) (mem_chart_source _ _) a (L x u) = u a) ∧
      (∀ u w, (∀ a, retainedAffineConormalDifferential X Y j d A hA x hx
        (Point.map j x) (mem_chart_source _ _) a w = 0) →
        g.coefficient (Point.map j x)
          ((chartAt (Fin d → ℂ) (Point.map j x)) (Point.map j x)) (L x u) w = 0))
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (U : Y.left.Opens) (hU : U ≤ j.left ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (n : ℕ) (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (σ : (Fin m → ℂ) → ComplexPoint Y) (b : Fin m → ℂ)
    (hσ : ContMDiffAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω σ b)
    (z : ComplexPoint X)
    (hdom : ∀ c, σ c ∈ Point.overOpen U ∧
      Point.map j (σ c) ∈ (chartAt (Fin d → ℂ) z).source)
    (w : Fin k → ℂ) :
    AnalyticAt ℝ (fun q : (Fin m → ℂ) × (Fin k → ℂ) =>
      retainedEuclideanDisplacement X Y j d k n emb L
        ((i1_normalFrameTrivialization j.left k U E).toOpenPartialHomeomorph.symm (σ q.1, q.2)))
      (b, w) := by
  classical
  have hi (c) := retained_conormal_differential_injective X Y j m d A hA
    (σ c) (hU (hdom c).1) z (hdom c).2
  have hex (c) := retained_hermitian_normal_section X Y j d g A hA
    (σ c) (hU (hdom c).1) z (hdom c).2 (hi c)
  choose Lz hLi hLe hLo using hex
  have hfix := retained_fixed_chart_euclidean_analytic X Y j m d k A hA U hU E g
    σ b z hσ hdom Lz hLe hLo n emb hemb w
  apply (hfix.contDiffAt.congr_of_eventuallyEq ?_).analyticAt
  apply Filter.Eventually.of_forall
  intro q
  exact retained_euclidean_displacement_frame_formula X Y j d k n g emb hemb A hA U E
    (σ q.1) (hdom q.1).1 (hU (hdom q.1).1) z (hdom q.1).2 (hi q.1) L (Lz q.1)
    (fun u => ⟨fun a => (hL A hA (σ q.1) (hU (hdom q.1).1)).1 u a,
      fun t ht => (hL A hA (σ q.1) (hU (hdom q.1).1)).2 u t ht⟩)
    (fun u => ⟨hLe q.1 u, hLo q.1 u⟩) q.2

#print axioms retained_euclidean_affine_parameter_analytic
end HodgeLean.Foundations.TubularEuler

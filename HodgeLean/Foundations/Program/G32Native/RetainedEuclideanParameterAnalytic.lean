import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanAffineAnalytic
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanDisplacement
import HodgeLean.Foundations.Program.G32Native.RetainedFixedChartEuclideanAnalytic
import HodgeLean.Foundations.Program.G32Native.RetainedParameterLocalization
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

/-- The differentiated representatives are analytic along analytic base
parameters in the specified original algebraic normal frame. -/
theorem retained_euclidean_parameter_analytic
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
    (U : Y.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (n : ℕ) (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (σ : (Fin m → ℂ) → ComplexPoint Y) (b : Fin m → ℂ)
    (hσ : ContMDiffAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω σ b)
    (hbU : σ b ∈ Point.overOpen U) (w : Fin k → ℂ) :
    AnalyticAt ℝ (fun q : (Fin m → ℂ) × (Fin k → ℂ) =>
      retainedEuclideanDisplacement X Y j d k n emb L
        ((i1_normalFrameTrivialization j.left k U E).toOpenPartialHomeomorph.symm (σ q.1, q.2)))
      (b, w) := by
  classical
  let z := Point.map j (σ b)
  obtain ⟨A, hA, hzA, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := z.underlying) (U := ⊤) (by trivial)
  let U₀ := U ⊓ j.left ⁻¹ᵁ A
  have h₀U : U₀ ≤ U := inf_le_left
  have h₀A : U₀ ≤ j.left ⁻¹ᵁ A := inf_le_right
  let E₀ := i1_conormalFrameRestriction j.left k h₀U E
  let S : Set (ComplexPoint Y) := Point.overOpen U₀ ∩
    (Point.map j) ⁻¹' (chartAt (Fin d → ℂ) z).source
  have hS : IsOpen S := (Point.isOpen_overOpen U₀).inter
    ((chartAt (Fin d → ℂ) z).open_source.preimage (Point.continuous_map j))
  have hbS : σ b ∈ S := by
    refine ⟨⟨hbU, hzA⟩, ?_⟩
    exact mem_chart_source (Fin d → ℂ) z
  obtain ⟨τ, hτ, hτS, hτeq, _⟩ := localize_manifold_parameter σ b S hS hbS hσ
  have hdom (c) : τ c ∈ Point.overOpen U₀ ∧
      Point.map j (τ c) ∈ (chartAt (Fin d → ℂ) z).source := hτS c
  have hlocal := retained_euclidean_affine_parameter_analytic X Y j m d k g L hL
    A hA U₀ h₀A E₀ n emb hemb τ b hτ z hdom w
  apply (hlocal.contDiffAt.congr_of_eventuallyEq ?_).analyticAt
  have hfst : ContinuousAt (Prod.fst : (Fin m → ℂ) × (Fin k → ℂ) → (Fin m → ℂ)) (b, w) :=
    continuous_fst.continuousAt
  filter_upwards [hfst.eventually hτeq] with q hq
  rw [← hq]
  exact congrArg (retainedEuclideanDisplacement X Y j d k n emb L)
    (retained_normal_frame_inverse_restriction j.left k h₀U E (τ q.1) (hdom q.1).1 q.2).symm

#print axioms retained_euclidean_parameter_analytic
end HodgeLean.Foundations.TubularEuler

import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanNormalFieldData
import HodgeLean.Foundations.Program.G32Native.RetainedConormalAffineIndependence
import HodgeLean.Foundations.Program.G32Native.RetainedAnalyticQuotientRegularity

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Bundle
open scoped Manifold ContDiff
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom
variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
variable [SmoothOfRelativeDimension k Q.hom]
variable [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)]
attribute [local instance] retainedNormalFieldFibreTopology retainedNormalFieldTotalTopology
  retainedNormalFieldLiftClosed retainedNormalFieldAmbientDimension
local notation "X" => Over.mk (v ≫ W.hom)
local notation "J" => i1_smoothLift ι v j hj
local notation "NT" => TotalSpace (Fin k → ℂ) (i1_normalFibre j)
local notation "zN" => zeroSection (Fin k → ℂ) (i1_normalFibre j)


/-- Chart-independent metric representatives for a supplied family of sections. -/
theorem retained_euclidean_metric_section
    (hD : ∀ (A : V.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Q)
      (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) (z : ComplexPoint X)
      (hz : Point.map J x ∈ (chartAt (Fin (k + k) → ℂ) z).source),
      Function.Injective (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz) ∧
      Module.finrank ℂ (LinearMap.range
        (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz)) = k)
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (L : ∀ x : ComplexPoint Q, i1_normalFibre j x →ₗ[ℂ] (Fin (k + k) → ℂ))
    (hL : ∀ (B : V.Opens) (hB : IsAffineOpen B) (x : ComplexPoint Q)
      (hxB : x ∈ Point.overOpen (j ⁻¹ᵁ B)),
      (∀ u a, retainedAffineConormalDifferential X Q J (k + k) B hB x hxB
        (Point.map J x) (mem_chart_source _ _) a (L x u) = u a) ∧
      (∀ u w, (∀ a, retainedAffineConormalDifferential X Q J (k + k) B hB x hxB
        (Point.map J x) (mem_chart_source _ _) a w = 0) →
        g.coefficient (Point.map J x)
          ((chartAt (Fin (k + k) → ℂ) (Point.map J x)) (Point.map J x)) (L x u) w = 0)) :
    ∀ (A : V.Opens) (hA : IsAffineOpen A)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A))
    (z : ComplexPoint X)
    (hz : Point.map J x ∈ (chartAt (Fin (k + k) → ℂ) z).source),
    ∃ Lz : i1_normalFibre j x →ₗ[ℂ] (Fin (k + k) → ℂ),
      (∀ u a, retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz a (Lz u) = u a) ∧
      (∀ u w, (∀ a, retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz a w = 0) →
        g.coefficient z ((chartAt (Fin (k + k) → ℂ) z) (Point.map J x)) (Lz u) w = 0) ∧
      ∀ u, fderiv ℝ (fun c => emb ((chartAt (Fin (k + k) → ℂ) (Point.map J x)).symm c))
        ((chartAt (Fin (k + k) → ℂ) (Point.map J x)) (Point.map J x)) (L x u) =
        fderiv ℝ (fun c => emb ((chartAt (Fin (k + k) → ℂ) z).symm c))
          ((chartAt (Fin (k + k) → ℂ) z) (Point.map J x)) (Lz u) := by
  intro B hB x hxB z hz
  obtain ⟨Lz, _, hze, hzo⟩ := retained_hermitian_normal_section
    X Q J (k + k) g B hB x hxB z hz (hD B hB x hxB z hz).1
  refine ⟨Lz, hze, hzo, ?_⟩
  exact retained_euclidean_sections_change_chart X Q J (k + k) n g emb hemb
    B hB x hxB (Point.map J x) z (mem_chart_source _ _) hz
    (hD B hB x hxB z hz).1 (L x) Lz
    (fun u => ⟨fun a => (hL B hB x hxB).1 u a,
      fun w hw => (hL B hB x hxB).2 u w hw⟩)
    (fun u => ⟨hze u, hzo u⟩)

#print axioms retained_euclidean_metric_section
end HodgeLean.Foundations.TubularEuler

import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanMetricChoiceSpec
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanMetricFamily
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanMetricPoint
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanNormalFieldData
import HodgeLean.Foundations.Program.G32Native.RetainedConormalAffineIndependence
import HodgeLean.Foundations.Program.G32Native.RetainedAnalyticQuotientRegularity

noncomputable section
set_option maxHeartbeats 400000
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


theorem retainedEuclideanMetricChoice_formula
    (hD : ∀ (A : V.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Q)
      (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) (z : ComplexPoint X)
      (hz : Point.map J x ∈ (chartAt (Fin (k + k) → ℂ) z).source),
      Function.Injective (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz) ∧
      Module.finrank ℂ (LinearMap.range
        (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz)) = k)
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (x : ComplexPoint Q) :
    let L := retainedEuclideanMetricChoice ι k v j hj hD g x
    ∀ (A : V.Opens) (hA : IsAffineOpen A)
    (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A))
    (z : ComplexPoint X)
    (hz : Point.map J x ∈ (chartAt (Fin (k + k) → ℂ) z).source),
    ∃ Lz : i1_normalFibre j x →ₗ[ℂ] (Fin (k + k) → ℂ),
      (∀ u a, retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz a (Lz u) = u a) ∧
      (∀ u w, (∀ a, retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz a w = 0) →
        g.coefficient z ((chartAt (Fin (k + k) → ℂ) z) (Point.map J x)) (Lz u) w = 0) ∧
      ∀ u, fderiv ℝ (fun c => emb ((chartAt (Fin (k + k) → ℂ) (Point.map J x)).symm c))
        ((chartAt (Fin (k + k) → ℂ) (Point.map J x)) (Point.map J x)) (L u) =
        fderiv ℝ (fun c => emb ((chartAt (Fin (k + k) → ℂ) z).symm c))
          ((chartAt (Fin (k + k) → ℂ) z) (Point.map J x)) (Lz u) := by
  exact retained_euclidean_metric_point ι k v j hj hD g n emb hemb x
    (retainedEuclideanMetricChoice ι k v j hj hD g x)
    (retainedEuclideanMetricChoice_spec ι k v j hj hD g x)


#print axioms retainedEuclideanMetricChoice_formula
end HodgeLean.Foundations.TubularEuler

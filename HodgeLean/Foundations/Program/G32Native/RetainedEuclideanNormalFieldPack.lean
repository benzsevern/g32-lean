import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanMetricFamily
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanMetricSection
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


/-- Package the retained displacement, linear frames and their field equations. -/
theorem retained_euclidean_normal_field_pack (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (g : ChartHermitianMetric (ComplexPoint X) (k + k))
    (displacement : C(NT, EuclideanSpace ℝ (Fin n)))
    (zero : ∀ x, displacement (zN x) = 0)
    (frame : ∀ x : ComplexPoint Q,
    Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j)))
    (frame_linear : ∀ x, (frame x).IsLinear ℂ)
    (frame_mem : ∀ x, zN x ∈ (frame x).source)
    (analytic : ∀ (x : ComplexPoint Q)
    (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ)),
    a3b4_IsHolChart Q.hom (b.trans
      ((Homeomorph.prodUnique (Fin k → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph)) →
    ∀ y ∈ b.source, zN y ∈ (frame x).source →
      let P := (frame x).toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
      AnalyticAt ℝ (fun q => displacement (P.symm q)) (b y, 0))
    (metric_evaluation : ∀ (A : V.Opens) (hA : IsAffineOpen A)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A))
    (z : ComplexPoint X)
    (hz : Point.map J x ∈ (chartAt (Fin (k + k) → ℂ) z).source),
    ∃ L : i1_normalFibre j x →ₗ[ℂ] (Fin (k + k) → ℂ),
      (∀ u a, retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz a (L u) = u a) ∧
      (∀ u w, (∀ a, retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz a w = 0) →
        g.coefficient z ((chartAt (Fin (k + k) → ℂ) z) (Point.map J x)) (L u) w = 0) ∧
      ∀ u, displacement ⟨x, u⟩ =
        fderiv ℝ (fun c => emb ((chartAt (Fin (k + k) → ℂ) z).symm c))
          ((chartAt (Fin (k + k) → ℂ) z) (Point.map J x)) (L u)) :
    Nonempty (RetainedEuclideanNormalField ι k v j hj n emb g) :=
  ⟨{ displacement := displacement, zero := zero, frame := frame, frame_linear := frame_linear, frame_mem := frame_mem, analytic := analytic, metric_evaluation := metric_evaluation }⟩

#print axioms retained_euclidean_normal_field_pack
end HodgeLean.Foundations.TubularEuler

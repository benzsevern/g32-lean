import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanMetricChoiceFormula
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanNormalFieldAssembly
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


/-- The metric normal representatives have compatible analytic Euclidean displacement.
This step compares the original affine fibre identifications on overlaps and
uses the inverse Gram coefficient formula in the retained linear frames.
Source: Lee, Introduction to Smooth Manifolds, second edition, normal bundle
construction in Theorem 6.24; Hirsch, Differential Topology, chapter 4, section 5.
HC no distance; AV milestone no distance. -/
theorem retained_euclidean_normal_field_aux
    (hD : ∀ (A : V.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Q)
      (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) (z : ComplexPoint X)
      (hz : Point.map J x ∈ (chartAt (Fin (k + k) → ℂ) z).source),
      Function.Injective (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz) ∧
      Module.finrank ℂ (LinearMap.range
        (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz)) = k)
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb) :
    Nonempty (RetainedEuclideanNormalField ι k v j hj n emb g) := by
  let L := fun x : ComplexPoint Q => retainedEuclideanMetricChoice ι k v j hj hD g x
  exact retained_euclidean_normal_field_of_sections ι k v j hj g n emb hemb L
    (fun B hB x hxB => retainedEuclideanMetricChoice_spec ι k v j hj hD g x B hB hxB)
    (i1_smoothConormalFrameAt j k (v ≫ W.hom) (Over.w J))
    (fun A hA x hx z hz => retainedEuclideanMetricChoice_formula
      ι k v j hj hD g n emb hemb x A hA hx z hz)

#print axioms retained_euclidean_normal_field_aux
end HodgeLean.Foundations.TubularEuler

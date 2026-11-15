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


/-- A metric section on each fibre compatible with every affine presentation. -/
theorem retained_euclidean_metric_family
    (hD : ∀ (A : V.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Q)
      (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) (z : ComplexPoint X)
      (hz : Point.map J x ∈ (chartAt (Fin (k + k) → ℂ) z).source),
      Function.Injective (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz) ∧
      Module.finrank ℂ (LinearMap.range
        (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz)) = k)
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) :
    ∀ x : ComplexPoint Q, ∃ L : i1_normalFibre j x →ₗ[ℂ] (Fin (k + k) → ℂ),
    ∀ (B : V.Opens) (hB : IsAffineOpen B)
      (hxB : x ∈ Point.overOpen (j ⁻¹ᵁ B)),
      (∀ u a, retainedAffineConormalDifferential X Q J (k + k) B hB x hxB
        (Point.map J x) (mem_chart_source _ _) a (L u) = u a) ∧
      (∀ u w, (∀ a, retainedAffineConormalDifferential X Q J (k + k) B hB x hxB
        (Point.map J x) (mem_chart_source _ _) a w = 0) →
        g.coefficient (Point.map J x)
          ((chartAt (Fin (k + k) → ℂ) (Point.map J x)) (Point.map J x)) (L u) w = 0) := by
  intro x
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  obtain ⟨A, hA, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := (Point.map J x).underlying) (U := ⊤) (by trivial)
  obtain ⟨L, _, hLe, hLo⟩ := retained_hermitian_normal_section
    X Q J (k + k) g A hA x hx (Point.map J x)
    (mem_chart_source _ _) (hD A hA x hx _ _).1
  refine ⟨L, ?_⟩
  intro B hB hxB
  have heq := retainedAffineConormalDifferential_independent_affine_aux
    X Q J (k + k) B A hB hA x hxB hx
    (Point.map J x) (mem_chart_source _ _)
  rw [heq]
  exact ⟨hLe, hLo⟩

#print axioms retained_euclidean_metric_family
end HodgeLean.Foundations.TubularEuler

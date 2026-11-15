import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanNormalFieldRegularity
import HodgeLean.Foundations.Program.G32Native.RetainedNormalFrameSource
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanNormalFieldPack
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
theorem retained_euclidean_normal_field_of_sections
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
          ((chartAt (Fin (k + k) → ℂ) (Point.map J x)) (Point.map J x)) (L x u) w = 0))
    (frames : ∀ x : ComplexPoint Q, Σ U : Q.left.Opens,
      {E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
        SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k) //
          x ∈ Point.overOpen U})
    (hmetric : ∀ (A : V.Opens) (hA : IsAffineOpen A)
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
          ((chartAt (Fin (k + k) → ℂ) z) (Point.map J x)) (Lz u)) :
    Nonempty (RetainedEuclideanNormalField ι k v j hj n emb g) := by
  let δ : NT → EuclideanSpace ℝ (Fin n) := fun p =>
    fderiv ℝ (fun c => emb ((chartAt (Fin (k + k) → ℂ)
      (Point.map J p.proj)).symm c))
      ((chartAt (Fin (k + k) → ℂ) (Point.map J p.proj)) (Point.map J p.proj))
      (L p.proj p.2)
  let e := fun x : ComplexPoint Q =>
    i1_normalFrameTrivialization j k (frames x).1 (frames x).2.1
  have hcont : Continuous δ := retained_euclidean_displacement_continuous
    ι k v j hj g n emb hemb L hL frames
  obtain ⟨displacement, hdisplacement⟩ :
      ∃ displacement : C(NT, EuclideanSpace ℝ (Fin n)), ∀ p, displacement p = δ p :=
    ⟨⟨δ, hcont⟩, fun _ => rfl⟩
  have hFun : (displacement : NT → EuclideanSpace ℝ (Fin n)) = δ :=
    funext hdisplacement
  refine retained_euclidean_normal_field_pack ι k v j hj n emb g
    displacement ?_ e
    (fun x => i1_normalFrameTrivialization_isLinear j k (frames x).1 (frames x).2.1)
    (fun x => (retained_normalFrame_mem_source (k := k) (j := j)
      (frames x).1 (frames x).2.1 (zN x)).mpr (frames x).2.2) ?_ ?_
  · intro x
    rw [hdisplacement]
    dsimp only [δ, Bundle.zeroSection]
    rw [map_zero, map_zero]
  · rw [hFun]
    exact retained_euclidean_displacement_analytic ι k v j hj g n emb hemb L hL frames
  · rw [hFun]
    exact hmetric

#print axioms retained_euclidean_normal_field_of_sections
end HodgeLean.Foundations.TubularEuler

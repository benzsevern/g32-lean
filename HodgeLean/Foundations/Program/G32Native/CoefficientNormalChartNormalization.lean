import HodgeLean.Foundations.Program.G32Native.CoefficientNormalChartFactorization
import HodgeLean.Foundations.Program.G32Native.ZeroRankLocalDetection

/-! # Local complex normalization of the original coefficient pullback -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular Bundle TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations.BundleThom
open HodgeLean.Foundations.Program.G32Native.EulerModel
namespace HodgeLean.Foundations.Program.G32Native
variable (G : CanonicalAbelGeometry) (D : CoefficientNormalIdentification G)
local instance (x : ComplexPoint G.Q) : TopologicalSpace (i1_normalFibre G.ι.left x) :=
  i1_normalFibreTopology G.ι.left x
local instance : TopologicalSpace (TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left)) :=
  i1_normalTotalTopology G.ι.left G.k
variable [FiberBundle (Fin G.k → ℂ) (i1_normalFibre G.ι.left)]
variable [VectorBundle ℂ (Fin G.k → ℂ) (i1_normalFibre G.ι.left)]
variable (e : Trivialization (Fin G.k → ℂ)
  (TotalSpace.proj : TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left) → ComplexPoint G.Q))
variable [e.IsLinear ℂ]

/-- The actual invertible matrix map over the analytic/model chart overlap. -/
def coefficientNormalChartMatrixPair (j : Fin (G.k + 1)) :
    i1_productNormalPair (coefficientNormalChartBaseOpen G e j) G.k ⟶ puncturedPair ℂ G.k :=
  i1_productMatrixNormalMap G.k
    (fun b : coefficientNormalChartBaseOpen G e j => coefficientNormalChartMatrix G D e j b.1)
    ((continuous_coefficientNormalChartMatrix G D e j).comp continuous_subtype_val)
    (fun b => coefficientNormalChartMatrix_det_ne_zero G D e j b.1 b.2)

/-- The model normal coordinate is exactly the action of the actual complex matrix. -/
theorem coefficientNormalChartLift_normal_apply (j : Fin (G.k + 1))
    (bv : (coefficientNormalChartBaseOpen G e j) × (Fin G.k → ℂ)) :
    (normalCoordinateKernelChart G.k j
      (TopPair.Hom.fst (coefficientNormalChartLift G D e j) bv).val).2 =
        (coefficientNormalChartMatrix G D e j bv.1.1).mulVec bv.2 := by
  rw [normalCoordinateKernelChart_apply G.k j _
    (TopPair.Hom.fst (coefficientNormalChartLift G D e j) bv).property]
  change (normalCoordinatePermutation G.k (Equiv.swap 0 j)
    (TopPair.Hom.fst (coefficientNormalChartComposite G D e j) bv).val.2).2 = _
  rw [coefficientNormalChartComposite_apply]
  change _ = (LinearMap.toMatrix' (coefficientNormalChartLinearMap G D e j bv.1.1)).mulVec bv.2
  rw [LinearMap.toMatrix'_mulVec]
  exact (coefficientNormalChartLinearMap_apply G D e j bv.1.1 bv.2).symm

/-- The lifted coefficient map factors normal projection through its invertible complex matrix family. -/
theorem coefficientNormalChartLift_comp_projection (j : Fin (G.k + 1)) :
    coefficientNormalChartLift G D e j ≫
      chartNormalProjectionPair (Fin G.k → ℂ) G.k (normalCoordinateKernelChart G.k j)
        {w | w.1.2 = 0} (normalCoordinateKernelChart_support G.k j)
        (normalKernelCoclassChartOpen G.k j) (le_refl _) =
      coefficientNormalChartMatrixPair G D e j := by
  apply MorphismProperty.Arrow.Hom.ext
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro bv
    exact Subtype.ext (coefficientNormalChartLift_normal_apply G D e j bv.1)
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro bv
    exact coefficientNormalChartLift_normal_apply G D e j bv

/-- On every specified chart overlap the original model Thom class pulls back to the complex normal orientation. -/
theorem coefficientNormalChartComposite_normalization (j : Fin (G.k + 1)) :
    relativeCohomologyMap ℚ (2 * G.k) (coefficientNormalChartComposite G D e j)
      (normalKernelGlobalThomClass G.k) =
    relativeCohomologyMap ℚ (2 * G.k)
      (i1_productNormalProjection (coefficientNormalChartBaseOpen G e j) G.k)
      (normalizedPointCoclass G.k) := by
  have h := congrArg (relativeCohomologyMap ℚ (2 * G.k) (coefficientNormalChartLift G D e j))
    (coefficientModelChart_normalization G.k j)
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    coefficientNormalChartLift_comp_inclusion] at h
  unfold chartNormalProjectionCoclass at h
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    coefficientNormalChartLift_comp_projection] at h
  exact h.trans (productMatrixNormalMap_thomDegree_pullback_allRanks G.k _ _ _ _)

end HodgeLean.Foundations.Program.G32Native

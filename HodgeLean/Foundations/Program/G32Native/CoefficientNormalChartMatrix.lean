import HodgeLean.Foundations.Program.G32Native.CoefficientNormalHomeomorph
import HodgeLean.Foundations.Program.G32Native.ContinuousNormalMatrix
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelChartTransitions

/-! # Complex linear coordinate maps from analytic normal charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Bundle TopologicalSpace
open HodgeLean.Foundations.BundleThom
open HodgeLean.Foundations.Program.G32Native.EulerModel
namespace HodgeLean.Foundations.Program.G32Native
variable (G : CanonicalAbelGeometry) (D : CoefficientNormalIdentification G)
local instance : TopologicalSpace (TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left)) :=
  i1_normalTotalTopology G.ι.left G.k
variable (e : Trivialization (Fin G.k → ℂ)
  (TotalSpace.proj : TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left) → ComplexPoint G.Q))
variable [e.IsLinear ℂ]

/-- The literal model normal-coordinate map on an analytic normal fibre. -/
def coefficientNormalChartLinearMap (j : Fin (G.k + 1)) (b : e.baseSet) :
    (Fin G.k → ℂ) →ₗ[ℂ] (Fin G.k → ℂ) :=
  (LinearMap.snd ℂ ℂ (Fin G.k → ℂ)).comp
    ((normalCoordinatePermutation G.k (Equiv.swap 0 j)).toLinearMap.comp
      ((coefficientModelCoordinates G.k).toLinearMap.comp
        (((g32n_homogeneousLine G.k G.eQ b.1).submodule.dualAnnihilator.subtype).comp
          ((D.fibre b.1).toLinearMap.comp (e.linearEquivAt ℂ b.1 b.2).symm.toLinearMap))))

/-- The chart map uses the same original normal vector and ordered coefficient total map. -/
theorem coefficientNormalChartLinearMap_apply (j : Fin (G.k + 1))
    (b : e.baseSet) (v : Fin G.k → ℂ) :
    coefficientNormalChartLinearMap G D e j b v =
      (normalCoordinatePermutation G.k (Equiv.swap 0 j)
        (coefficientNormalTotalMap G D
          ⟨b.1, (e.linearEquivAt ℂ b.1 b.2).symm v⟩).val.2).2 := by
  change (normalCoordinatePermutation G.k (Equiv.swap 0 j)
    (coefficientModelCoordinates G.k _)).2 = _
  rw [coefficientModelCoordinates_apply]
  rfl

/-- On a model chart over this base, the complex linear normal-coordinate map is injective. -/
theorem coefficientNormalChartLinearMap_injective (j : Fin (G.k + 1))
    (b : e.baseSet)
    (hb : normalPermutationBaseHomeomorph G.k (Equiv.swap 0 j)
      (coefficientBaseHomeomorph G b.1) ∈ Set.range (normalProjectiveChart G.k)) :
    Function.Injective (coefficientNormalChartLinearMap G D e j b) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hchart : coefficientNormalTotalMap G D
      ⟨b.1, (e.linearEquivAt ℂ b.1 b.2).symm v⟩ ∈
      (normalCoordinateKernelChart G.k j).source := by
    rw [normalCoordinateKernelChart_source, normalCoordinateKernelParam_range]
    exact hb
  have hz : (normalCoordinateKernelChart G.k j
      (coefficientNormalTotalMap G D ⟨b.1, (e.linearEquivAt ℂ b.1 b.2).symm v⟩)).2 = 0 := by
    rw [normalCoordinateKernelChart_apply G.k j _ hchart]
    exact (coefficientNormalChartLinearMap_apply G D e j b v).symm.trans hv
  have hzero := (normalCoordinateKernelChart_support G.k j _ hchart).mpr hz
  have hn := (coefficientNormalTotalMap_zero_iff G D
    ⟨b.1, (e.linearEquivAt ℂ b.1 b.2).symm v⟩).mp hzero
  exact (e.linearEquivAt ℂ b.1 b.2).symm.map_eq_zero_iff.mp hn

/-- Normal coordinates vary continuously with both analytic base and normal vector. -/
theorem continuous_coefficientNormalChartLinearMap_apply (j : Fin (G.k + 1)) :
    Continuous (fun bv : e.baseSet × (Fin G.k → ℂ) =>
      coefficientNormalChartLinearMap G D e j bv.1 bv.2) := by
  have hp : Continuous (fun bv : e.baseSet × (Fin G.k → ℂ) =>
      (⟨bv.1.1, (e.linearEquivAt ℂ bv.1.1 bv.1.2).symm bv.2⟩ :
        TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left))) := by
    apply (continuous_subtype_val.comp e.sourceHomeomorphBaseSetProd.symm.continuous).congr
    intro bv
    change e.toPartialEquiv.symm (bv.1.1, bv.2) =
      (⟨bv.1.1, e.symm bv.1.1 bv.2⟩ : TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left))
    exact (e.mk_symm bv.1.2 bv.2).symm
  have hc := continuous_snd.comp (continuous_subtype_val.comp
    ((coefficientNormalTotalMap G D).continuous.comp hp))
  have h := continuous_snd.comp
    ((normalCoordinatePermutation G.k (Equiv.swap 0 j)).toLinearMap.continuous_of_finiteDimensional.comp hc)
  exact h.congr (fun bv => (coefficientNormalChartLinearMap_apply G D e j bv.1 bv.2).symm)

/-- The actual complex matrix of the analytic-to-model normal-coordinate map. -/
def coefficientNormalChartMatrix (j : Fin (G.k + 1)) (b : e.baseSet) :
    Matrix (Fin G.k) (Fin G.k) ℂ :=
  LinearMap.toMatrix' (coefficientNormalChartLinearMap G D e j b)

/-- The actual normal-coordinate matrices vary continuously on the analytic chart base. -/
theorem continuous_coefficientNormalChartMatrix (j : Fin (G.k + 1)) :
    Continuous (coefficientNormalChartMatrix G D e j) :=
  continuous_normalMatrix_of_joint G.k (coefficientNormalChartLinearMap G D e j)
    (continuous_coefficientNormalChartLinearMap_apply G D e j)

/-- Every model chart overlap has an invertible complex normal-coordinate matrix. -/
theorem coefficientNormalChartMatrix_det_ne_zero (j : Fin (G.k + 1))
    (b : e.baseSet)
    (hb : normalPermutationBaseHomeomorph G.k (Equiv.swap 0 j)
      (coefficientBaseHomeomorph G b.1) ∈ Set.range (normalProjectiveChart G.k)) :
    (coefficientNormalChartMatrix G D e j b).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w h
  apply coefficientNormalChartLinearMap_injective G D e j b hb
  exact (LinearMap.toMatrix'_mulVec _ v).symm.trans
    (h.trans (LinearMap.toMatrix'_mulVec _ w))

end HodgeLean.Foundations.Program.G32Native

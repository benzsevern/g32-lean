import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelChartTransitions
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Analytic coordinate changes for the actual global kernel atlas -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified homogeneous-ratio kernel coordinate formula is analytic wherever its actual denominator is nonzero. -/
theorem normalKernelCoordinateFormula_analyticAt (k : ℕ)
    (A : (ℂ × (Fin k → ℂ)) ≃ₗ[ℂ] (ℂ × (Fin k → ℂ)))
    (za : (Fin k → ℂ) × (Fin k → ℂ)) (hne : (A (1, za.1)).1 ≠ 0) :
    AnalyticAt ℂ (fun zb : (Fin k → ℂ) × (Fin k → ℂ) =>
      (homogeneousNormalChartCoordinate k (A (1, zb.1)),
        (A (normalKernelChart k zb.1 zb.2).1).2)) za := by
  have hA (v : ℂ × (Fin k → ℂ)) : AnalyticAt ℂ A v :=
    A.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt v
  have hv : AnalyticAt ℂ (fun zb : (Fin k → ℂ) × (Fin k → ℂ) => A (1, zb.1)) za :=
    (hA _).comp (analyticAt_const.prod analyticAt_fst)
  have hs : AnalyticAt ℂ (fun zb : (Fin k → ℂ) × (Fin k → ℂ) =>
      ∑ r : Fin k, zb.1 r * zb.2 r) za := by
    apply Finset.analyticAt_fun_sum
    intro r hr
    exact (((ContinuousLinearMap.proj r : (Fin k → ℂ) →L[ℂ] ℂ).analyticAt _).comp
      analyticAt_fst).mul
      (((ContinuousLinearMap.proj r : (Fin k → ℂ) →L[ℂ] ℂ).analyticAt _).comp analyticAt_snd)
  have hk : AnalyticAt ℂ (fun zb : (Fin k → ℂ) × (Fin k → ℂ) =>
      (normalKernelChart k zb.1 zb.2).1) za := by
    simp_rw [normalKernelChart_val]
    exact hs.neg.prod analyticAt_snd
  exact (((analyticAt_fst.comp hv).inv hne).smul (analyticAt_snd.comp hv)).prod
    (analyticAt_snd.comp ((hA _).comp hk))

#print axioms normalKernelCoordinateFormula_analyticAt
/-- The inverse of each actual ambient chart is its specified global parameterization. -/
theorem normalCoordinateKernelChart_symm_apply (k : ℕ) (j : Fin (k + 1))
    (za : (Fin k → ℂ) × (Fin k → ℂ)) :
    (normalCoordinateKernelChart k j).symm za = normalCoordinateKernelParam k j za := by
  exact congr_fun ((isOpenEmbedding_normalCoordinateKernelParam k j).toOpenPartialHomeomorph_apply
    (normalCoordinateKernelParam k j)) za

#print axioms normalCoordinateKernelChart_symm_apply
/-- Every actual kernel chart transition is analytic throughout its specified overlap. -/
theorem normalCoordinateKernelChart_transition_analyticAt (k : ℕ) (i j : Fin (k + 1))
    (za : (Fin k → ℂ) × (Fin k → ℂ))
    (hv : normalCoordinateKernelParam k j za ∈ (normalCoordinateKernelChart k i).source) :
    AnalyticAt ℂ ((normalCoordinateKernelChart k j).symm.trans
      (normalCoordinateKernelChart k i)) za := by
  let A := (normalCoordinatePermutation k (Equiv.swap 0 j)).symm.trans
    (normalCoordinatePermutation k (Equiv.swap 0 i))
  have hA := normalKernelCoordinateFormula_analyticAt k A za
    (normalCoordinateKernelChart_transition_ne_zero k i j za hv)
  apply hA.congr
  have hN := ((normalCoordinateKernelChart k i).open_source.preimage
    (isOpenEmbedding_normalCoordinateKernelParam k j).continuous).mem_nhds hv
  filter_upwards [hN] with zb hzb
  rw [OpenPartialHomeomorph.trans_apply, normalCoordinateKernelChart_symm_apply]
  exact (normalCoordinateKernelChart_transition k i j zb hzb).symm

#print axioms normalCoordinateKernelChart_transition_analyticAt
end HodgeLean.Foundations.Program.G32Native.EulerModel

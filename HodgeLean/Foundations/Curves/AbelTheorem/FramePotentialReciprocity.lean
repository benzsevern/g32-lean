import HodgeLean.Foundations.Curves.AbelTheorem.PotentialMeromorphicRelation
import HodgeLean.Foundations.Curves.AbelTheorem.PotentialDivisorValues

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory Module
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

/-- Source: Farkas–Kra, Riemann Surfaces, III.6, the bilinear calculation for third-kind periods. -/
theorem frame_reciprocity_from_dual_data (h : finrank ℂ E = 1)
    (D : C →₀ ℤ) (hdeg : b4c_deg D = 0) (F : PeriodFrame (E := E) D)
    (w : b4c_MeroForm E C h)
    (hr : ∀ x, b4c_res (hE := h) w x = (D x : ℂ))
    (ho : ∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (hn : ∀ i, loopIntegral (F.a i) w = 0)
    (p : C) (paths : C → ℝ → C) (hp : ∀ x, b3A_IsGoodPath (E := E) (paths x) p x)
    (η : Fin F.genus ⊕ Fin F.genus → C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hη : ∀ s, b3Forms_IsSmooth (η s))
    (hzero : ∀ s x, x ∈ D.support → η s =ᶠ[𝓝 x] 0)
    (hdual : ∀ s, ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ,
      b3Forms_IsSmooth α → b3Forms_d α = 0 →
        b3Forms_integral (b3Rest_b h) (b3Forms_wedgeForm α (η s)) =
          b3Forms_lineIntegral α (Sum.elim F.a F.b s).val 0 1)
    (hpair : ∀ (P : ℂ →L[ℝ] ℝ) s, b3Forms_integral (b4c_residue_basis h)
      (b3Forms_wedgeForm (b4c_residue_realForm h (b4c_residue_normalizedForm h w) P) (η s)) =
        P (loopIntegral (Sum.elim F.a F.b s) w))
    (hint : ∀ s x, x ∈ D.support → ∃ n : ℤ, b3Forms_lineIntegral (η s) (paths x) 0 1 = (n : ℝ)) :
    ∃ ell : b3_periodLattice E C, ∀ i,
      loopIntegral (F.b i) w = (2 * Real.pi * Complex.I) *
        (divisorIntegral (E := E) D paths (F.forms i) + ell.val (F.forms i)) := by
  classical
  obtain ⟨N, hN⟩ := integral_divisor_path_coefficients D paths η hint
  let n : Fin F.genus ⊕ Fin F.genus → ℤ := Sum.elim
    (fun j => N (.inr j)) (fun j => -N (.inl j))
  let ell : b3_periodLattice E C := ∑ s, n s • F.latticeBasis s
  refine ⟨ell, fun i => ?_⟩
  let θ := F.forms i
  let c : Fin F.genus ⊕ Fin F.genus → ℂ := Sum.elim
    (fun j => -loopIntegral (F.b j) θ) (fun j => loopIntegral (F.a j) θ)
  have hcRe (s) : (c s).re = Sum.elim
      (fun j => -b3Forms_lineIntegral (b3Forms_reForm θ) (F.b j).val 0 1)
      (fun j => b3Forms_lineIntegral (b3Forms_reForm θ) (F.a j).val 0 1) s := by
    cases s <;> rename_i j <;>
      simp [c, loopIntegral, b3Forms_pathIntegral_eq θ (F.b j).property.2,
        b3Forms_pathIntegral_eq θ (F.a j).property.2]
  have hcIm (s) : (c s).im = Sum.elim
      (fun j => -b3Forms_lineIntegral (b3Forms_imForm θ) (F.b j).val 0 1)
      (fun j => b3Forms_lineIntegral (b3Forms_imForm θ) (F.a j).val 0 1) s := by
    cases s <;> rename_i j <;>
      simp [c, loopIntegral, b3Forms_pathIntegral_eq θ (F.b j).property.2,
        b3Forms_pathIntegral_eq θ (F.a j).property.2]
  obtain ⟨G, hG, hRe, hIm, hhol⟩ := exists_frame_holomorphic_potential h F η hη hdual hzero θ
  have hRe' : b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).re)) =
      b3Forms_reForm θ + ∑ s, (c s).re • η s := by simpa only [hcRe] using hRe
  have hIm' : b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).im)) =
      b3Forms_imForm θ + ∑ s, (c s).im • η s := by simpa only [hcIm] using hIm
  have hv := potential_meromorphic_relation h D w hr ho ha η hη hzero c θ G hG hRe' hIm' hhol
    (fun s => loopIntegral (Sum.elim F.a F.b s) w) hpair
  rw [potential_divisor_values D hdeg p paths hp η hη c N (hN c) θ G hG hRe' hIm'] at hv
  have hleft : ∑ s, c s * loopIntegral (Sum.elim F.a F.b s) w = loopIntegral (F.b i) w := by
    simp [c, θ, Fintype.sum_sum_type, hn, F.normalized, Finset.sum_ite_eq']
  have hell : ell.val θ = ∑ s, c s * (N s : ℂ) := by
    let ev : b3_periodLattice E C →ₗ[ℤ] ℂ :=
      (LinearMap.proj θ).comp (b3_periodLattice E C).subtype.toIntLinearMap
    have he : ell.val θ = ∑ s, (n s : ℂ) * (F.latticeBasis s).val θ := by
      change ev ell = _
      simp only [ell, map_sum, map_smul, zsmul_eq_mul]
      rfl
    rw [he, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [n, c, Sum.elim_inl, Sum.elim_inr, F.a_basis, F.b_basis, Int.cast_neg]
    change (∑ j, (N (.inr j) : ℂ) * loopIntegral (F.a j) θ) +
      (∑ j, -(N (.inl j) : ℂ) * loopIntegral (F.b j) θ) = _
    rw [add_comm]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [hleft, ← hell] at hv
  exact hv

end HodgeLean.Foundations.Curves.AbelTheorem

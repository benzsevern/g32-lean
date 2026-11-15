import HodgeLean.Foundations.Curves.AbelTheorem.Defs
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.MeromorphicTrace
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.FiberPeriodReduction

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Manifold Filter Topology
open scoped ContDiff BigOperators TensorProduct
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
theorem principalVanishing
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
    [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (p : C)
    (f : b4c_MeroFun E C) (hf : ∃ x, f x ≠ (0 : ℂ)) :
    weightedSum (analyticAbel h p) (b4c_div E f) = 0 := by
  classical
  by_cases hnc : ∃ x y, f x ≠ f y
  · letI := b3_periodLattice_finite (E := E) (C := C) h
    letI := b3_periodLattice_free (E := E) (C := C)
    letI := b2_latticeMap_discrete (Λ := b3_periodLattice E C) (b3_periodF E C)
      (b3_isWeightOne (E := E) (C := C) h)
    have ha := b3_abelJacobi_holomorphic (E := E) (C := C) h p
      (analyticAbel (E := E) (C := C) h p)
      (b3_exists_abelJacobi (E := E) (C := C) h p).choose_spec
    exact meromorphic_divisor_sum_zero_of_fiber_holomorphic h f hnc
      (b3_periodLattice E C) (b3_periodF E C) (b3_isWeightOne (E := E) (C := C) h)
      (analyticAbel (E := E) (C := C) h p)
      (meromorphicFiberSum_contMDiff h f hnc (b3_periodF E C)
        (analyticAbel (E := E) (C := C) h p) ha)
  · have hc : ∀ x y, f x = f y := by
      push_neg at hnc
      exact hnc
    rw [meromorphic_divisor_eq_zero_of_constant f hf hc, map_zero]


variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem integral_lattice_of_abel_sum_zero (h : Module.finrank ℂ E = 1) (p : C)
    (D : C →₀ ℤ) (paths : C → ℝ → C)
    (hp : ∀ x, b3A_IsGoodPath (E := E) (paths x) p x)
    (hz : weightedSum (analyticAbel h p) D = 0) :
    ∃ ell : b3_periodLattice E C,
      ∀ θ : b3_HolForm E C, divisorIntegral (E := E) D paths θ = ell.val θ := by
  classical
  have haj := (b3_exists_abelJacobi (E := E) (C := C) h p).choose_spec
  choose v hv hj using fun x => haj.2 (paths x) (hp x).1
  have hj' (x : C) : b3A_jacMk (v x) = analyticAbel h p x := by
    have hx := hj x
    rw [(hp x).apply_one, (hp x).apply_zero, haj.1, sub_zero] at hx
    exact hx.symm
  let u := weightedSum v D
  have hu : b3A_jacMk u = 0 := by
    change b3A_jacMk (D.sum fun x n => n • v x) = 0
    rw [map_finsuppSum]
    simp only [map_zsmul, hj']
    exact hz
  obtain ⟨ell, hell⟩ := (QuotientAddGroup.eq_zero_iff _).mp hu
  have heq : (Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℤ] ell) :
      (ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) =
      Submodule.Quotient.mk u := hell
  have hker := (Submodule.Quotient.eq (b3_periodF E C)).mp heq
  change b3_cplxPeriod E C ((1 : ℂ) ⊗ₜ[ℤ] ell - u) = 0 at hker
  have huper : b3_cplxPeriod E C u = ell.val := by
    rw [map_sub] at hker
    change (1 : ℂ) • ell.val - b3_cplxPeriod E C u = 0 at hker
    simpa only [one_smul] using (sub_eq_zero.mp hker).symm
  refine ⟨ell, fun θ => ?_⟩
  rw [← huper]
  change D.sum (fun x n => (n : ℂ) * b3_pathIntegral E C (paths x) θ) =
    b3_cplxPeriod E C (D.sum fun x n => n • v x) θ
  rw [map_finsuppSum]
  simp only [map_zsmul, hv, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
    zsmul_eq_mul]
  rfl

end HodgeLean.Foundations.Curves.AbelTheorem

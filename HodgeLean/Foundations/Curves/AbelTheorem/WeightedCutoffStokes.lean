import HodgeLean.Foundations.Curves.AbelTheorem.IntegrationByParts

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap MeasureTheory
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem weighted_cutoff_stokes (h : Module.finrank ℂ E = 1) (w : b4c_MeroForm E C h)
    (s : Finset C) (χ ψ : C → C → ℝ)
    (hχ : ∀ i ∈ s, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (χ i))
    (hψ : ∀ i ∈ s, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (ψ i))
    (hchart : ∀ i ∈ s, tsupport (χ i) ⊆ (chartAt E i).source)
    (hd : (s : Set C).PairwiseDisjoint (fun i => tsupport (χ i)))
    (hone : ∀ i ∈ s, ∀ x ∈ tsupport (ψ i), χ i x = 1)
    (hpoles : ∀ x, meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0 < 0 →
      (fun y => 1 - ∑ i ∈ s, ψ i y) =ᶠ[𝓝 x] 0)
    (g : C → ℝ) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (c : C → ℝ)
    (hc : ∀ i ∈ s, ∀ x ∈ tsupport (χ i), g x = c i) (P : ℂ →L[ℝ] ℝ) :
    let α := b4c_residue_realForm h (fun v =>
      ((1 - ∑ i ∈ s, ψ i v.proj : ℝ) : ℂ) * b4c_residue_normalizedForm h w v) P
    b3Forms_integral (b4c_residue_basis h)
      (b3Forms_wedgeForm (b3Forms_d (b3Forms_fun (E := E) g)) α) =
      -∑ i ∈ s, c i * b3Forms_chartIntegral (b4c_residue_basis h) i
        (b3Forms_smulFun (χ i) (b3Forms_d α)) := by
  classical
  dsimp only
  let μ : C → ℝ := fun y => 1 - ∑ i ∈ s, ψ i y
  let α := b4c_residue_realForm h
    (fun v => (μ v.proj : ℂ) * b4c_residue_normalizedForm h w v) P
  have hμ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ μ :=
    contMDiff_const.sub (ContMDiff.sum hψ)
  have hα : b3Forms_IsSmooth α := b4c_residue_smooth_global h w μ hμ hpoles P
  rw [integral_d_wedge_eq_neg_smul_d h g hg α hα]
  congr 1
  rw [b4c_residue_integral_localize h s χ hχ hchart _ (hα.d.smulFun hg)]
  · apply Finset.sum_congr rfl
    intro i hi
    have he : b3Forms_smulFun (χ i) (b3Forms_smulFun g (b3Forms_d α)) =
        c i • b3Forms_smulFun (χ i) (b3Forms_d α) := by
      funext x
      by_cases hx : χ i x = 0
      · simp only [b3Forms_smulFun, hx, zero_smul, Pi.smul_apply, smul_zero]
      · simp only [b3Forms_smulFun, Pi.smul_apply, hc i hi x (subset_tsupport _ hx)]
        exact smul_comm _ _ _
    rw [he, b3Forms_chartIntegral_smul]
  · intro x hx
    have hx' : b3Forms_d α x ≠ 0 := by
      intro hz
      exact hx (by simp only [b3Forms_smulFun, hz, smul_zero])
    exact b4c_residue_cutoff_partition s χ ψ hd hone
      (b4c_residue_d_support h w s ψ hψ hpoles P hx')

end HodgeLean.Foundations.Curves.AbelTheorem

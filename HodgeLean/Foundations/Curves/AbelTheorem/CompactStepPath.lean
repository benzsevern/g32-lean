import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem step_path_range_eq_interval_image (δ : ℝ → C) :
    Set.range (δ ∘ b3A_step) = (δ ∘ b3A_step) '' Icc (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    by_cases ht : t < 0
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      have hzero : b3A_step t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
      exact congrArg δ ((show b3A_step 0 = 0 from
        Real.smoothTransition.zero_of_nonpos (by norm_num)).trans hzero.symm)
    · by_cases ht' : 1 < t
      · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
        have hone : b3A_step t = 1 := Real.smoothTransition.one_of_one_le (by linarith)
        exact congrArg δ ((show b3A_step 1 = 1 from
          Real.smoothTransition.one_of_one_le (by norm_num)).trans hone.symm)
      · exact ⟨t, ⟨not_lt.mp ht, not_lt.mp ht'⟩, rfl⟩
  · rintro ⟨t, _, rfl⟩
    exact ⟨t, rfl⟩

end HodgeLean.Foundations.Curves.AbelTheorem

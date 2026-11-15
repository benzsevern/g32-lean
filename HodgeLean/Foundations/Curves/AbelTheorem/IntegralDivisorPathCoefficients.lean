import HodgeLean.Foundations.Curves.AbelTheorem.ComplexPotentialPath

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

/-- Source: Farkas–Kra, Riemann Surfaces, III.6, integer intersections with divisor paths. -/
theorem integral_divisor_path_coefficients (D : C →₀ ℤ) (paths : C → ℝ → C)
    {ι : Type} [Fintype ι] (η : ι → C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hint : ∀ s x, x ∈ D.support → ∃ n : ℤ, b3Forms_lineIntegral (η s) (paths x) 0 1 = (n : ℝ)) :
    ∃ N : ι → ℤ, ∀ c : ι → ℂ,
      ∑ x ∈ D.support, (D x : ℂ) * ∑ s, c s * (b3Forms_lineIntegral (η s) (paths x) 0 1 : ℂ) =
        ∑ s, c s * (N s : ℂ) := by
  classical
  have hm : ∀ s x, ∃ n : ℤ, x ∈ D.support → b3Forms_lineIntegral (η s) (paths x) 0 1 = (n : ℝ) := by
    intro s x
    by_cases hx : x ∈ D.support
    · obtain ⟨n, hn⟩ := hint s x hx
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun hs => False.elim (hx hs)⟩
  choose m hm using hm
  refine ⟨fun s => ∑ x ∈ D.support, D x * m s x, fun c => ?_⟩
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hm s x hx]
  push_cast
  ring

end HodgeLean.Foundations.Curves.AbelTheorem

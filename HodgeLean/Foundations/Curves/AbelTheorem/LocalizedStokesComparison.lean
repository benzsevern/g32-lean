import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem integral_eq_neg_local_derivatives (h : Module.finrank ℂ E = 1)
    (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) (hα : b3Forms_IsSmooth α)
    (β : C → E [⋀^Fin 2]→L[ℝ] ℝ) (hβ : b3Forms_IsSmooth β)
    (s : Finset C) (χ : C → C → ℝ)
    (hχ : ∀ i ∈ s, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (χ i))
    (hchart : ∀ i ∈ s, tsupport (χ i) ⊆ (chartAt E i).source)
    (hpart : ∀ x, (b3Forms_d α - β) x ≠ 0 → ∑ i ∈ s, χ i x = 1)
    (hz : ∀ i ∈ s, ∀ x ∈ tsupport (χ i), β x = 0) :
    b3Forms_integral (b4c_residue_basis h) β =
      -∑ i ∈ s, b3Forms_chartIntegral (b4c_residue_basis h) i
        (b3Forms_smulFun (χ i) (b3Forms_d α)) := by
  classical
  have hδ : b3Forms_IsSmooth (b3Forms_d α - β) := by
    rw [sub_eq_add_neg, show -β = (-1 : ℝ) • β from (neg_one_smul ℝ β).symm]
    exact hα.d.add (hβ.smul (-1))
  have hs := b3Forms_integral_d_eq_zero b3Forms_oriented_complex (b4c_residue_basis h) hα
  have he : b3Forms_d α = β + (b3Forms_d α - β) := by abel
  rw [he, b3Forms_integral_add _ hβ hδ,
    b4c_residue_integral_localize h s χ hχ hchart _ hδ hpart] at hs
  have hterms : ∑ i ∈ s, b3Forms_chartIntegral (b4c_residue_basis h) i
      (b3Forms_smulFun (χ i) (b3Forms_d α - β)) =
      ∑ i ∈ s, b3Forms_chartIntegral (b4c_residue_basis h) i
        (b3Forms_smulFun (χ i) (b3Forms_d α)) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    funext x
    by_cases hx : χ i x = 0
    · simp only [b3Forms_smulFun, hx, zero_smul]
    · simp only [b3Forms_smulFun, Pi.sub_apply, hz i hi x (subset_tsupport _ hx), sub_zero]
  rw [hterms] at hs
  linarith

end HodgeLean.Foundations.Curves.AbelTheorem

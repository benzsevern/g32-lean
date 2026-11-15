import HodgeLean.Foundations.Curves.AbelTheorem.IntegralDivisorPathCoefficients

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

/-- Source: Farkas–Kra, Riemann Surfaces, III.6, the divisor-weighted primitive calculation. -/
theorem potential_divisor_values (D : C →₀ ℤ) (hdeg : b4c_deg D = 0)
    (p : C) (paths : C → ℝ → C) (hp : ∀ x, b3A_IsGoodPath (E := E) (paths x) p x)
    {ι : Type} [Fintype ι] (η : ι → C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hη : ∀ s, b3Forms_IsSmooth (η s)) (c : ι → ℂ) (N : ι → ℤ)
    (hN : ∑ x ∈ D.support, (D x : ℂ) * ∑ s, c s * (b3Forms_lineIntegral (η s) (paths x) 0 1 : ℂ) =
      ∑ s, c s * (N s : ℂ))
    (θ : b3_HolForm E C) (G : C → ℂ)
    (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G)
    (hre : b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).re)) =
      b3Forms_reForm θ + ∑ s, (c s).re • η s)
    (him : b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).im)) =
      b3Forms_imForm θ + ∑ s, (c s).im • η s) :
    ∑ x ∈ D.support, (D x : ℂ) * G x =
      divisorIntegral (E := E) D paths θ + ∑ s, c s * (N s : ℂ) := by
  classical
  have hsum : ∑ x ∈ D.support, (D x : ℂ) = 0 := by
    change ∑ x ∈ D.support, D x = 0 at hdeg
    exact_mod_cast hdeg
  calc
    ∑ x ∈ D.support, (D x : ℂ) * G x =
        ∑ x ∈ D.support, (D x : ℂ) * (G x - G p) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, zero_mul, sub_zero]
    _ = ∑ x ∈ D.support, (D x : ℂ) * (b3_pathIntegral E C (paths x) θ.val +
        ∑ s, c s * (b3Forms_lineIntegral (η s) (paths x) 0 1 : ℂ)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [complex_potential_path_increment η hη c θ G hG hre him p x (paths x) (hp x)]
    _ = divisorIntegral (E := E) D paths θ + ∑ s, c s * (N s : ℂ) := by
      simp only [mul_add, Finset.sum_add_distrib, hN]
      rfl

end HodgeLean.Foundations.Curves.AbelTheorem

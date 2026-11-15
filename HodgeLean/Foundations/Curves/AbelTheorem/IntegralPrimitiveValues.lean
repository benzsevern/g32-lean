import HodgeLean.Foundations.Curves.AbelTheorem.Defs

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

theorem integral_divisor_values_of_primitive (D : C →₀ ℤ) (hdeg : b4c_deg D = 0)
    (p : C) (paths : C → ℝ → C)
    (hp : ∀ x, b3A_IsGoodPath (E := E) (paths x) p x)
    {ι : Type} [Fintype ι] (η : ι → C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hη : ∀ i, b3Forms_IsSmooth (η i)) (n : ι → ℤ)
    (hint : ∀ i x, x ∈ D.support → ∃ m : ℤ,
      b3Forms_lineIntegral (η i) (paths x) 0 1 = (m : ℝ))
    (f : C → ℝ) (hf : b3Forms_IsSmooth (b3Forms_fun (E := E) f))
    (hdf : b3Forms_d (b3Forms_fun (E := E) f) = ∑ i, (n i : ℝ) • η i) :
    ∃ N : ℤ, ∑ x ∈ D.support, (D x : ℝ) * f x = (N : ℝ) := by
  classical
  have hvalues : ∀ x, ∃ m : ℤ, x ∈ D.support → f x - f p = (m : ℝ) := by
    intro x
    by_cases hx : x ∈ D.support
    · choose m hm using fun i => hint i x hx
      refine ⟨∑ i, n i * m i, fun _ => ?_⟩
      have he := b3Forms_lineIntegral_d hf (hp x).1 0 1
      rw [(hp x).apply_zero, (hp x).apply_one, hdf,
        b3Rest2_lineIntegral_sum _ (fun i _ => (hη i).smul _) (hp x).1] at he
      simpa only [b3Forms_lineIntegral_smul, hm, Int.cast_sum, Int.cast_mul] using he.symm
    · exact ⟨0, fun hs => False.elim (hx hs)⟩
  choose m hm using hvalues
  refine ⟨∑ x ∈ D.support, D x * m x, ?_⟩
  have hsum : ∑ x ∈ D.support, (D x : ℝ) = 0 := by
    change ∑ x ∈ D.support, D x = 0 at hdeg
    exact_mod_cast hdeg
  have he : ∑ x ∈ D.support, (D x : ℝ) * f x =
      ∑ x ∈ D.support, (D x : ℝ) * (f p + (m x : ℝ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [show f x = f p + (m x : ℝ) by linarith [hm x hx]]
  rw [he]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul,
    zero_add, Int.cast_sum, Int.cast_mul]

end HodgeLean.Foundations.Curves.AbelTheorem

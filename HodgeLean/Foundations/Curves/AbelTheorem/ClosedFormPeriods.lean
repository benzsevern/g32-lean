import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem closed_form_period_eq_of_holomorphic_period_eq (h : Module.finrank ℂ E = 1)
    (γ δ : b3_SmoothLoop E C) (hper : b3_period E C γ = b3_period E C δ)
    (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) (hα : b3Forms_IsSmooth α) (hd : b3Forms_d α = 0) :
    b3Forms_lineIntegral α γ.val 0 1 = b3Forms_lineIntegral α δ.val 0 1 := by
  letI : IsManifold 𝓘(ℝ, E) ∞ C := b3Forms_isManifold_real
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : Fact (Module.finrank ℂ E = 1) := ⟨h⟩
  obtain ⟨θ, f, hf, he⟩ := b3Rest_hodge hα hd
  have heval (ξ : b3_SmoothLoop E C) :
      b3Forms_lineIntegral α ξ.val 0 1 = (b3_period E C ξ θ).re := by
    have hend : ξ.val 1 = ξ.val 0 := by simpa only [zero_add] using ξ.property.1 0
    rw [he, b3Forms_lineIntegral_add (b3Forms_isSmooth_reForm θ) hf.d ξ.property.2,
      b3Forms_lineIntegral_d hf ξ.property.2, hend, sub_self, add_zero,
      ← b3Rest2_re_period]
  rw [heval γ, heval δ, hper]

end HodgeLean.Foundations.Curves.AbelTheorem

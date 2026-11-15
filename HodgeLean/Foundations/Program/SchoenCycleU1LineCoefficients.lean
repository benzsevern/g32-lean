import HodgeLean.Foundations.Program.SchoenCycleCanonicalFamily

/-! # Linearity of the actual differential line coefficient -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The actual native differential coefficient preserves the linear parameter
family, in precisely the scalar normalization used for its divisor orders.
Source: HodgeLean, `s2e_holomorphicCoefficientFamily_eq_loc`. -/
theorem s2e_u1_holomorphic_line_coefficient
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (hE : Module.finrank ℂ E = 1) (θ δ : b3_HolForm E C) (p : C) (t : ℂ) :
    HurwitzPrymRR_loc hE (θ + t • δ) p =
      (fun z => HurwitzPrymRR_loc hE θ p z + t * HurwitzPrymRR_loc hE δ p z) := by
  funext z
  have hh := (s2e_holomorphicCoefficientFamily_eq_loc hE ![θ, δ] p (![1, t], z)).symm
  simpa only [s2e_holomorphicCoefficientFamily, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, one_mul] using hh

end HodgeLean.Foundations.Program

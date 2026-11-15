import HodgeLean.Foundations.Program.SchoenTransferJ12PeriodPullback
import HodgeLean.Foundations.Program.HurwitzPrymCovInvariant

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- A nonconstant map of compact curves has injective pullback in their specified complex line models. -/
theorem s4_selected_curve_pullback_injective
    {E F C Y : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace F Y] [IsManifold 𝓘(ℂ, F) ω Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (hE : Module.finrank ℂ E = 1) (hF : Module.finrank ℂ F = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hnc : ∃ x x', f x ≠ f x') :
    Function.Injective (cohomologyMap ℚ 1 (TopCat.ofHom ⟨f, hf.continuous⟩)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have ht0 : b3Rest2_T (C := C) hE 0 = 0 := by
    have h := b3Rest2_T_smul (C := C) hE 0 0
    simpa only [zero_smul, Rat.cast_zero] using h
  have ht := s4_selected_period_pullback hE hF f hf a
  rw [ha, ht0] at ht
  apply b3Rest2_eq_zero_of_T hF
  apply Subtype.ext
  exact b4cov_pullback_injective hE hF
    f hf hnc _ (b3Rest2_T hF a).property
    (congrArg Subtype.val ht.symm)


#print axioms s4_selected_curve_pullback_injective

end HodgeLean.Foundations.Program

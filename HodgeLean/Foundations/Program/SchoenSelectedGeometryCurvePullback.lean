import HodgeLean.Foundations.Program.SchoenSelectedGeometryPeriodNaturality
import HodgeLean.Foundations.Program.HurwitzPrymCovInvariant

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- A nonconstant holomorphic map of compact curves has injective rational degree-one pullback. -/
theorem s0_curve_pullback_injective
    {C Y : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hnc : ∃ x x', f x ≠ f x') :
    Function.Injective (cohomologyMap ℚ 1 (TopCat.ofHom ⟨f, hf.continuous⟩)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have ht0 : b3Rest2_T (C := C) (Module.finrank_self ℂ) 0 = 0 := by
    have h := b3Rest2_T_smul (C := C) (Module.finrank_self ℂ) 0 0
    simpa only [zero_smul, Rat.cast_zero] using h
  have ht := s0_period_form_pullback f hf a
  rw [ha, ht0] at ht
  apply b3Rest2_eq_zero_of_T (Module.finrank_self ℂ)
  apply Subtype.ext
  exact b4cov_pullback_injective (Module.finrank_self ℂ) (Module.finrank_self ℂ)
    f hf hnc _ (b3Rest2_T (Module.finrank_self ℂ) a).property
    (congrArg Subtype.val ht.symm)

#print axioms s0_curve_pullback_injective
end HodgeLean.Foundations.Program

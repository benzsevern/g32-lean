import HodgeLean.Foundations.Program.SchoenSelectedGeometryPeriodCharacter
import HodgeLean.Foundations.Program.SchoenSelectedGeometryPeriodNaturality

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Rational period characters pull back by precomposition with lattice pushforward. -/
theorem s0_periodCharacter_pullback
    {C Y : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (a : Cohomology ℚ (TopCat.of Y) 1) :
    s0_periodCharacter C (cohomologyMap ℚ 1 (TopCat.ofHom ⟨f, hf.continuous⟩) a) =
      (s0_periodCharacter Y a).comp (b3A_push f hf) := by
  ext l
  apply Rat.cast_injective (α := ℝ)
  change ((s0_periodCharacter C _ l : ℚ) : ℝ) =
    ((s0_periodCharacter Y a (b3A_push f hf l) : ℚ) : ℝ)
  rw [s0_periodCharacter_spec, s0_periodCharacter_spec, s0_period_form_pullback]
  rfl

#print axioms s0_periodCharacter_pullback
end HodgeLean.Foundations.Program

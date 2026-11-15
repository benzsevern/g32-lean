import HodgeLean.Foundations.Program.SchoenSelectedGeometryPeriodEquivalence
import HodgeLean.Foundations.Program.SchoenSelectedGeometryCharacterNaturality
import HodgeLean.Foundations.Program.SchoenSelectedGeometryCharacterDescent

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Descent of the representing holomorphic form implies descent of the rational class. -/
theorem s0_class_descends_of_period_form
    {C Y : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (a : Cohomology ℚ (TopCat.of C) 1) (θ : b3_HolForm ℂ Y)
    (hθ : b3Rest2_T (Module.finrank_self ℂ) a = b3A_pullHol f hf θ) :
    a ∈ LinearMap.range (cohomologyMap ℚ 1 (TopCat.ofHom ⟨f, hf.continuous⟩)) := by
  have hk : ∀ l, b3A_push f hf l = 0 → s0_periodCharacter C a l = 0 := by
    intro l hl
    apply Rat.cast_injective (α := ℝ)
    rw [s0_periodCharacter_spec, hθ, Rat.cast_zero]
    change (b3Rest2_s : ℝ) * ((b3A_push f hf l).1 θ).re = (0 : ℝ)
    rw [hl]
    simp
  obtain ⟨b, hb⟩ := s0_rational_character_descends (b3A_push f hf) (s0_periodCharacter C a) hk
  obtain ⟨β, hβ⟩ := (s0_periodCharacter_bijective Y).surjective b
  refine ⟨β, s0_periodCharacter_injective C ?_⟩
  rw [s0_periodCharacter_pullback f hf, hβ, hb]

#print axioms s0_class_descends_of_period_form
end HodgeLean.Foundations.Program

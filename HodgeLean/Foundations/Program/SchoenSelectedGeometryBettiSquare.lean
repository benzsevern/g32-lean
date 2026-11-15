import HodgeLean.Foundations.Singular.Circle

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

/-- A commuting homeomorphism square transports rational pullback bijectivity. -/
theorem s0_pullback_bijective_of_homeomorph_square
    {X Y X' Y' : TopCat} (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (n : ℕ)
    (hs : TopCat.ofHom ⟨eX, eX.continuous⟩ ≫ g =
      f ≫ TopCat.ofHom ⟨eY, eY.continuous⟩)
    (hf : Function.Bijective (cohomologyMap ℚ n f)) :
    Function.Bijective (cohomologyMap ℚ n g) := by
  have hx : Function.Bijective (cohomologyMap ℚ n (TopCat.ofHom ⟨eX, eX.continuous⟩)) :=
    (cohomologyHomeomorphEquiv eX n).symm.bijective
  have hy : Function.Bijective (cohomologyMap ℚ n (TopCat.ofHom ⟨eY, eY.continuous⟩)) :=
    (cohomologyHomeomorphEquiv eY n).symm.bijective
  have hb : Function.Bijective ((cohomologyMap ℚ n f).comp
      (cohomologyMap ℚ n (TopCat.ofHom ⟨eY, eY.continuous⟩))) := hf.comp hy
  rw [← cohomologyMap_comp, ← hs, cohomologyMap_comp] at hb
  change Function.Bijective ((cohomologyMap ℚ n (TopCat.ofHom ⟨eX, eX.continuous⟩)) ∘
    (cohomologyMap ℚ n g)) at hb
  exact hb.of_comp_left hx.injective

#print axioms s0_pullback_bijective_of_homeomorph_square
end HodgeLean.Foundations.Program

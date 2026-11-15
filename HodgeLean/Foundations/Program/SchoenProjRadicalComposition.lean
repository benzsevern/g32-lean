import HodgeLean.Foundations.Program.SchoenHomogeneousStalkComposition
import HodgeLean.Foundations.Program.SchoenProjRadicalMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization CategoryTheory
namespace HodgeLean.Foundations.Program
namespace S2RadicalProj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The point maps of actual radical-controlled Proj morphisms respect composition. -/
theorem map_comp_base {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) (𝒞 : ℕ → AddSubgroup C)
    [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f.toRingHom).radical)
    (hg : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      ((HomogeneousIdeal.irrelevant ℬ).toIdeal.map g.toRingHom).radical)
    (hfg : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.comp f).toRingHom).radical) :
    (map 𝒜 𝒞 (g.comp f) hfg).base = (map ℬ 𝒞 g hg ≫ map 𝒜 ℬ f hf).base := by
  ext p
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual radical-controlled Proj scheme morphisms respect composition. -/
theorem map_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) (𝒞 : ℕ → AddSubgroup C)
    [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f.toRingHom).radical)
    (hg : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      ((HomogeneousIdeal.irrelevant ℬ).toIdeal.map g.toRingHom).radical)
    (hfg : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.comp f).toRingHom).radical) :
    map 𝒜 𝒞 (g.comp f) hfg = map ℬ 𝒞 g hg ≫ map 𝒜 ℬ f hf := by
  apply Scheme.Hom.ext (map_comp_base 𝒜 ℬ 𝒞 f g hf hg hfg)
  intro U
  simp only [eqToHom_refl, Functor.map_id, Category.comp_id]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply Subtype.ext
  funext p
  change HomogeneousLocalization.map (g.comp f) _ _ =
    HomogeneousLocalization.map g _ (HomogeneousLocalization.map f _ _)
  exact (HomogeneousLocalization.map_map _ _ _).symm

end S2RadicalProj
end HodgeLean.Foundations.Program

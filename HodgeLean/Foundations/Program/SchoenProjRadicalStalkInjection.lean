import HodgeLean.Foundations.Program.SchoenProjRadicalMap
import HodgeLean.Foundations.Program.SchoenHomogeneousLocalizationMaps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization CategoryTheory
namespace HodgeLean.Foundations.Program

/-- An injective graded map into a domain stays injective on homogeneous prime localizations. -/
theorem s2_homogeneousLocalRingHom_injective {A B : Type} [CommRing A] [CommRing B]
    [IsDomain B] (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B)
    [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Injective f)
    (P : Ideal B) [P.IsPrime] :
    Function.Injective (localRingHom f (P.comap f) P rfl) := by
  exact s2_homogeneousLocalization_map_injective 𝒜 ℬ f _ _ _ (by simp) hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An injective graded map into a domain induces injective stalk pullbacks on actual Proj schemes. -/
theorem s2_projRadicalMap_stalkMap_injective {A B : Type} [CommRing A] [CommRing B]
    [IsDomain B] (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B)
    [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f.toRingHom).radical)
    (hinj : Function.Injective f) (p : Proj ℬ) :
    Function.Injective ((S2RadicalProj.map 𝒜 ℬ f hf).stalkMap p) := by
  have hcomp : Function.Injective
      ((S2RadicalProj.map 𝒜 ℬ f hf).stalkMap p ≫ (Proj.stalkIso ℬ p).hom) := by
    change Function.Injective
      ((S2RadicalProj.sheafedSpaceMap 𝒜 ℬ f hf).hom.stalkMap p ≫ (Proj.stalkIso ℬ p).hom)
    rw [S2RadicalProj.stalkMap_comp_stalkIso]
    exact (s2_homogeneousLocalRingHom_injective 𝒜 ℬ f hinj p.asHomogeneousIdeal.toIdeal).comp
      (Proj.stalkIso 𝒜 (s2_projRadicalComap 𝒜 ℬ f hf p)).commRingCatIsoToRingEquiv.injective
  intro a b hab
  apply hcomp
  exact congrArg (Proj.stalkIso ℬ p).hom hab

end HodgeLean.Foundations.Program

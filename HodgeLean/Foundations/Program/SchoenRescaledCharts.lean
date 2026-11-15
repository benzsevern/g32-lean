import HodgeLean.Foundations.Program.SchoenRescaledSchemeIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization CategoryTheory
namespace HodgeLean.Foundations.Program
namespace S2RescaledProj

variable {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    [GradedRing (fun n => 𝒜 (D * n))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rescaled chart sections pull back by the actual homogeneous fraction comparison. -/
theorem awayToSection_comp_appLE (f : A) :
    Proj.awayToSection (fun n => 𝒜 (D * n)) f ≫
      (map 𝒜 D hD).appLE (Proj.basicOpen (fun n => 𝒜 (D * n)) f)
        (Proj.basicOpen 𝒜 f) (by rfl) =
    CommRingCat.ofHom (s2_rescaledLocalizationHom 𝒜 D (Submonoid.powers f)) ≫
      Proj.awayToSection 𝒜 f := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  apply Subtype.ext
  funext p
  apply HomogeneousLocalization.val_injective
  change (s2_rescaledLocalizationFun 𝒜 D _
    (HomogeneousLocalization.mapId (fun n => 𝒜 (D * n)) _ (.mk c))).val = _
  rw [s2_rescaledLocalizationFun_val]
  change (HomogeneousLocalization.mapId (fun n => 𝒜 (D * n)) _ (.mk c)).val =
    (HomogeneousLocalization.mapId 𝒜 _
      (s2_rescaledLocalizationHom 𝒜 D (Submonoid.powers f) (.mk c))).val
  rw [s2_rescaledLocalizationHom_mk]
  rfl

/-- Rescaling preserves the actual degree-zero coefficient fractions. -/
theorem localizationHom_fromZeroRingHom (M : Submonoid A) :
    (s2_rescaledLocalizationHom 𝒜 D M).comp
      (fromZeroRingHom (fun n => 𝒜 (D * n)) M) = fromZeroRingHom 𝒜 M := by
  apply RingHom.ext
  intro a
  apply HomogeneousLocalization.val_injective
  change (s2_rescaledLocalizationFun 𝒜 D M _).val = _
  rw [s2_rescaledLocalizationFun_val]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual rescaling morphism has the expected spectrum map on every basic chart. -/
theorem resLE_comp_basicOpenToSpec (f : A) :
    (map 𝒜 D hD).resLE (Proj.basicOpen (fun n => 𝒜 (D * n)) f)
      (Proj.basicOpen 𝒜 f) (by rfl) ≫
        Proj.basicOpenToSpec (fun n => 𝒜 (D * n)) f =
    Proj.basicOpenToSpec 𝒜 f ≫
      Spec.map (CommRingCat.ofHom (s2_rescaledLocalizationHom 𝒜 D (Submonoid.powers f))) := by
  simp only [Proj.basicOpenToSpec, ← Category.assoc]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE]
  simp only [Category.assoc, ← Spec.map_comp]
  rw [awayToSection_comp_appLE]

end S2RescaledProj
end HodgeLean.Foundations.Program

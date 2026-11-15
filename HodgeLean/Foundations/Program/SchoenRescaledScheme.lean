import HodgeLean.Foundations.Program.SchoenRescaledSheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization TopologicalSpace CategoryTheory
namespace HodgeLean.Foundations.Program
namespace S2RescaledProj

variable {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    [GradedRing (fun n => 𝒜 (D * n))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The Proj rescaling homeomorphism with its actual structure sheaf pullback. -/
def sheafedSpaceMap : Proj.toSheafedSpace 𝒜 ⟶
    Proj.toSheafedSpace (fun n => 𝒜 (D * n)) where
  hom :=
    { base := TopCat.ofHom
        ⟨s2_rescaledProjHomeomorph 𝒜 D hD, (s2_rescaledProjHomeomorph 𝒜 D hD).continuous⟩
      c := { app U := CommRingCat.ofHom (sheafPullback 𝒜 D hD _ _ Set.Subset.rfl) } }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The rescaling sheaf map induces the actual fraction comparison on every stalk. -/
theorem stalkMap_comp_stalkIso (p : ProjectiveSpectrum 𝒜) :
    (sheafedSpaceMap 𝒜 D hD).hom.stalkMap p ≫ (Proj.stalkIso 𝒜 p).hom =
      (Proj.stalkIso (fun n => 𝒜 (D * n)) (s2_rescaledProjHomeomorph 𝒜 D hD p)).hom ≫
        CommRingCat.ofHom (s2_rescaledLocalizationHom 𝒜 D
          p.asHomogeneousIdeal.toIdeal.primeCompl) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨W, hpW, s, rfl⟩ :=
    (Proj (fun n => 𝒜 (D * n))).presheaf.exists_germ_eq z
  change (Proj.stalkIso' 𝒜 p)
      ((sheafedSpaceMap 𝒜 D hD).hom.stalkMap p
        ((Proj (fun n => 𝒜 (D * n))).presheaf.germ W _ hpW s)) =
    s2_rescaledLocalizationHom 𝒜 D _
      ((Proj.stalkIso' (fun n => 𝒜 (D * n)) (s2_rescaledProjHomeomorph 𝒜 D hD p))
        ((Proj (fun n => 𝒜 (D * n))).presheaf.germ W _ hpW s))
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [Proj.stalkIso'_germ, Proj.stalkIso'_germ]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Positive degree rescaling induces an actual morphism of Proj schemes. -/
def map : Proj 𝒜 ⟶ Proj (fun n => 𝒜 (D * n)) where
  __ := (sheafedSpaceMap 𝒜 D hD).hom
  prop p := .mk fun x hx => by
    have hx' := hx.map (Proj.stalkIso 𝒜 p).hom.hom
    change IsUnit (((sheafedSpaceMap 𝒜 D hD).hom.stalkMap p ≫
      (Proj.stalkIso 𝒜 p).hom).hom x) at hx'
    rw [stalkMap_comp_stalkIso] at hx'
    let e := s2_rescaledLocalizationEquiv 𝒜 D
      p.asHomogeneousIdeal.toIdeal.primeCompl
      (show (0 : A) ∉ p.asHomogeneousIdeal.toIdeal.primeCompl from
        fun h => h (Ideal.zero_mem _))
    have he : IsUnit ((Proj.stalkIso (fun n => 𝒜 (D * n))
        (s2_rescaledProjHomeomorph 𝒜 D hD p)).hom x) :=
      by
        have hu := hx'.map e.symm.toRingHom
        change IsUnit (e.symm (e _)) at hu
        rw [RingEquiv.symm_apply_apply] at hu
        exact hu
    haveI : IsLocalHom (Proj.stalkIso (fun n => 𝒜 (D * n))
        (s2_rescaledProjHomeomorph 𝒜 D hD p)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every stalk map of the actual rescaling morphism is an isomorphism. -/
theorem map_stalkMap_isIso (p : ProjectiveSpectrum 𝒜) :
    IsIso ((map 𝒜 D hD).stalkMap p) := by
  let e := s2_rescaledLocalizationEquiv 𝒜 D
    p.asHomogeneousIdeal.toIdeal.primeCompl
    (show (0 : A) ∉ p.asHomogeneousIdeal.toIdeal.primeCompl from
      fun h => h (Ideal.zero_mem _))
  have he : IsIso (CommRingCat.ofHom (s2_rescaledLocalizationHom 𝒜 D
      p.asHomogeneousIdeal.toIdeal.primeCompl)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr e.bijective
  have hcomp : IsIso ((map 𝒜 D hD).stalkMap p ≫ (Proj.stalkIso 𝒜 p).hom) := by
    change IsIso ((sheafedSpaceMap 𝒜 D hD).hom.stalkMap p ≫ _)
    rw [stalkMap_comp_stalkIso]
    infer_instance
  exact IsIso.of_isIso_comp_right (f := (Proj.stalkIso 𝒜 p).hom)
    ((map 𝒜 D hD).stalkMap p)

end S2RescaledProj
end HodgeLean.Foundations.Program

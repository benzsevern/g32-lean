import HodgeLean.Foundations.Program.SchoenRescaledLocalizationEquiv
import HodgeLean.Foundations.Program.SchoenRescaledProjPoints
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization TopologicalSpace CategoryTheory
namespace HodgeLean.Foundations.Program
namespace S2RescaledProj

variable {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    [GradedRing (fun n => 𝒜 (D * n))]
    (U : Opens (ProjectiveSpectrum (fun n => 𝒜 (D * n))))
    (V : Opens (ProjectiveSpectrum 𝒜))
    (hUV : (V : Set _) ⊆ s2_rescaledProjHomeomorph 𝒜 D hD ⁻¹' (U : Set _))

/-- Pointwise transport from rescaled homogeneous fractions to the original fractions. -/
def sectionPullback
    (s : ∀ x : U, AtPrime (fun n => 𝒜 (D * n)) x.val.asHomogeneousIdeal.toIdeal)
    (y : V) : AtPrime 𝒜 y.val.asHomogeneousIdeal.toIdeal :=
  s2_rescaledLocalizationHom 𝒜 D _
    (s ⟨s2_rescaledProjHomeomorph 𝒜 D hD y.val, hUV y.property⟩)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rescaling transport preserves the local fraction representations of sections. -/
theorem sectionPullback_locallyFraction
    (s : ∀ x : U, AtPrime (fun n => 𝒜 (D * n)) x.val.asHomogeneousIdeal.toIdeal)
    (hs : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction
      (fun n => 𝒜 (D * n))).pred s) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred
      (sectionPullback 𝒜 D hD U V hUV s) := by
  rintro ⟨p, hpV⟩
  obtain ⟨W, hpW, hWU, n, a, b, hb, hrep⟩ :=
    hs ⟨s2_rescaledProjHomeomorph 𝒜 D hD p, hUV hpV⟩
  refine ⟨W.comap ⟨s2_rescaledProjHomeomorph 𝒜 D hD, (s2_rescaledProjHomeomorph 𝒜 D hD).continuous⟩ ⊓ V,
    ⟨hpW, hpV⟩, Opens.infLERight _ _, D * n, a, b,
    (fun ⟨q, hqW, _⟩ => hb ⟨_, hqW⟩), ?_⟩
  rintro ⟨q, hqW, hqV⟩
  change s2_rescaledLocalizationHom 𝒜 D _
    (s ⟨s2_rescaledProjHomeomorph 𝒜 D hD q, hUV hqV⟩) = _
  apply HomogeneousLocalization.val_injective
  rw [show s2_rescaledLocalizationHom 𝒜 D _ =
    (s2_rescaledLocalizationHom 𝒜 D _) from rfl]
  change (s2_rescaledLocalizationFun 𝒜 D _
    (s ⟨s2_rescaledProjHomeomorph 𝒜 D hD q, hUV hqV⟩)).val = _
  rw [s2_rescaledLocalizationFun_val]
  exact congrArg HomogeneousLocalization.val (hrep ⟨_, hqW⟩)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rescaling pulls actual structure sheaf sections back as a ring homomorphism. -/
def sheafPullback : (ProjectiveSpectrum.Proj.structureSheaf
    (fun n => 𝒜 (D * n))).val.obj (.op U) →+*
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).val.obj (.op V) where
  toFun s := ⟨sectionPullback 𝒜 D hD U V hUV s.val,
    sectionPullback_locallyFraction 𝒜 D hD U V hUV s.val s.property⟩
  map_one' := by
    apply Subtype.ext
    funext y
    exact (s2_rescaledLocalizationHom 𝒜 D _).map_one
  map_mul' a b := by
    apply Subtype.ext
    funext y
    exact (s2_rescaledLocalizationHom 𝒜 D _).map_mul _ _
  map_zero' := by
    apply Subtype.ext
    funext y
    exact (s2_rescaledLocalizationHom 𝒜 D _).map_zero
  map_add' a b := by
    apply Subtype.ext
    funext y
    exact (s2_rescaledLocalizationHom 𝒜 D _).map_add _ _

end S2RescaledProj
end HodgeLean.Foundations.Program

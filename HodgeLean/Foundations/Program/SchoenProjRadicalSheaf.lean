import HodgeLean.Foundations.Program.SchoenProjRadicalComap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization TopologicalSpace CategoryTheory
namespace HodgeLean.Foundations.Program
namespace S2RadicalProj

variable {A B : Type} [CommRing A] [CommRing B]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f.toRingHom).radical)
    (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
    (hUV : (V : Set _) ⊆ s2_projRadicalComap 𝒜 ℬ f hf ⁻¹' (U : Set _))

/-- Pullback of pointwise homogeneous-localization sections along radical-controlled contraction. -/
def sectionPullback (s : ∀ x : U, AtPrime 𝒜 x.val.asHomogeneousIdeal.toIdeal) (y : V) :
    AtPrime ℬ y.val.asHomogeneousIdeal.toIdeal :=
  localRingHom f _ y.val.asHomogeneousIdeal.toIdeal rfl
    (s ⟨s2_projRadicalComap 𝒜 ℬ f hf y.val, hUV y.property⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise pullback preserves local homogeneous-fraction representations. -/
theorem sectionPullback_locallyFraction
    (s : ∀ x : U, AtPrime 𝒜 x.val.asHomogeneousIdeal.toIdeal)
    (hs : (AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred s) :
    (AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isLocallyFraction ℬ).pred (sectionPullback 𝒜 ℬ f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  obtain ⟨W, hpW, hWU, n, a, b, hb, hrep⟩ :=
    hs ⟨s2_projRadicalComap 𝒜 ℬ f hf p, hUV hpV⟩
  refine ⟨W.comap (s2_projRadicalComap 𝒜 ℬ f hf) ⊓ V, ⟨hpW, hpV⟩,
    Opens.infLERight _ _, n, f.gradedAddHom n a, f.gradedAddHom n b,
    (fun ⟨q, hqW, _⟩ => hb ⟨_, hqW⟩), ?_⟩
  rintro ⟨q, hqW, hqV⟩
  ext
  have hr := hrep ⟨_, hqW⟩
  simp_all [sectionPullback]

set_option backward.isDefEq.respectTransparency false in
/-- Radical-controlled contraction pulls sections back as a ring homomorphism. -/
def sheafPullback : (AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜).val.obj (.op U) →+*
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf ℬ).val.obj (.op V) where
  toFun s := ⟨sectionPullback 𝒜 ℬ f hf U V hUV s.val,
    sectionPullback_locallyFraction 𝒜 ℬ f hf U V hUV s.val s.property⟩
  map_one' := by ext; simp [sectionPullback]
  map_mul' _ _ := by ext; simp [sectionPullback]
  map_zero' := by ext; simp [sectionPullback]
  map_add' _ _ := by ext; simp [sectionPullback]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The continuous radical-controlled contraction with its actual sheaf pullback. -/
def sheafedSpaceMap :
    (AlgebraicGeometry.Proj.toSheafedSpace ℬ) ⟶
      (AlgebraicGeometry.Proj.toSheafedSpace 𝒜) where
  hom :=
    { base := TopCat.ofHom (s2_projRadicalComap 𝒜 ℬ f hf)
      c := { app U := CommRingCat.ofHom (sheafPullback 𝒜 ℬ f hf _ _ Set.Subset.rfl) } }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual sheaf pullback induces the expected homogeneous-localization map on stalks. -/
theorem stalkMap_comp_stalkIso (p : ProjectiveSpectrum ℬ) :
    (sheafedSpaceMap 𝒜 ℬ f hf).hom.stalkMap p ≫ (Proj.stalkIso ℬ p).hom =
      (Proj.stalkIso 𝒜 (s2_projRadicalComap 𝒜 ℬ f hf p)).hom ≫
        CommRingCat.ofHom (localRingHom f _ p.asHomogeneousIdeal.toIdeal rfl) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨W, hpW, s, rfl⟩ := (Proj 𝒜).presheaf.exists_germ_eq z
  change (Proj.stalkIso' ℬ p)
      ((sheafedSpaceMap 𝒜 ℬ f hf).hom.stalkMap p
        ((Proj 𝒜).presheaf.germ W _ hpW s)) =
    localRingHom f _ p.asHomogeneousIdeal.toIdeal rfl
      ((Proj.stalkIso' 𝒜 (s2_projRadicalComap 𝒜 ℬ f hf p))
        ((Proj 𝒜).presheaf.germ W _ hpW s))
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [Proj.stalkIso'_germ, Proj.stalkIso'_germ]
  rfl

end S2RadicalProj
end HodgeLean.Foundations.Program

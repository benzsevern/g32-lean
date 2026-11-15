import HodgeLean.Foundations.Program.SchoenProjRadicalMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization CategoryTheory
namespace HodgeLean.Foundations.Program
namespace S2RadicalProj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual radical-controlled Proj morphism commutes with the affine spectrum
maps of homogeneous localization on every positive-degree basic chart. -/
theorem awayι_comp_map {A B : Type} [CommRing A] [CommRing B]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f.toRingHom).radical)
    {n : ℕ} (hn : 0 < n) (a : A) (ha : a ∈ 𝒜 n) :
    Proj.awayι ℬ (f a) (f.map_mem ha) hn ≫ map 𝒜 ℬ f hf =
      Spec.map (CommRingCat.ofHom (Away.map f a)) ≫ Proj.awayι 𝒜 a ha hn := by
  rw [Proj.awayι, Proj.awayι, Category.assoc, basicOpen_ι_comp_map,
    ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec ((cancel_mono (Proj.basicOpen ℬ (f a)).topIso.hom).mp ?_)
  simp [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top,
    awayToSection_comp_appLE 𝒜 ℬ f hf ha]

/-- The actual affine localization square of a radical-controlled Proj morphism is a pullback. -/
theorem away_isPullback {A B : Type} [CommRing A] [CommRing B]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f.toRingHom).radical)
    {n : ℕ} (hn : 0 < n) (a : A) (ha : a ∈ 𝒜 n) :
    CategoryTheory.IsPullback (Spec.map (CommRingCat.ofHom (Away.map f a)))
      (Proj.awayι ℬ (f a) (f.map_mem ha) hn) (Proj.awayι 𝒜 a ha hn) (map 𝒜 ℬ f hf) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (awayι_comp_map 𝒜 ℬ f hf hn a ha)
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι, map_preimage_basicOpen]

end S2RadicalProj
end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenProjRadicalSheaf

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization CategoryTheory
namespace HodgeLean.Foundations.Program
namespace S2RadicalProj

variable {A B : Type} [CommRing A] [CommRing B]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f.toRingHom).radical)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A graded ring map with radical control of irrelevant ideals induces an actual scheme morphism. -/
def map : Proj ℬ ⟶ Proj 𝒜 where
  __ := (sheafedSpaceMap 𝒜 ℬ f hf).hom
  prop p := .mk fun x hx => by
    have hx' := hx.map (Proj.stalkIso ℬ p).hom.hom
    change IsUnit (((sheafedSpaceMap 𝒜 ℬ f hf).hom.stalkMap p ≫
      (Proj.stalkIso ℬ p).hom).hom x) at hx'
    rw [stalkMap_comp_stalkIso] at hx'
    change IsUnit (localRingHom f _ p.asHomogeneousIdeal.toIdeal rfl
      ((Proj.stalkIso 𝒜 (s2_projRadicalComap 𝒜 ℬ f hf p)).hom x)) at hx'
    have hA : IsUnit ((Proj.stalkIso 𝒜 (s2_projRadicalComap 𝒜 ℬ f hf p)).hom x) :=
      IsLocalHom.map_nonunit _ hx'
    haveI : IsLocalHom (Proj.stalkIso 𝒜 (s2_projRadicalComap 𝒜 ℬ f hf p)).hom.hom :=
      isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hA

/-- Basic opens pull back under the actual scheme morphism to the graded image basic opens. -/
theorem map_preimage_basicOpen (a : A) :
    map 𝒜 ℬ f hf ⁻¹ᵁ Proj.basicOpen 𝒜 a = Proj.basicOpen ℬ (f a) := rfl

/-- Under the stronger irrelevant-ideal hypothesis the extended morphism is Mathlib's Proj map. -/
theorem map_eq_of_irrelevant_le
    (hstrong : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    map 𝒜 ℬ f hf = Proj.map f hstrong := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On homogeneous affine charts the actual radical-controlled morphism induces
homogeneous localization of the given graded ring map. -/
theorem awayToSection_comp_appLE {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    Proj.awayToSection 𝒜 a ≫
      Scheme.Hom.appLE (map 𝒜 ℬ f hf) (Proj.basicOpen 𝒜 a) (Proj.basicOpen ℬ (f a)) (by rfl) =
    CommRingCat.ofHom (Away.map f a : Away 𝒜 a →+* Away ℬ (f a)) ≫
      Proj.awayToSection ℬ (f a) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨k, z, hz, rfl⟩ := z.mk_surjective _ ha
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
  apply Subtype.ext
  funext p
  change HomogeneousLocalization.mk _ = HomogeneousLocalization.mk _
  ext
  simp

/-- The actual morphism factors through the inverse-image basic open restriction. -/
theorem basicOpen_ι_comp_map (a : A) :
    (Proj.basicOpen ℬ (f a)).ι ≫ map 𝒜 ℬ f hf =
      (map 𝒜 ℬ f hf).resLE (Proj.basicOpen 𝒜 a) (Proj.basicOpen ℬ (f a)) (by rfl) ≫
        (Proj.basicOpen 𝒜 a).ι :=
  (Scheme.Hom.resLE_comp_ι (map 𝒜 ℬ f hf) (by rfl)).symm

end S2RadicalProj
end HodgeLean.Foundations.Program

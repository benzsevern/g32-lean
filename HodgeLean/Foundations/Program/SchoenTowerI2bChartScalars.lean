import HodgeLean.Foundations.Program.SchoenTowerI2bGenericAction
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! Scalar compatibility of a field action with the actual affine coefficient map.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
universe u
namespace HodgeLean.Foundations.Program

/-- Invariance of the field-valued chart map makes its coefficient image pointwise fixed.
Source: naturality of global sections and the spectrum global-section identification. -/
theorem s2v_i2b_chart_coefficient_fixed
    {K : Type u} [CommRing K] {U : Scheme.{u}}
    (η : Spec ↧K ⟶ U) (δ : K ≃+* K)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ η = η)
    (r : Γ(U, ⊤)) :
    δ ((η.appTop ≫ (Scheme.ΓSpecIso ↧K).hom).hom r) =
      (η.appTop ≫ (Scheme.ΓSpecIso ↧K).hom).hom r := by
  have h := congrArg (fun f : Spec ↧K ⟶ U =>
    f.appTop ≫ (Scheme.ΓSpecIso ↧K).hom) hδ
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    ← Category.assoc] at h
  exact congrArg (fun f : Γ(U, ⊤) ⟶ CommRingCat.of K => f.hom r) h

/-- A dominant chart map into a reduced scheme has an injective actual coefficient map.
Source: injectivity of pullback on sections for a quasi-compact scheme-theoretically dominant map. -/
theorem s2v_i2b_chart_coefficient_injective
    {K : Type u} [CommRing K] {U : Scheme.{u}} [IsReduced U]
    (η : Spec ↧K ⟶ U) [IsDominant η] [QuasiCompact η] :
    Function.Injective (η.appTop ≫ (Scheme.ΓSpecIso ↧K).hom).hom := by
  haveI : IsSchemeTheoreticallyDominant η :=
    IsSchemeTheoreticallyDominant.of_isDominant η
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso ↧K).hom).1.comp
    (η.app_injective ⊤)

/-- The ring map of a dominant morphism of affine spectra is injective on a domain.
Source: injectivity of global sections and naturality of the spectrum identifications. -/
theorem s2v_i2b_spec_preimage_injective
    {A K : Type u} [CommRing A] [IsDomain A] [CommRing K]
    (p : Spec ↧K ⟶ Spec ↧A) [IsDominant p] :
    Function.Injective (Spec.preimage p).hom := by
  have hn := Scheme.ΓSpecIso_naturality (Spec.preimage p)
  rw [Spec.map_preimage] at hn
  have he : (Scheme.ΓSpecIso ↧A).inv ≫
      (p.appTop ≫ (Scheme.ΓSpecIso ↧K).hom) = Spec.preimage p := by
    calc
      (Scheme.ΓSpecIso ↧A).inv ≫ (p.appTop ≫ (Scheme.ΓSpecIso ↧K).hom) =
          (Scheme.ΓSpecIso ↧A).inv ≫ ((Scheme.ΓSpecIso ↧A).hom ≫ Spec.preimage p) :=
        congrArg (fun f => (Scheme.ΓSpecIso ↧A).inv ≫ f) hn
      _ = Spec.preimage p := by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [← he]
  exact (s2v_i2b_chart_coefficient_injective p).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso ↧A).inv).1

/-- The affine coefficient map represents the actual field-source map into the spectrum of sections.
Source: naturality of the canonical morphism to the spectrum of global sections. -/
theorem s2v_i2b_field_chart_toSpecΓ
    {K : Type u} [CommRing K] {U : Scheme.{u}} (η : Spec ↧K ⟶ U) :
    η ≫ U.toSpecΓ = Spec.map (CommRingCat.ofHom
      (η.appTop ≫ (Scheme.ΓSpecIso ↧K).hom).hom) := by
  rw [Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  rfl

end HodgeLean.Foundations.Program

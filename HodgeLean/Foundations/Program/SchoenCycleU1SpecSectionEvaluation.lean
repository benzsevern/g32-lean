import HodgeLean.Foundations.Program.SchoenCycleU1SectionEvaluation

/-! # Actual section evaluations induced by affine scheme maps -/
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual affine-source scheme map evaluates regular sections on any
open containing its whole image.
Source: Hartshorne, Algebraic Geometry, II.2, sections and affine scheme maps. -/
def s2e_u1_specSectionEvaluation {A : Type u} [CommRing A]
    (X : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ X)
    (U : X.Opens) (hU : ⊤ ≤ f ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (f.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

/-- Restricting a regular section preserves its actual affine-source evaluation.
Source: Hartshorne, Algebraic Geometry, II.2; Mathlib, `Scheme.Hom.map_appLE`. -/
theorem s2e_u1_specSectionEvaluation_restrict {A : Type u} [CommRing A]
    (X : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ X)
    (U V : X.Opens) (hUV : U ≤ V)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) (hV : ⊤ ≤ f ⁻¹ᵁ V) :
    (s2e_u1_specSectionEvaluation X f U hU).comp
      (X.presheaf.map (homOfLE hUV).op).hom = s2e_u1_specSectionEvaluation X f V hV := by
  change ((X.presheaf.map (homOfLE hUV).op ≫ f.appLE U ⊤ hU) ≫
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom = _
  rw [f.map_appLE]
  rfl

/-- On a map of affine spectra, actual global-section evaluation is the
specified ring map after the canonical global-section identification.
Source: Mathlib, `Scheme.ΓSpecIso_naturality`; Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_u1_specSectionEvaluation_specMap_top
    {A R : Type u} [CommRing A] [CommRing R] (φ : R →+* A) :
    s2e_u1_specSectionEvaluation (Spec (CommRingCat.of R))
      (Spec.map (CommRingCat.ofHom φ)) ⊤ (by simp) =
        φ.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom := by
  change ((Spec.map (CommRingCat.ofHom φ)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/-- Actual affine-source section evaluation commutes with composition and
pullback through an intermediate source open.
Source: Mathlib, `Scheme.Hom.appLE_comp_appLE`; Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_u1_specSectionEvaluation_comp {A : Type u} [CommRing A]
    (X Y : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ X) (g : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (hVU : V ≤ g ⁻¹ᵁ U)
    (hV : ⊤ ≤ f ⁻¹ᵁ V) (hU : ⊤ ≤ (f ≫ g) ⁻¹ᵁ U) :
    (s2e_u1_specSectionEvaluation X f V hV).comp (g.appLE U V hVU).hom =
      s2e_u1_specSectionEvaluation Y (f ≫ g) U hU := by
  change ((g.appLE U V hVU ≫ f.appLE V ⊤ hV) ≫
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

end HodgeLean.Foundations.Program

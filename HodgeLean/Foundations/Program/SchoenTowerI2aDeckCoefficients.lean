import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Actual affine coefficients fixed by the field deck map
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A field automorphism fixing the retained field point fixes every coefficient from each actual open factorization of that point.
Source: Mathlib, Scheme.ΓSpecIso_naturality and cancellation of an open immersion. -/
theorem s2v_i2a_field_deck_fixes_affine_coefficients
    {K : Type*} [Field K] {B U : Scheme} (u : U ⟶ B) [IsOpenImmersion u]
    (η : Spec (CommRingCat.of K) ⟶ B) (ηU : Spec (CommRingCat.of K) ⟶ U)
    (hη : ηU ≫ u = η) (δ : K ≃+* K)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ η = η) :
    let φ : Γ(U, ⊤) →+* K := (ηU.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
    ∀ r, δ (φ r) = φ r := by
  intro φ r
  have hηU : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ ηU = ηU := by
    apply (cancel_mono u).mp
    rw [Category.assoc, hη, hδ]
  have htop : ηU.appTop ≫ (Spec.map (CommRingCat.ofHom δ.toRingHom)).appTop = ηU.appTop := by
    rw [← Scheme.Hom.comp_appTop, hηU]
  change (ηU.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫
    CommRingCat.ofHom δ.toRingHom).hom r = φ r
  rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc, htop]

end HodgeLean.Foundations.Program

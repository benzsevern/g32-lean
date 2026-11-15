import Mathlib.AlgebraicGeometry.Scheme

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Invariance of an actual field-valued point fixes its retained section pullback. -/
theorem s2v_l1b_invariant_field_point_sections
    {K : Type} [Field K] (X : Scheme.{0})
    (η : Spec (.of K) ⟶ X) (φ : K →+* K)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ η = η)
    (U : X.Opens) (hU : ⊤ ≤ η ⁻¹ᵁ U) (f : Γ(X, U)) :
    φ ((η.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom f) =
      (η.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom f := by
  have he : η.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of K)).hom ≫
      CommRingCat.ofHom φ = η.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of K)).hom := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc]
    change (η.appLE U ⊤ hU ≫
      (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp)) ≫ _ = _
    rw [Scheme.Hom.appLE_comp_appLE]
    have app_congr {f g : Spec (.of K) ⟶ X} (h : f = g)
        (hf : ⊤ ≤ f ⁻¹ᵁ U) (hg : ⊤ ≤ g ⁻¹ᵁ U) :
        f.appLE U ⊤ hf = g.appLE U ⊤ hg := by
      cases h
      rfl
    exact congrArg (fun g => g ≫ (Scheme.ΓSpecIso (.of K)).hom) (app_congr hφ _ _)
  exact congrArg (fun g : Γ(X, U) ⟶ CommRingCat.of K => g f) he

end HodgeLean.Foundations.Program

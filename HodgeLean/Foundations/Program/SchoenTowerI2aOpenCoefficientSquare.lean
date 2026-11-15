import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Spec

/-! Coefficients of an actual open subscheme at the specified field point.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The field coefficient map on an actual open subscheme agrees with the restricted section map on its ambient scheme. -/
theorem s2v_i2a_open_coefficient_square
    {K : Type} [Field K] (X : Scheme.{0}) (O : X.Opens)
    (η : Spec (.of K) ⟶ X) (ηO : Spec (.of K) ⟶ O.toScheme)
    (hη : ηO ≫ O.ι = η) (hO : ⊤ ≤ η ⁻¹ᵁ O) :
    (ηO.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom.comp
        (O.ι.appLE O ⊤ O.ι_preimage_self.ge).hom =
      (η.appLE O ⊤ hO ≫ (Scheme.ΓSpecIso (.of K)).hom).hom := by
  have H := Scheme.Hom.appLE_comp_appLE ηO O.ι O ⊤ ⊤ O.ι_preimage_self.ge
    (show ⊤ ≤ ηO ⁻¹ᵁ ⊤ from by simp)
  have htop : ηO.appLE ⊤ ⊤ (show ⊤ ≤ ηO ⁻¹ᵁ ⊤ from by simp) = ηO.appTop := by
    simp [Scheme.Hom.appLE]
  rw [htop] at H
  have H' : O.ι.appLE O ⊤ O.ι_preimage_self.ge ≫ ηO.appTop = η.appLE O ⊤ hO := by
    simpa only [hη] using H
  change (O.ι.appLE O ⊤ O.ι_preimage_self.ge ≫ ηO.appTop ≫
    (Scheme.ΓSpecIso (.of K)).hom).hom = _
  rw [← Category.assoc, H']

end HodgeLean.Foundations.Program

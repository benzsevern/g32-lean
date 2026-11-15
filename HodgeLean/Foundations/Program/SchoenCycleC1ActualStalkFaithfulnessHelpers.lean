import HodgeLean.Foundations.Program.SchoenCycleC1ActualLocalActionHelpers

/-! # Faithfulness detected on an actual fixed stalk -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An automorphism of an integral separated complex scheme inducing the
identity on one fixed stalk is the identity scheme morphism. -/
theorem s2e_c1_actual_automorphism_eq_id_of_fixed_stalk
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsSeparated X.hom]
    (f : X ⟶ X) [IsIso f.left] (p : X.left) (hp : f.left p = p)
    (hτ : s2e_fixed_point_stalkPullback X.left f.left p hp = RingHom.id _) :
    f = 𝟙 X := by
  have hf : s2e_step1_fieldPullback X.left f.left = s2e_step1_fieldPullback X.left (𝟙 X.left) := by
    rw [s2e_c1_fieldPullback_id]
    apply IsFractionRing.ringHom_ext (A := X.left.presheaf.stalk p)
    intro r
    rw [s2e_c1_fieldPullback_local_stalk X.left f.left p hp, hτ, RingHom.id_apply,
      RingHom.id_apply]
  apply Over.OverMorphism.ext
  exact s2e_c1_fieldPullback_faithful X.hom f.left (𝟙 X.left)
    (by simpa only [Category.id_comp] using Over.w f) hf

end HodgeLean.Foundations.Program

import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Ring.Action.Group

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend a ring action to a localization at a stable multiplicative subset. -/
@[instance_reducible]
def s2_localizationAction (B L G : Type*) [CommRing B] [CommRing L]
    [Group G] [MulSemiringAction G B] [Algebra B L]
    (M : Submonoid B) [IsLocalization M L]
    (hM : ∀ (g : G) (b : B), b ∈ M → g • b ∈ M) : MulSemiringAction G L where
  smul g := IsLocalization.map (S := L) (M := M) (T := M) L (MulSemiringAction.toRingHom G B g) (fun _ hb => hM g _ hb)
  one_smul x := by
    have heq : IsLocalization.map (S := L) (M := M) (T := M) L (MulSemiringAction.toRingHom G B 1)
        (fun _ hb => hM 1 _ hb) = RingHom.id L := by
      apply IsLocalization.ringHom_ext M
      ext b
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [IsLocalization.map_eq]
      simp only [MulSemiringAction.toRingHom_apply, one_smul]
    exact RingHom.congr_fun heq x
  mul_smul g h x := by
    have heq : IsLocalization.map (S := L) (M := M) (T := M) L (MulSemiringAction.toRingHom G B (g * h))
        (fun _ hb => hM (g * h) _ hb) =
        (IsLocalization.map (S := L) (M := M) (T := M) L (MulSemiringAction.toRingHom G B g) (fun _ hb => hM g _ hb)).comp
          (IsLocalization.map (S := L) (M := M) (T := M) L (MulSemiringAction.toRingHom G B h) (fun _ hb => hM h _ hb)) := by
      apply IsLocalization.ringHom_ext M
      ext b
      simp only [RingHom.comp_apply]
      rw [IsLocalization.map_eq, IsLocalization.map_eq, IsLocalization.map_eq]
      simp only [MulSemiringAction.toRingHom_apply, mul_smul]
    exact RingHom.congr_fun heq x
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

/-- The localized action agrees with the original action on numerators. -/
theorem s2_localizationAction_algebraMap (B L G : Type*) [CommRing B] [CommRing L]
    [Group G] [MulSemiringAction G B] [Algebra B L]
    (M : Submonoid B) [IsLocalization M L]
    (hM : ∀ (g : G) (b : B), b ∈ M → g • b ∈ M) (g : G) (b : B) :
    letI := s2_localizationAction B L G M hM
    g • algebraMap B L b = algebraMap B L (g • b) :=
  IsLocalization.map_eq _ b

/-- Scalar multiplication and the action extend compatibly to the localization. -/
theorem s2_localizationAction_smulDistribClass (B L G : Type*)
    [CommRing B] [CommRing L] [Group G] [MulSemiringAction G B] [Algebra B L]
    (M : Submonoid B) [IsLocalization M L]
    (hM : ∀ (g : G) (b : B), b ∈ M → g • b ∈ M) :
    letI := s2_localizationAction B L G M hM
    SMulDistribClass G B L := by
  letI := s2_localizationAction B L G M hM
  constructor
  intro g b x
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul',
    s2_localizationAction_algebraMap]

end HodgeLean.Foundations.Program

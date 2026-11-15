import HodgeLean.Foundations.Program.SchoenCycleC1ActualEigenparameterHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1ActualStalkFaithfulnessHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1FixedParameterRigidityHelpers

/-! # Faithful exact characters of actual curve stabilizers -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Faithfulness of an actual finite curve action gives a faithful complex
character and an associated regular parameter with that exact character.
The kernel is detected by finite parameter expansions and local separation. -/
theorem s2e_c1_actual_curve_faithful_eigenparameter
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (G : Type) [Group G] [Fintype G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (hinj : Function.Injective a)
    (p : ComplexPoint X) (hfixed : ∀ g, (a g).left p.underlying = p.underlying) :
    let R := X.left.presheaf.stalk p.underlying
    let t := s2e_native_curve_parameter X p
    ∃ χ : G →* ℂˣ, Function.Injective χ ∧ ∃ u : Rˣ, ∀ g : G,
      s2e_fixed_point_stalkPullback X.left (a g).left p.underlying (hfixed g)
        (t * (u : R)) =
      HodgeLean.Foundations.Curves.stalkC p.underlying (χ g : ℂ) * (t * (u : R)) := by
  let R := X.left.presheaf.stalk p.underlying
  let t := s2e_native_curve_parameter X p
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  haveI : IsDiscreteValuationRing R := s2e_smooth_curve_point_stalk_dvr X p
  haveI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
  obtain ⟨χ, u, hu⟩ := s2e_c1_actual_curve_finite_eigenparameter X G a ha1 hamul p hfixed
  refine ⟨χ, ?_, u, hu⟩
  apply (injective_iff_map_eq_one χ).mpr
  intro g hg
  obtain ⟨τ, hτ⟩ := s2e_c1_fixed_point_stalk_algEquiv X (a g) p.underlying (hfixed g)
  have ht : IsLocalRing.maximalIdeal R = Ideal.span {t * (u : R)} := by
    rw [Ideal.span_singleton_mul_right_unit u.isUnit]
    exact s2e_native_curve_parameter_maximalIdeal X p
  have hfix : τ (t * (u : R)) = t * (u : R) := by
    change τ.toRingHom (t * (u : R)) = _
    rw [hτ]
    simpa only [hg, Units.val_one, map_one, one_mul] using hu g
  have hτid : τ = 1 := s2e_c1_local_automorphism_eq_one_of_fixed_parameter R
    (s2e_complex_point_augmentation X p) (t * (u : R)) ht τ hfix
  have hpb : s2e_fixed_point_stalkPullback X.left (a g).left p.underlying (hfixed g) =
      RingHom.id R := by
    rw [← hτ, hτid]
    rfl
  apply hinj
  exact (s2e_c1_actual_automorphism_eq_id_of_fixed_stalk X (a g) p.underlying
    (hfixed g) hpb).trans ha1.symm

end HodgeLean.Foundations.Program

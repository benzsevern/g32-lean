import HodgeLean.Foundations.Program.SchoenCycleC1ParameterAdicAction
import HodgeLean.Foundations.Program.SchoenCycleC1FaithfulEigenparameterHelpers
import HodgeLean.Foundations.Program.SchoenCycleQuotientAdicStalkAction

/-! # Formal linearization retaining the actual fixed stalk action -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- An actual faithful finite curve action fixing a point has formal parameter
coordinates intertwining all the specified stalk pullbacks with its faithful
scalar character, and retaining every polynomial value in the parameter. -/
theorem s2e_c1_actual_fixed_formal_parameter_action
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (G : Type) [Group G] [Fintype G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (hinj : Function.Injective a)
    (p : ComplexPoint X) (hfixed : ∀ g, (a g).left p.underlying = p.underlying) :
    let R := X.left.presheaf.stalk p.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
    let I : Ideal (Polynomial ℂ) := Ideal.span {Polynomial.X}
    let J := IsLocalRing.maximalIdeal R
    let β (g : G) : R →ₐ[ℂ] R :=
      { toRingHom := s2e_fixed_point_stalkPullback X.left (a g).left p.underlying (hfixed g)
        commutes' := s2e_fixed_point_stalkPullback_scalars X (a g) p.underlying (hfixed g) }
    ∃ χ : G →* ℂˣ, Function.Injective χ ∧ ∃ u : Rˣ,
      let t := s2e_native_curve_parameter X p * (u : R)
      let α (g : G) : Polynomial ℂ →ₐ[ℂ] Polynomial ℂ :=
        Polynomial.aeval (Polynomial.C (χ g : ℂ) * Polynomial.X)
      ∃ hα : ∀ g n, ∀ f ∈ I ^ n, α g f ∈ I ^ n,
      ∃ E : AdicCompletion I (Polynomial ℂ) ≃ₐ[ℂ] AdicCompletion J R,
        (∀ f, E (AdicCompletion.of _ _ f) = AdicCompletion.of _ _ (Polynomial.aeval t f)) ∧
        ∀ g, (s2e_adic_algebra_map J J (β g)
          (s2e_fixed_point_stalkPullback_power X.left (a g).left p.underlying (hfixed g))).comp
            E.toAlgHom = E.toAlgHom.comp (s2e_adic_algebra_map I I (α g) (hα g)) := by
  let R := X.left.presheaf.stalk p.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  let β (g : G) : R →ₐ[ℂ] R :=
    { toRingHom := s2e_fixed_point_stalkPullback X.left (a g).left p.underlying (hfixed g)
      commutes' := s2e_fixed_point_stalkPullback_scalars X (a g) p.underlying (hfixed g) }
  obtain ⟨χ, hχ, u, hu⟩ := s2e_c1_actual_curve_faithful_eigenparameter
    X G a ha1 hamul hinj p hfixed
  let t := s2e_native_curve_parameter X p * (u : R)
  have ht : IsLocalRing.maximalIdeal R = Ideal.span {t} := by
    rw [Ideal.span_singleton_mul_right_unit u.isUnit]
    exact s2e_native_curve_parameter_maximalIdeal X p
  have htn : t ≠ 0 := mul_ne_zero (s2e_native_curve_parameter_irreducible X p).ne_zero u.ne_zero
  have hreg : Function.Injective (fun x : R => t * x) := fun _ _ h => mul_left_cancel₀ htn h
  have he (g : G) : β g t = algebraMap ℂ R (χ g : ℂ) * t := hu g
  obtain ⟨hp, hα, hβ, E, _, hval, hact⟩ := s2e_c1_parameter_adic_action
    R (s2e_complex_point_augmentation X p) t ht hreg G β (fun g => (χ g : ℂ)) he
  exact ⟨χ, hχ, u, hα, E, hval, hact⟩

end HodgeLean.Foundations.Program

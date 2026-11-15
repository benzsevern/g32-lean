import HodgeLean.Foundations.Program.SchoenCycleSmoothPowerJets
import HodgeLean.Foundations.Program.SchoenCycleAdicCoordinates
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! # Adic coordinates on the actual smooth curve power -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The finite polynomial coordinates of the actual curve power determine formal
coordinates in its maximal-ideal adic ring, with the specified parameter evaluation.
Source: Hartshorne, Algebraic Geometry, II.8; Mathlib, AdicCompletion.liftRingHom. -/
theorem s2e_smooth_curve_power_stalk_adic_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x : ComplexPoint (g3_power X n)) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ E : AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal R) R,
      ∀ p : MvPolynomial (Fin n) ℂ,
        E (AdicCompletion.of (idealOfVars (Fin n) ℂ) _ p) =
          AdicCompletion.of (IsLocalRing.maximalIdeal R) R
            (aeval (s2e_curvePowerParameter X n x) p) := by
  let R := (g3_power X n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let I := idealOfVars (Fin n) ℂ
  let J := IsLocalRing.maximalIdeal R
  have hn : ∀ N : ℕ, ∃ e : (MvPolynomial (Fin n) ℂ ⧸ I ^ N) ≃+* (R ⧸ J ^ N),
      ∀ p, e (Ideal.Quotient.mk (I ^ N) p) =
        Ideal.Quotient.mk (J ^ N) (aeval (s2e_curvePowerParameter X n x) p) := by
    intro N
    by_cases hN : N = 0
    · subst N
      haveI : Subsingleton (MvPolynomial (Fin n) ℂ ⧸ I ^ 0) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      haveI : Subsingleton (R ⧸ J ^ 0) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      letI : Unique (MvPolynomial (Fin n) ℂ ⧸ I ^ 0) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
      letI : Unique (R ⧸ J ^ 0) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
      exact ⟨RingEquiv.ofUnique, fun _ => Subsingleton.elim _ _⟩
    · obtain ⟨e, he⟩ := s2e_smooth_curve_power_stalk_finite_coordinates X n x N
        (Nat.pos_of_ne_zero hN)
      exact ⟨e.toRingEquiv, he⟩
  choose e he using hn
  have hc : ∀ {a b : ℕ} (h : a ≤ b) z,
      Ideal.Quotient.factorPow J h (e b z) = e a (Ideal.Quotient.factorPow I h z) := by
    intro a b h z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [he, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  obtain ⟨E, hE⟩ := s2e_adic_coordinates_equiv I J e hc
  refine ⟨E, fun p => ?_⟩
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [hE, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, he]

#print axioms s2e_smooth_curve_power_stalk_adic_coordinates

/-- Formal power series give coordinates on the actual curve-power adic stalk,
and polynomial series evaluate at the fixed geometric parameters.
Source: Hartshorne, Algebraic Geometry, II.8;
Mathlib, MvPowerSeries.toAdicCompletionAlgEquiv. -/
theorem s2e_smooth_curve_power_stalk_powerSeries_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x : ComplexPoint (g3_power X n)) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ E : MvPowerSeries (Fin n) ℂ ≃+* AdicCompletion (IsLocalRing.maximalIdeal R) R,
      ∀ p : MvPolynomial (Fin n) ℂ,
        E (p : MvPowerSeries (Fin n) ℂ) =
          AdicCompletion.of (IsLocalRing.maximalIdeal R) R
            (aeval (s2e_curvePowerParameter X n x) p) := by
  obtain ⟨E, hE⟩ := s2e_smooth_curve_power_stalk_adic_coordinates X n x
  refine ⟨(MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) ℂ).toRingEquiv.trans E, ?_⟩
  intro p
  change E (MvPowerSeries.toAdicCompletion (Fin n) ℂ p) = _
  rw [MvPowerSeries.toAdicCompletion_coe, hE]

#print axioms s2e_smooth_curve_power_stalk_powerSeries_coordinates

/-- The formal coordinates respect the native complex algebra structure.
Source: Hartshorne, Algebraic Geometry, II.8;
the scalar identity follows by evaluating constant polynomials. -/
theorem s2e_smooth_curve_power_stalk_powerSeries_algCoordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x : ComplexPoint (g3_power X n)) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ E : MvPowerSeries (Fin n) ℂ ≃ₐ[ℂ] AdicCompletion (IsLocalRing.maximalIdeal R) R,
      ∀ p : MvPolynomial (Fin n) ℂ,
        E (p : MvPowerSeries (Fin n) ℂ) =
          AdicCompletion.of (IsLocalRing.maximalIdeal R) R
            (aeval (s2e_curvePowerParameter X n x) p) := by
  let R := (g3_power X n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  obtain ⟨E, hE⟩ := s2e_smooth_curve_power_stalk_powerSeries_coordinates X n x
  refine ⟨{ E with commutes' := ?_ }, hE⟩
  intro c
  change E (algebraMap ℂ (MvPowerSeries (Fin n) ℂ) c) =
    algebraMap ℂ (AdicCompletion (IsLocalRing.maximalIdeal R) R) c
  simpa only [MvPolynomial.coe_C, MvPowerSeries.algebraMap_apply,
    AdicCompletion.algebraMap_apply, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply] using hE (C c)

#print axioms s2e_smooth_curve_power_stalk_powerSeries_algCoordinates
end HodgeLean.Foundations.Program

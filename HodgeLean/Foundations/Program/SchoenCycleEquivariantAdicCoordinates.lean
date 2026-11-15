import HodgeLean.Foundations.Program.SchoenCycleSmoothPowerAdicCoordinates
import HodgeLean.Foundations.Program.SchoenCycleFixedAdicAction
import HodgeLean.Foundations.Program.SchoenCycleAdicPermutation
import HodgeLean.Foundations.Program.SchoenCyclePowerSeriesAdicAction

/-! # Equivariant adic coordinates of the actual smooth curve power -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Actual finite coordinates assemble into an adic coordinate equivalence
intertwining every permutation fixing the point with coordinate renaming.
Source: Hartshorne, Algebraic Geometry, II.8; Macdonald, Symmetric Functions
and Hall Polynomials, Chapter I, §2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_smooth_curve_power_equivariant_adic_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x : ComplexPoint (g3_power X n)) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ E : AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal R) R,
      (∀ p : MvPolynomial (Fin n) ℂ,
        E (AdicCompletion.of (idealOfVars (Fin n) ℂ) _ p) =
          AdicCompletion.of (IsLocalRing.maximalIdeal R) R
            (aeval (s2e_curvePowerParameter X n x) p)) ∧
      ∀ (σ : Equiv.Perm (Fin n)) (hx : Point.map (s2_permute X n σ) x = x)
        (z : AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ)),
        E (s2e_polynomial_adic_rename σ.symm z) =
          s2e_fixed_point_adicPullback (g3_power X n).left (s2_permute X n σ).left
            x.underlying (s2e_complex_point_fixed_underlying
              (g3_power X n) (s2_permute X n σ) x hx) (E z) := by
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
  refine ⟨E, ?_, ?_⟩
  · intro p
    apply AdicCompletion.ext_evalₐ
    intro N
    rw [hE, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, he]
  · intro σ hx z
    unfold s2e_polynomial_adic_rename s2e_fixed_point_adicPullback
    apply AdicCompletion.ext_evalₐ
    intro N
    rw [hE, s2e_adic_ring_map_eval, s2e_adic_ring_map_eval, hE]
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I N z)
    rw [← hp]
    simp only [s2e_adic_quotient_ring_map, he]
    change e N (Ideal.Quotient.mk (I ^ N) (rename σ.symm p)) = _
    rw [he]
    exact congrArg (Ideal.Quotient.mk (J ^ N))
      (s2e_fixed_permutation_parameter_polynomial X n σ x hx p).symm

#print axioms s2e_smooth_curve_power_equivariant_adic_coordinates
/-- Formal coordinates on the actual curve-power stalk intertwine the actual
fixed-point permutation pullbacks with formal coordinate renaming.
Source: Hartshorne, Algebraic Geometry, II.8; Macdonald, Symmetric Functions
and Hall Polynomials, Chapter I, §2. -/
theorem s2e_smooth_curve_power_equivariant_powerSeries_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x : ComplexPoint (g3_power X n)) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ E : MvPowerSeries (Fin n) ℂ ≃+* AdicCompletion (IsLocalRing.maximalIdeal R) R,
      (∀ p : MvPolynomial (Fin n) ℂ,
        E (p : MvPowerSeries (Fin n) ℂ) =
          AdicCompletion.of (IsLocalRing.maximalIdeal R) R
            (aeval (s2e_curvePowerParameter X n x) p)) ∧
      ∀ (σ : Equiv.Perm (Fin n)) (hx : Point.map (s2_permute X n σ) x = x)
        (z : MvPowerSeries (Fin n) ℂ),
        E (MvPowerSeries.rename σ.symm z) =
          s2e_fixed_point_adicPullback (g3_power X n).left (s2_permute X n σ).left
            x.underlying (s2e_complex_point_fixed_underlying
              (g3_power X n) (s2_permute X n σ) x hx) (E z) := by
  obtain ⟨E, hE, heq⟩ := s2e_smooth_curve_power_equivariant_adic_coordinates X n x
  refine ⟨(MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) ℂ).toRingEquiv.trans E,
    ?_, ?_⟩
  · intro p
    change E (MvPowerSeries.toAdicCompletion (Fin n) ℂ p) = _
    rw [MvPowerSeries.toAdicCompletion_coe, hE]
  · intro σ hx z
    change E (MvPowerSeries.toAdicCompletion (Fin n) ℂ
      (MvPowerSeries.rename σ.symm z)) = _
    rw [s2e_powerSeries_toAdic_rename, heq σ hx]
    rfl

#print axioms s2e_smooth_curve_power_equivariant_powerSeries_coordinates
end HodgeLean.Foundations.Program

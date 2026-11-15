import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.FieldHelpers
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Extending evaluations through integral covers
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.TameMonomialCover.Helpers

/-- An evaluation in an algebraically closed field extends through an injective integral extension.
Source: Mathlib, Ideal.exists_ideal_over_maximal_of_isIntegral and IsAlgClosed.lift; Stacks Project, tag 00GU. -/
theorem evaluation_extends_integral
    {C B A : Type*} [Field C] [IsAlgClosed C] [CommRing B] [CommRing A]
    [Algebra C B] [Algebra C A] [Algebra B A] [IsScalarTower C B A]
    [FaithfulSMul B A] [Algebra.IsIntegral B A]
    (p : B →ₐ[C] C) :
    ∃ q : A →ₐ[C] C, ∀ b, q (algebraMap B A b) = p b := by
  let P := RingHom.ker p.toRingHom
  have hp : Function.Surjective p := fun c =>
    ⟨algebraMap C B c, by simpa using p.commutes c⟩
  letI : P.IsMaximal := RingHom.ker_isMaximal_of_surjective p.toRingHom hp
  have hker : RingHom.ker (algebraMap B A) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective B A)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) P
    (by rw [hker]; exact bot_le)
  letI := hQ
  let π : A →ₐ[C] A ⧸ Q := Ideal.Quotient.mkₐ C Q
  have hcomm (b : B) : π (algebraMap B A b) = algebraMap C (A ⧸ Q) (p b) := by
    have hb : b - algebraMap C B (p b) ∈ P := by
      change p (b - algebraMap C B (p b)) = 0
      rw [map_sub, p.commutes]
      simp only [Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have hbQ : algebraMap B A (b - algebraMap C B (p b)) ∈ Q := by
      change b - algebraMap C B (p b) ∈ Q.under B
      rw [hQP]
      exact hb
    have H := Ideal.Quotient.eq_zero_iff_mem.mpr hbQ
    change π (algebraMap B A (b - algebraMap C B (p b))) = 0 at H
    rw [map_sub, map_sub, ← IsScalarTower.algebraMap_apply C B A, π.commutes] at H
    exact sub_eq_zero.mp H
  letI : Algebra.IsIntegral C (A ⧸ Q) := ⟨fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Algebra.IsIntegral.isIntegral (R := B) a).map_of_comp_eq p.toRingHom π.toRingHom
      (by ext b; exact (hcomm b).symm)⟩
  let e : A ⧸ Q →ₐ[C] C := IsAlgClosed.lift
  refine ⟨e.comp π, ?_⟩
  intro b
  change e (π (algebraMap B A b)) = p b
  rw [hcomm, e.commutes]
  rfl

/-- An evaluation on the integral closure extends along an embedding into a larger ambient field.
Source: Mathlib, AlgHom.mapIntegralClosure and Ideal.exists_ideal_over_maximal_of_isIntegral. -/
theorem evaluation_extends_integralClosure
    {C R K L : Type*} [Field C] [IsAlgClosed C] [CommRing R] [Field K] [Field L]
    [Algebra C R] [Algebra R K] [Algebra R L] [Algebra C K] [Algebra C L]
    [IsScalarTower C R K] [IsScalarTower C R L]
    (f : K →ₐ[R] L) (p : integralClosure R K →ₐ[C] C) :
    ∃ q : integralClosure R L →ₐ[C] C,
      ∀ b, q (f.mapIntegralClosure b) = p b := by
  let B := integralClosure R K
  let A := integralClosure R L
  let fR : B →ₐ[R] A := f.mapIntegralClosure
  let fC : B →ₐ[C] A := fR.restrictScalars C
  letI : Algebra B A := fC.toRingHom.toAlgebra
  haveI : IsScalarTower C B A := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact congrArg Subtype.val (fC.commutes c).symm)
  haveI : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact congrArg Subtype.val (fR.commutes r).symm)
  haveI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr (by
    intro b c h
    apply Subtype.ext
    apply f.injective
    exact congrArg Subtype.val h)
  haveI : Algebra.IsIntegral B A := ⟨fun a =>
    (Algebra.IsIntegral.isIntegral (R := R) a).tower_top⟩
  exact evaluation_extends_integral p

end AlgebraicGeometry.TameMonomialCover.Helpers

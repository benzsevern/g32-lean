import HodgeLean.Foundations.Program.SchoenTowerI2aEvaluationExtensions
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Specified evaluations on integral root covers
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An integral cover with an ambient-field map factors through the integral closure, retaining the specified evaluation there.
Source: Mathlib, IsIntegral.map and integralClosure. -/
theorem s2v_i2a_integral_cover_evaluation
    {R A L C : Type*} [CommRing R] [CommRing A] [CommRing L] [CommRing C]
    [Algebra R L] (i : R →+* A) (hi : i.IsIntegral) (τ : A →+* L)
    (hτ : τ.comp i = algebraMap R L) (p : integralClosure R L →+* C) :
    ∃ (β : A →+* integralClosure R L) (q : A →+* C),
      (∀ a, (β a : L) = τ a) ∧ q = p.comp β ∧
      (∀ r, β (i r) = algebraMap R (integralClosure R L) r) := by
  letI : Algebra R A := i.toAlgebra
  letI : Algebra.IsIntegral R A := algebraMap_isIntegral_iff.mp hi
  let τA : A →ₐ[R] L := { τ with commutes' := RingHom.congr_fun hτ }
  let β : A →+* integralClosure R L :=
    { toFun := fun a => ⟨τ a, (Algebra.IsIntegral.isIntegral a).map τA⟩
      map_one' := Subtype.ext (map_one τ)
      map_mul' := fun a b => Subtype.ext (map_mul τ a b)
      map_zero' := Subtype.ext (map_zero τ)
      map_add' := fun a b => Subtype.ext (map_add τ a b) }
  refine ⟨β, p.comp β, fun _ => rfl, rfl, ?_⟩
  intro r
  exact Subtype.ext (RingHom.congr_fun hτ r)

/-- Localization preserves the specified value of an integral element identified in the ambient field.
Source: Mathlib, IsLocalization.surj and cancellation of a nonzero evaluation denominator. -/
theorem s2v_i2a_localized_integral_evaluation
    {R A L C S : Type*} [CommRing R] [CommRing A] [CommRing L]
    [Field C] [CommRing S] [Algebra R L]
    (β : A →+* integralClosure R L) (p : integralClosure R L →+* C)
    [(RingHom.ker (p.comp β)).IsPrime] [Algebra A S]
    [IsLocalization.AtPrime S (RingHom.ker (p.comp β))]
    (σ : S →+* L) (hσ : ∀ a, σ (algebraMap A S a) = (β a : L))
    (pS : S →+* C) (hpS : pS.comp (algebraMap A S) = p.comp β)
    (x : S) (b : integralClosure R L) (hx : σ x = (b : L)) : pS x = p b := by
  obtain ⟨⟨a, s⟩, he⟩ := IsLocalization.surj (RingHom.ker (p.comp β)).primeCompl x
  have heL : (b : L) * (β s : L) = (β a : L) := by
    have H := congrArg σ he
    simpa only [map_mul, hσ, hx] using H
  have heI : b * β s = β a := Subtype.ext heL
  have hden : p (β s) ≠ 0 := s.2
  apply mul_right_cancel₀ hden
  calc
    pS x * p (β s) = pS x * pS (algebraMap A S s) :=
      congrArg (fun t => pS x * t) (RingHom.congr_fun hpS s).symm
    _ = pS (algebraMap A S a) := by rw [← map_mul, he]
    _ = p (β a) := RingHom.congr_fun hpS a
    _ = p b * p (β s) := by rw [← heI, map_mul]

end HodgeLean.Foundations.Program

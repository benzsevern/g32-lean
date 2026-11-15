import HodgeLean.Foundations.Program.SchoenSelectedGeometryUnramifiedLength
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A finite flat extension of complex domains has simple evaluation fibres on a nonempty basic open.
Source: generic separability in characteristic zero and openness of the unramified locus. -/
theorem s0_generic_simple_evaluations
    {B T : Type} [CommRing B] [CommRing T] [IsDomain B] [IsDomain T]
    [Algebra ℂ B] [Algebra ℂ T] [Algebra B T] [IsScalarTower ℂ B T]
    [Module.FinitePresentation B T] [Module.Flat B T] :
    ∃ f : T, f ≠ 0 ∧ ∀ (u : B →ₐ[ℂ] ℂ) (w : T →ₐ[ℂ] ℂ),
      w.comp (IsScalarTower.toAlgHom ℂ B T) = u → w f ≠ 0 →
        a3b4a_gysin_evaluationSliceLength u w = 1 := by
  letI : CharZero B := charZero_of_injective_algebraMap (algebraMap ℂ B).injective
  letI : Algebra.IsUnramifiedAt B (⊥ : Ideal T) := Algebra.isUnramifiedAt_bot
  obtain ⟨f, hf, hopen⟩ := Algebra.exists_unramified_of_isUnramifiedAt (R := B) (⊥ : Ideal T)
  refine ⟨f, hf, ?_⟩
  intro u w hw hfw
  let q := RingHom.ker w
  letI : q.IsPrime := RingHom.ker_isPrime w
  have hp : q.under B = RingHom.ker u := by
    ext b
    change w (algebraMap B T b) = 0 ↔ u b = 0
    have hb : w (algebraMap B T b) = u b := congrArg (fun v : B →ₐ[ℂ] ℂ => v b) hw
    rw [hb]
  letI : Algebra.Unramified B (Localization.Away f) := hopen
  have hmem : (⟨q, inferInstance⟩ : PrimeSpectrum T) ∈ Algebra.unramifiedLocus B T :=
    (Algebra.basicOpen_subset_unramifiedLocus_iff (R := B) (f := f)).mpr inferInstance hfw
  letI : Algebra.IsUnramifiedAt B q := hmem
  have hlen := Ideal.ramificationIdx_eq_one q B
  rw [Ideal.ramificationIdx_def, hp, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one] at hlen
  exact hlen

#print axioms s0_generic_simple_evaluations
end HodgeLean.Foundations.Program

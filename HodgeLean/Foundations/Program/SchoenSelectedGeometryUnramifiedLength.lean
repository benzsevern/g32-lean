import HodgeLean.Adapters.NormalConeB4aGysinFiniteEvaluationLength
import Mathlib.RingTheory.RamificationInertia.Ramification

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A simple evaluation fibre of a finite complex algebra is unramified at that evaluation.
Source: the ramification-index criterion over a perfect residue field. -/
theorem s0_unramified_of_evaluation_length_one
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Module.Finite B T]
    (u : B →ₐ[ℂ] ℂ) (w : T →ₐ[ℂ] ℂ)
    (hw : w.comp (IsScalarTower.toAlgHom ℂ B T) = u)
    (h : a3b4a_gysin_evaluationSliceLength u w = 1) :
    letI : (RingHom.ker w).IsPrime := RingHom.ker_isPrime w
    Algebra.IsUnramifiedAt B (RingHom.ker w) := by
  let q := RingHom.ker w
  letI : q.IsPrime := RingHom.ker_isPrime w
  have hp : q.under B = RingHom.ker u := by
    ext b
    change w (algebraMap B T b) = 0 ↔ u b = 0
    have hb : w (algebraMap B T b) = u b := congrArg (fun v : B →ₐ[ℂ] ℂ => v b) hw
    rw [hb]
  obtain ⟨e, _⟩ := a3b4a_gysin_exists_rational_residue_equiv (q.under B) u hp.symm
  letI : IsAlgClosed (q.under B).ResidueField :=
    IsAlgClosed.of_ringEquiv ℂ (q.under B).ResidueField e.symm.toRingEquiv
  apply (Ideal.ramificationIdx_eq_one_iff (R := B) (q := q)).mp
  rw [Ideal.ramificationIdx_def, hp]
  change (a3b4a_gysin_evaluationSliceLength u w).toNat = 1
  simp [h]

#print axioms s0_unramified_of_evaluation_length_one
end HodgeLean.Foundations.Program

import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Smooth.Basic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Successive positive adic quotients have square-zero transition kernel. -/
theorem s2v_l1b_adic_transition_square_zero
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) (hn : 0 < n) :
    RingHom.ker (Ideal.Quotient.factorPow I n.le_succ) ^ 2 = ⊥ := by
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
  apply le_antisymm ?_ bot_le
  rw [Ideal.map_le_iff_le_comap]
  change I ^ (n * 2) ≤ RingHom.ker (Ideal.Quotient.mk (I ^ (n + 1)))
  rw [Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)

/-- A formally smooth algebra map lifts to the next positive adic quotient. -/
theorem s2v_l1b_adic_lift_successor
    {k B R : Type*} [CommRing k] [CommRing B] [CommRing R]
    [Algebra k B] [Algebra k R] [Algebra.FormallySmooth k B]
    (I : Ideal R) (n : ℕ) (hn : 0 < n) (f : B →ₐ[k] R ⧸ I ^ n) :
    ∃ g : B →ₐ[k] R ⧸ I ^ (n + 1),
      (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right n.le_succ)).comp g = f := by
  let q : (R ⧸ I ^ (n + 1)) →ₐ[k] R ⧸ I ^ n :=
    Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right n.le_succ)
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right n.le_succ)
  have hnil : IsNilpotent (RingHom.ker q.toRingHom) :=
    ⟨2, s2v_l1b_adic_transition_square_zero I n hn⟩
  exact ⟨Algebra.FormallySmooth.liftOfSurjective f q hq hnil,
    Algebra.FormallySmooth.comp_liftOfSurjective f q hq hnil⟩

end HodgeLean.Foundations.Program

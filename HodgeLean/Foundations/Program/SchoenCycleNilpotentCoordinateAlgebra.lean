import HodgeLean.Foundations.Program.SchoenCycleSymmetricJets
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.LocalRing.Basic

/-! # Local algebras of nilpotent polynomial coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Polynomial evaluation at nilpotent variables differs from its constant
term by a nilpotent element.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1,
nilradicals and polynomial evaluation. -/
theorem s2e_nilpotent_coordinate_evaluation
    (σ A : Type*) [CommRing A] [Algebra ℂ A]
    (a : σ → A) (ha : ∀ i, IsNilpotent (a i)) (p : MvPolynomial σ ℂ) :
    IsNilpotent (aeval a p - algebraMap ℂ A (constantCoeff p)) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    convert (Commute.all _ _).isNilpotent_add hp hq using 1 <;>
      simp only [map_add] <;> ring
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact (Commute.all _ _).isNilpotent_mul_left (ha i)

/-- A complex algebra whose elements differ nilpotently from their scalar
residues is local.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1,
units modulo nilpotents and local rings. -/
theorem s2e_nilpotent_scalar_residue_isLocalRing
    (A : Type*) [CommRing A] [Algebra ℂ A] (ε : A →ₐ[ℂ] ℂ)
    (hε : ∀ a, IsNilpotent (a - algebraMap ℂ A (ε a))) : IsLocalRing A := by
  letI : Nontrivial A := ε.toRingHom.domain_nontrivial
  have hu (a : A) (ha : ε a ≠ 0) : IsUnit a := by
    have hc : IsUnit (algebraMap ℂ A (ε a)) :=
      (isUnit_iff_ne_zero.mpr ha).map (algebraMap ℂ A)
    simpa only [sub_add_cancel] using
      (hε a).isUnit_add_right_of_commute hc (Commute.all _ _)
  refine ⟨fun {a b} hab => ?_⟩
  by_cases ha : ε a = 0
  · right
    apply hu b
    have he : ε b = 1 := by
      simpa only [map_add, ha, zero_add, map_one] using congrArg ε hab
    rw [he]
    exact one_ne_zero
  · exact Or.inl (hu a ha)

end HodgeLean.Foundations.Program

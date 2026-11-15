import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistLinearCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistingCocyclePolynomial

/-! # The original coordinate monomials as actual homogeneous fractions -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open AlgebraicCurves.Cohomology.Cech.Proofs
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_nonempty_HEquiv_FD
open ProjSpaceCech
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

variable (R : Type) [CommRing R] (n : ℕ)

/-- The original coordinate monomial as a fraction of the shifted free module. -/
def paired_twist_coordinateFraction (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    GradedModule.Frac (GradedModule.FD R n 1) I :=
  GradedModule.twistFrac 1
    (Twist.Mon.incl n 1 (Finset.empty_subset I) (paired_twist_coordinateMonomial n j))

/-- A polynomial coordinate monomial retains denominator one. -/
theorem paired_twist_coordinateFraction_denExp
    (I : Finset (Fin (n + 1))) (j l : Fin (n + 1)) :
    (paired_twist_coordinateFraction R n I j).denExp l = 0 := by
  change (-(if l = j then (1 : ℤ) else 0)).toNat = 0
  split_ifs <;> rfl

/-- The numerator is the original variable with the same index and scale. -/
theorem paired_twist_coordinateFraction_num
    (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    (paired_twist_coordinateFraction R n I j).num = MvPolynomial.X j := by
  classical
  change (∏ l : Fin (n + 1), (MvPolynomial.X l : MvPolynomial (Fin (n + 1)) R) ^
    (if l = j then (1 : ℤ) else 0).toNat) = _
  rw [Finset.prod_eq_single j]
  · simp only [ite_true, Int.toNat_one, pow_one]
  · intro l _ hlj
    simp only [hlj, ite_false, Int.toNat_zero, pow_zero]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- The original coordinate trivialization appends precisely its one denominator coordinate. -/
theorem paired_twist_coordinateFraction_shift_denExp
    (I : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ I)
    (j l : Fin (n + 1)) :
    (GradedModule.coordinateDenominatorFrac (GradedModule.free R n) 1 i hi
      (paired_twist_coordinateFraction R n I j)).denExp l =
        Pi.single (M := fun _ : Fin (n + 1) => ℕ) i 1 l := by
  change (paired_twist_coordinateFraction R n I j).denExp l + Pi.single (M := fun _ : Fin (n + 1) => ℕ) i 1 l = _
  rw [paired_twist_coordinateFraction_denExp, zero_add]

/-- The original coordinate trivialization retains the same numerator variable. -/
theorem paired_twist_coordinateFraction_shift_num
    (I : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ I)
    (j : Fin (n + 1)) :
    (GradedModule.coordinateDenominatorFrac (GradedModule.free R n) 1 i hi
      (paired_twist_coordinateFraction R n I j)).num = MvPolynomial.X j :=
  paired_twist_coordinateFraction_num R n I j

end HodgeLean.Foundations.Program.G32Native

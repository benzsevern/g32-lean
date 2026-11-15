import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistingCocyclePolynomial

/-! # Degree-zero polynomial data in the actual twisting complex -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology
open ProjSpaceCech
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- A degree-zero monomial without negative exponents has every exponent zero. -/
theorem paired_c3_twist_zero_monomial {n : ℕ} (a : Twist.Mon n 0 ∅)
    (i : Fin (n + 1)) : a.val i = 0 := by
  have hnonneg : ∀ j, 0 ≤ a.val j := fun j => not_lt.mp fun h =>
    (Finset.notMem_empty j) (a.property.2 ((Twist.mem_negSupp n).mpr h))
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp
    a.property.1 i (Finset.mem_univ i)

/-- The unique monomial of degree zero in the original exponent coordinates. -/
def pairedC3TwistConstantMonomial (n : ℕ) : Twist.Mon n 0 ∅ :=
  ⟨0, by simp only [Pi.zero_apply, Finset.sum_const_zero], by
    intro j hj
    have h := (Twist.mem_negSupp n).mp hj
    exact False.elim ((lt_irrefl (0 : ℤ)) h)⟩

/-- Every degree-zero polynomial datum is its single constant coefficient. -/
theorem paired_c3_twist_constant_polynomial {R : Type} [CommRing R] {n : ℕ}
    (g : Twist.Mon n 0 ∅ →₀ R) :
    g = Finsupp.single (pairedC3TwistConstantMonomial n)
      (g (pairedC3TwistConstantMonomial n)) := by
  classical
  ext a
  have ha : a = pairedC3TwistConstantMonomial n := by
    apply Subtype.ext
    funext i
    exact paired_c3_twist_zero_monomial a i
  subst a
  exact (Finsupp.single_eq_same).symm

/-- Every degree-zero twisting cocycle is given by one constant coefficient. -/
theorem paired_c3_twisting_zero_cocycle_constant (R : Type) [CommRing R]
    (n : ℕ) (hn : 1 ≤ n)
    (c : (AlgebraicGeometry.ProjSpace.twistingSectionPresheaf R n 0).cochain
      (AlgebraicGeometry.ProjSpace.stdCoverPullback (𝟙 (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))) 0)
    (hc : (AlgebraicGeometry.ProjSpace.twistingSectionPresheaf R n 0).d
      (AlgebraicGeometry.ProjSpace.stdCoverPullback (𝟙 (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))) 0 c = 0) :
    ∃ r : R, paired_twistCochainEquiv R n 0 0
      (Twist.constSec R 0 (Finsupp.single (pairedC3TwistConstantMonomial n) r)) = c := by
  obtain ⟨g, hg⟩ := paired_twisting_zero_cocycle_polynomial R n 0 hn c hc
  refine ⟨g (pairedC3TwistConstantMonomial n), ?_⟩
  rw [← paired_c3_twist_constant_polynomial g]
  exact hg

end HodgeLean.Foundations.Program.G32Native

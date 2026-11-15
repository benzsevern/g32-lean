import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialCocycles

/-! # Unique polynomial representatives in degree zero -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech
open ProjSpaceCech
open scoped ProjSpaceCech.Twist
namespace HodgeLean.Foundations.Program.G32Native

/-- The original polynomial cocycle map retains every coefficient. -/
theorem conormal_projective_polynomial_cocycle_injective
    (R : Type) [CommRing R] (n : ℕ) (d : ℤ) :
    Function.Injective
      ((Twist.constSec R d).codRestrict
        (LinearMap.ker (Twist.d R n d 0)) (Twist.constSec_mem_ker R d)) := by
  intro p q h
  apply Finsupp.ext
  intro a
  have ht : ∑ j, a.val j = d ∧ Twist.negSupp n a.val = ∅ :=
    ⟨a.property.1, Finset.subset_empty.mp a.property.2⟩
  have hc := congrArg (fun c => Twist.coeff R d c (Twist.vtx 0) a.val)
    (congrArg Subtype.val h)
  change Twist.coeff R d (Twist.constSec R d p) (Twist.vtx 0) a.val =
    Twist.coeff R d (Twist.constSec R d q) (Twist.vtx 0) a.val at hc
  have ha : (⟨a.val, ht.1, ht.2.le⟩ : Twist.Mon n d ∅) = a := Subtype.ext rfl
  simpa only [Twist.coeff_constSec, dif_pos ht, ha] using hc

/-- Polynomial coefficients identify the entire original homogeneous zero-cocycle module. -/
def conormalProjectivePolynomialZeroEquiv
    (R : Type) [CommRing R] (n : ℕ) (hn : 1 ≤ n) (d : ℤ) :
    (Twist.Mon n d ∅ →₀ R) ≃ₗ[R] LinearMap.ker (Twist.d R n d 0) :=
  LinearEquiv.ofBijective
    ((Twist.constSec R d).codRestrict
      (LinearMap.ker (Twist.d R n d 0)) (Twist.constSec_mem_ker R d))
    ⟨conormal_projective_polynomial_cocycle_injective R n d,
      conormal_projective_polynomial_cocycle_surjective R n hn d⟩

end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.G32Native.PairedConormalLinearMonomials
import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistingPolynomialModule

/-! # The exact dimension of actual global degree-one twisting sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry ProjSpaceCech
open scoped ProjSpaceCech.Twist
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual native global linear-section module has one dimension per homogeneous coordinate. -/
theorem conormal_twisting_linear_sections_finrank
    (K : Type) [Field K] (k : ℕ) (hk : 1 ≤ k) :
    Module.finrank K ((ProjSpace.twistingSectionPresheaf K k 1).obj ⊤) = k + 1 := by
  letI : Fintype (Twist.Mon k 1 ∅) := Fintype.ofEquiv (Fin (k + 1)) (conormalLinearMonomialEquiv k)
  obtain ⟨E⟩ := conormal_twisting_global_polynomial_module K k hk 1
  calc
    Module.finrank K ((ProjSpace.twistingSectionPresheaf K k 1).obj ⊤) =
        Module.finrank K (Twist.Mon k 1 ∅ →₀ K) := E.finrank_eq
    _ = Fintype.card (Twist.Mon k 1 ∅) := Module.finrank_finsupp_self K
    _ = k + 1 := (Fintype.card_congr (conormalLinearMonomialEquiv k).symm).trans
      (Fintype.card_fin (k + 1))

/-- The homogeneous linear polynomial module has the same specified coordinate dimension. -/
theorem conormal_homogeneous_linear_polynomials_finrank
    (K : Type) [Field K] (k : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) K 1) = k + 1 := by
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X]
  simpa only [Fintype.card_fin] using
    finrank_span_eq_card (MvPolynomial.linearIndependent_X (Fin (k + 1)) K)

end HodgeLean.Foundations.Program.G32Native

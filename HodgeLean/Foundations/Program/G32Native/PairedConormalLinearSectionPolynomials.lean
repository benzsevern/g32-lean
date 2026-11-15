import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialSectionMap
import HodgeLean.Foundations.Program.G32Native.PairedConormalLinearSectionsRank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Actual linear polynomial representatives for native global sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry ProjSpaceCech
open scoped ProjSpaceCech.Twist
namespace HodgeLean.Foundations.Program.G32Native
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every actual global degree-one section is the concrete section of a homogeneous linear polynomial. -/
theorem conormal_polynomial_linear_sections_surjective
    (K : Type) [Field K] (k : ℕ) (hk : 1 ≤ k) :
    Function.Surjective (ProjSpace.polynomialTwistingSection K k 1) := by
  classical
  letI : Module.Finite K (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) K 1) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin (k + 1)) K 1)
  letI : Fintype (Twist.Mon k 1 ∅) :=
    Fintype.ofEquiv (Fin (k + 1)) (conormalLinearMonomialEquiv k)
  obtain ⟨E⟩ := conormal_twisting_global_polynomial_module K k hk 1
  letI : Module.Finite K ((ProjSpace.twistingSectionPresheaf K k 1).obj ⊤) :=
    Module.Finite.of_surjective E.symm.toLinearMap E.symm.surjective
  change Function.Surjective (conormalPolynomialSectionMap K k 1)
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((conormal_homogeneous_linear_polynomials_finrank K k).trans
      (conormal_twisting_linear_sections_finrank K k hk).symm)).mp
  exact ProjSpace.polynomialTwistingSection_injective K k 1

/-- The concrete polynomial-section map is a linear equivalence with its original chart normalization. -/
def conormalLinearPolynomialSectionEquiv
    (K : Type) [Field K] (k : ℕ) (hk : 1 ≤ k) :
    MvPolynomial.homogeneousSubmodule (Fin (k + 1)) K 1 ≃ₗ[K]
      (ProjSpace.twistingSectionPresheaf K k 1).obj ⊤ :=
  LinearEquiv.ofBijective (conormalPolynomialSectionMap K k 1)
    ⟨ProjSpace.polynomialTwistingSection_injective K k 1,
      conormal_polynomial_linear_sections_surjective K k hk⟩

end HodgeLean.Foundations.Program.G32Native

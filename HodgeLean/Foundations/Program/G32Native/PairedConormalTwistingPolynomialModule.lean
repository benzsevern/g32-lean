import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistingGlobal
import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialZeroEquiv
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModuleHEquivFD

/-! # The module of actual global twisting sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry ProjSpaceCech
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech
open scoped ProjSpaceCech.Twist
namespace HodgeLean.Foundations.Program.G32Native
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
  GradedModule.H.addCommGroup GradedModule.H.module

/-- As base-ring modules, actual global twisting sections have precisely the polynomial module. -/
theorem conormal_twisting_global_polynomial_module
    (R : Type) [CommRing R] (k : ℕ) (hk : 1 ≤ k) (d : ℕ) :
    Nonempty ((ProjSpace.twistingSectionPresheaf R k d).obj ⊤ ≃ₗ[R]
      (Twist.Mon k d ∅ →₀ R)) := by
  obtain ⟨E⟩ := GradedModule.nonempty_HEquiv_FD R k d 0
  exact ⟨(conormalTwistingGlobalEquiv R k d).trans
    (E.symm.trans (conormalProjectivePolynomialZeroEquiv R k hk d).symm)⟩

end HodgeLean.Foundations.Program.G32Native

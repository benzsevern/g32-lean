import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import HodgeLean.Foundations.Program.G32Native.PairedC3InitialFlagLinearConormal
import HodgeLean.Foundations.Program.G32Native.PairedC3PositiveTwistExtension

/-! # The initial linear-subspace flag for Route N -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected

/-- The selected initial linear subspace has the split conormal of its
flag in the full initial Abel fibre. Only this stage uses an Abel fibre.
Source: Hartshorne, Algebraic Geometry, II.8.12 and III.5.1;
ACGH, Geometry of Algebraic Curves I, IV.1–IV.3;
Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(ii).
Checked: assembly from the geometric flag, linear conormal and positive-twist section. -/
theorem paired_c3_route_n_initial_aux
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (hr : 0 < R.r) :
    Nonempty (pairedC3StageConormal P 0 ≅
      pairedC3SplitBundle R.P.k (R.P.k + 1 - R.r) (R.r - 1)) := by
  obtain ⟨F⟩ := paired_c3_initial_flag_exact_aux R P hr
  obtain ⟨eN⟩ := paired_c3_initial_flag_linear_conormal_aux R P hr F
  let e₁ := F.leftTerm ≪≫ F.fibreFrame
  let e₃ := F.rightTerm ≪≫ eN
  obtain ⟨s, hs⟩ := paired_c3_positive_twist_extension_section_aux
    R.P.k (R.P.k + 1 - R.r) (R.r - 1) F.sequence F.exact e₁ e₃
  exact ⟨F.stageTerm.symm ≪≫ pairedC3PositiveTwistExtensionFrame
    R.P.k (R.P.k + 1 - R.r) (R.r - 1) F.sequence F.exact e₁ e₃ s hs⟩

end HodgeLean.Foundations.Program.G32Native

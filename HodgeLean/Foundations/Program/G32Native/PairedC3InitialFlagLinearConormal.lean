import HodgeLean.Foundations.Program.G32Native.PairedC3InitialFlagExact
import HodgeLean.Foundations.Program.G32Native.PairedC3InitialLinearFlag
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateConormal
import HodgeLean.Foundations.Program.G32Native.PairedC3InitialFlagCoordinateNormalization
import HodgeLean.Foundations.Program.SchoenCycleS3ConormalIsoTransport

/-! # The stage-zero conormal flag -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
variable {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)

/-- B0.3: the actual inclusion in the full fibre has the negative linear
conormal, with one summand for each independent pair-residue sum.
Source: Hartshorne, Algebraic Geometry, II.8.12;
Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(ii).
Checked: transport from the coordinate inclusion and normalization statements. -/
theorem paired_c3_initial_flag_linear_conormal_aux (hr : 0 < R.r)
    (F : PairedC3InitialFlag R P) :
    Nonempty (s2c_conormal F.inclusion ≅ pairedC3SplitBundle R.P.k 0 (R.r - 1)) := by
  obtain ⟨e, he⟩ := paired_c3_initial_flag_coordinate_normalization_aux R P hr F
  obtain ⟨c⟩ := paired_c3_initial_coordinate_conormal_aux R.P.k R.r hr
  exact ⟨(s2e_ambientIsoConormalIso F.inclusion e.hom).symm ≪≫
    eqToIso (congrArg s2c_conormal he) ≪≫ c⟩

end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNMonoAssembly
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNTotalIdealComparison
import HodgeLean.Foundations.Program.G32Native.PairedC3StageFrames
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNTotalTransform
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNReesNativeMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29


/-- The natural retained-stage comparison is monic in the full ambient.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8.17;
Fulton, Intersection Theory, Appendix B.6.
The equal-rank union assembly uses the source-to-total ideal comparison
along the actual next slice. -/
theorem paired_c3_route_n_comparison_mono_aux
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 < R.r) :
    Mono (pairedC3StageComparison P i) := by
  obtain ⟨p, sq, hcomp⟩ := paired_c3_route_n_total_ideal_comparison_aux R P i
  exact paired_c3_route_n_comparison_mono_of_total_ideal R P i p sq hcomp

end HodgeLean.Foundations.Program.G32Native

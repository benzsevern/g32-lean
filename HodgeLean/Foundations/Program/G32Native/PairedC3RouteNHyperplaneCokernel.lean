import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNCokernelUnitAssembly
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNIntersectionConormalUnit
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNReesCokernel
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNAdaptedUnit
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNStepTransitions

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29


/-- The actual natural comparison has the specified untwisted residue
hyperplane pushforward as its categorical cokernel.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8;
Fulton, Intersection Theory, Appendix B.6.
The normalized intersection conormal trivialization supplies the
geometric input; the natural cokernel and hyperplane transports are retained. -/
theorem paired_c3_route_n_hyperplane_cokernel_aux
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 < R.r) :
    Nonempty (cokernel (pairedC3StageComparison P i) ≅
      pairedC3HyperplaneQuotient R.P.k (P.C.residue.indices i)) := by
  obtain ⟨eUnit⟩ := paired_c3_route_n_intersection_conormal_unit_aux R P i
  exact paired_c3_route_n_hyperplane_cokernel_of_unit R P i eUnit

end HodgeLean.Foundations.Program.G32Native

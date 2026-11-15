import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNResidueIntersection
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNReesCokernelGenerator
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNInverseRatio
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNAdaptedUnit
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNMarkedRuling
import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveRulingConormal
import HodgeLean.Foundations.Program.G32Native.PairedResidualDiagramGeometry

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- The actual residual-intersection conormal is the untwisted structure
module on that same intersection scheme.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7, pp. 16–17;
Hartshorne, Algebraic Geometry, II.7.13 and II.8;
Fulton, Intersection Theory, Appendix B.6.
The normalized paired-ratio maps glue to a smooth marked ruling at every
retained stage. Flat conormal base change identifies its actual marked
fibre conormal with the untwisted structure module. -/
theorem paired_c3_route_n_intersection_conormal_unit_aux
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    letI := P.C.sliceImmersion i.succ
    let E := (P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap (P.T.b i).left
    let I := (P.C.slices i.castSucc).left.ker.comap (P.T.b i).left
    let Z := residualIntersection (P.C.slices i.succ) (E ⊔ I)
    Nonempty (s2c_conormal (residualIntersectionSecond (P.C.slices i.succ) (E ⊔ I)).left ≅
      (SheafOfModules.unit Z.left.ringCatSheaf : Z.left.Modules)) := by
  letI := P.C.sliceImmersion i.succ
  dsimp only
  have h := pairedC3_route_n_marked_ruling R P i
  dsimp only at h
  rw [Scheme.IdealSheafData.comap_sup] at h
  obtain ⟨g, hg, hsquare⟩ := h
  letI : Smooth g.left := hg
  exact pairedC3_projective_ruling_conormal_unit _ g.left _ hsquare

end HodgeLean.Foundations.Program.G32Native

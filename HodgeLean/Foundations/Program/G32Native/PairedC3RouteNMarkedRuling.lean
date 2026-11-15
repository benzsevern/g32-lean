import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNRulingOverlap
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNRulingSmooth
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNRulingMarked

/-! # The selected global ruling from its local quotient maps -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

attribute [local instance] G32JointSlicedComponent.sliceImmersion
open HodgeLean.Foundations.Program.G32Native


open CategoryTheory.Limits
open AlgebraicGeometry.RamifiedNormalization.StageFour


/-- The local quotient-map assembly supplies the selected residual ruling,
its smoothness and the marked fibre on the actual intersection subscheme.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.3, II.7.13 and III.10. -/
theorem pairedC3_route_n_marked_ruling
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let M := (K ⊔ (P.C.slices i.castSucc).left.ker).comap (P.T.b i).left
    ∃ g : residualComponent (V := P.T.B i.succ) M ⟶ projectiveLine,
      Smooth g.left ∧ IsPullback
        (residualIntersection (P.C.slices i.succ) M).hom
        (residualIntersectionSecond (P.C.slices i.succ) M).left
        (projectiveLineChart 1 (1 : ℂ)).left g.left := by
  dsimp only
  let A := pairedC3RouteNRulingCharts R P i
  exact pairedC3_quotient_ruling_assembly _ _ projectiveLine A.V A.covers
    (fun j => (A.map j).left) (pairedC3_route_n_ruling_overlap R P i)
    (fun j => Over.w (A.map j)) (pairedC3_route_n_ruling_chart_smooth R P i)
    _ _ _ (pairedC3_route_n_ruling_chart_marked R P i)

#print axioms pairedC3_route_n_marked_ruling
end HodgeLean.Foundations.Program.ResidueSelected

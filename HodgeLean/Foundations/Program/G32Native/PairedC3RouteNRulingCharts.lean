import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNRatioAtlas
import HodgeLean.Foundations.Program.G32Native.PairedC3QuotientRulingCharts

/-! # The actual normalized local maps for the selected ruling -/
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



open AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Choose the checked normalized Rees charts and attach their actual
projective ratio maps. On the two charts the parameters are αs and α⁻¹t.
Source: Hartshorne, Algebraic Geometry, II.7.13;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
def pairedC3RouteNRulingCharts
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let M := (K ⊔ (P.C.slices i.castSucc).left.ker).comap (P.T.b i).left
    PairedC3QuotientRulingCharts M
      (M.subschemeι ≫ (P.T.B i.succ).hom) := by
  dsimp only
  let A := pairedC3RouteNRatioAtlas R P i
  exact ⟨A.Index, (fun j => (A.chart j).V), A.covers, (fun j => (A.chart j).map)⟩

#print axioms pairedC3RouteNRulingCharts
end HodgeLean.Foundations.Program.ResidueSelected

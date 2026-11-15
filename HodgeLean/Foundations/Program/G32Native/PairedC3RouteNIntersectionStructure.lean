import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNResidueIntersection
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import HodgeLean.Foundations.Program.SchoenCycleS3ConormalIsoTransport

/-! # The untwisted structure module of the actual retained intersection -/
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

/-- The original immersion of the actual residual intersection transports
its structure module to the specified untwisted hyperplane quotient.
The specified residue index and the unit structure module are retained.
Source: Hartshorne, Algebraic Geometry, II.5 and II.7.13. -/
theorem paired_c3_route_n_intersection_structure
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
    Nonempty ((Scheme.Modules.pullback
      (s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))).hom).obj
      ((Scheme.Modules.pushforward (residualIntersectionFirst
        (P.C.slices i.succ) (E ⊔ I)).left).obj
          (SheafOfModules.unit Z.left.ringCatSheaf)) ≅
      pairedC3HyperplaneQuotient R.P.k (P.C.residue.indices i)) := by
  letI := P.C.sliceImmersion i.succ
  dsimp only
  obtain ⟨e, he⟩ := paired_c3_route_n_residue_intersection R P i
  let H := s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)
  let E := (P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap (P.T.b i).left
  let I := (P.C.slices i.castSucc).left.ker.comap (P.T.b i).left
  let Z := residualIntersection (P.C.slices i.succ) (E ⊔ I)
  haveI : IsIso (SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom) :=
    s2e_unitPushforward_isIso e.hom
  let ef := (Scheme.Modules.pushforwardCongr he.symm).app
      (SheafOfModules.unit Z.left.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforwardComp e.hom H.subschemeι).symm.app
      (SheafOfModules.unit Z.left.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforward H.subschemeι).mapIso
      (asIso (SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom)).symm
  exact ⟨(Scheme.Modules.pullback
    (s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))).hom).mapIso ef⟩

#print axioms paired_c3_route_n_intersection_structure
end HodgeLean.Foundations.Program.G32Native

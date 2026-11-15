import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNResidualCokernel
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNIntersectionStructure

/-! # The hyperplane cokernel from the actual intersection conormal -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- A trivialization of the actual residual-intersection conormal gives
the specified untwisted cokernel of the actual stage comparison.
This assembly transports that trivialization; it does not supply it.
Source: Fulton, Intersection Theory, Appendix B.7.4;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_route_n_hyperplane_cokernel_of_unit
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
    ∀ eUnit : s2c_conormal (residualIntersectionSecond (P.C.slices i.succ) (E ⊔ I)).left ≅
      (SheafOfModules.unit Z.left.ringCatSheaf : Z.left.Modules),
      Nonempty (cokernel (pairedC3StageComparison P i) ≅
        pairedC3HyperplaneQuotient R.P.k (P.C.residue.indices i)) := by
  letI := P.C.sliceImmersion i.succ
  dsimp only
  intro eUnit
  obtain ⟨eC⟩ := paired_c3_route_n_residual_cokernel R P i
  obtain ⟨eH⟩ := paired_c3_route_n_intersection_structure R P i
  let E := (P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap (P.T.b i).left
  let I := (P.C.slices i.castSucc).left.ker.comap (P.T.b i).left
  let a := (residualIntersectionFirst (P.C.slices i.succ) (E ⊔ I)).left
  let F := Scheme.Modules.pullback (s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))).hom
  exact ⟨eC ≪≫ F.mapIso ((Scheme.Modules.pushforward a).mapIso eUnit) ≪≫ eH⟩

#print axioms paired_c3_route_n_hyperplane_cokernel_of_unit
end HodgeLean.Foundations.Program.G32Native

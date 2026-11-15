import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedOrientedPositiveData
import HodgeLean.Foundations.Program.SchoenTowerFoundC1b
import HodgeLean.Foundations.Program.G32Native.PairedC3ClosedPointCover
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedReesCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidueSupport

/-! # Actual total-transform identities on the two selected last charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- The supplied selected blowup is an actual isomorphism off its paired
centre, by the image-ideal universal property.
Source: Hartshorne, Algebraic Geometry, II.7.14. -/
theorem paired_c3_selected_off_centre_iso
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let U : (P.T.B i.castSucc).left.Opens :=
      ⟨(K.support : Set _)ᶜ, K.support.isClosed.isOpen_compl⟩
    ∃ e : ((P.T.b i).left ⁻¹ᵁ U).toScheme ≅ U.toScheme,
      e.hom = (P.T.b i).left ∣_ U ∧
      e.inv ≫ ((P.T.b i).left ⁻¹ᵁ U).ι ≫ (P.T.b i).left = U.ι := by
  dsimp only
  apply ExistsUnique.exists
  apply s2t_cartierUniversal_offCentre
  · intro T f hf
    let T' : Over (Spec ↧ℂ) := Over.mk (f ≫ (P.T.B i.castSucc).hom)
    let f' : T' ⟶ P.T.B i.castSucc := Over.homMk f rfl
    obtain ⟨u, hu, huniq⟩ := P.T.hblowup i T' f' hf
    refine ⟨u.left, congrArg (fun v => v.left) hu, ?_⟩
    intro v hv
    have hvbase : v ≫ (P.T.B i.succ).hom = T'.hom := by
      rw [← (P.T.b i).w, ← Category.assoc, hv]
      rfl
    let v' : T' ⟶ P.T.B i.succ := Over.homMk v hvbase
    have heq : v' ≫ P.T.b i = f' := by
      apply Over.OverMorphism.ext
      exact hv
    exact congrArg (fun v => v.left) (huniq v' heq)
  · intro x hx
    exact hx

#print axioms paired_c3_selected_off_centre_iso
end HodgeLean.Foundations.Program.ResidueSelected

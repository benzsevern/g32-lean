import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedSliceQuotientRegular
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Morphism properties of the selected step used for ratio comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

attribute [local instance] G32JointSlicedComponent.sliceImmersion

/-- The selected blow-up step is dominant and quasi-compact. Dominance
comes from the retained dominant generic source, and quasi-compactness
from the projective structure morphisms.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem pairedC3_selected_ruling_step_properties
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) : IsDominant (P.T.b i).left ∧ QuasiCompact (P.T.b i).left := by
  haveI : IsDominant R.β₀.left := n1bc_dominant_of_points_surjective R.β₀
    (n1bc_originalCover_points_surjective R.p₀ R.hpsurj (R.h + 1)
      R.q₀ R.γ R.hγsurj R.β₀ R.hβ₀)
  haveI : IsDominant (R.W₀.left.fromSpecStalk (genericPoint R.W₀.left)) :=
    s2_genericPointMorphism_dominant R.W₀.left
  haveI : IsDominant (P.T.η 0 ≫ P.T.e₀.hom.left) := by rw [P.T.hη₀]; infer_instance
  have hdom₀ : IsDominant (P.T.η 0) :=
    IsDominant.of_comp_of_isOpenImmersion (P.T.η 0) P.T.e₀.hom.left
  let K := fun j : Fin R.r => P.T.D j.castSucc ⟨2 * j.val, by omega⟩ ⊔
    P.T.D j.castSucc ⟨2 * j.val + 1, by omega⟩
  haveI : ∀ j, IsDominant (P.T.η j) :=
    s2v_i2b_tower_genericSource_dominant P.T.B P.T.b K P.T.hcartier
      P.T.hblowup P.T.η P.T.hη hdom₀
  haveI : IsDominant (P.T.η i.succ ≫ (P.T.b i).left) := by rw [P.T.hη]; infer_instance
  have hdom := IsDominant.of_comp (P.T.η i.succ) (P.T.b i).left
  haveI : QuasiCompact ((P.T.b i).left ≫ (P.T.B i.castSucc).hom) := by
    rw [Over.w]
    infer_instance
  exact ⟨hdom, QuasiCompact.of_comp (P.T.b i).left (P.T.B i.castSucc).hom⟩

#print axioms pairedC3_selected_ruling_step_properties
end HodgeLean.Foundations.Program.ResidueSelected

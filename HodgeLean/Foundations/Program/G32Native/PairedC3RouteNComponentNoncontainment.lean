import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRestrictions
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidueSupport

/-! # The retained component is not contained in the exceptional component -/
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

/-- Properness of the specified residue hyperplane excludes containment of
the retained next slice in the exceptional part of its total transform.
Source: Hartshorne, Algebraic Geometry, II.2 and II.7.13. -/
theorem paired_c3_route_n_component_noncontainment
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    let σ := (P.T.b i).left
    let I := (P.C.slices i.castSucc).left.ker.comap σ
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    ¬ Set.range (P.C.slices i.succ).left ⊆ ((K.comap σ ⊔ I).support : Set _) := by
  dsimp only
  let σ := (P.T.b i).left
  let i₀ := (P.C.slices i.castSucc).left
  let i₁ := (P.C.slices i.succ).left
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
  have hK : K.comap i₀ = s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i) := by
    rw [Scheme.IdealSheafData.comap_sup, hp.1, hp.2, sup_idem]
  have hc : i₁ ≫ σ = i₀ := congrArg Over.Hom.left (P.C.sliceComp i)
  intro hsub
  apply paired_c3_residue_support_proper R.P.k (P.C.residue.indices i)
  apply top_unique
  intro x _
  rw [← hK, Scheme.IdealSheafData.support_comap]
  change i₀ x ∈ (K.support : Set _)
  have hx := hsub (Set.mem_range_self (f := i₁) x)
  rw [Scheme.IdealSheafData.support_sup] at hx
  have hx' := hx.1
  rw [Scheme.IdealSheafData.support_comap] at hx'
  change σ (i₁ x) ∈ (K.support : Set _) at hx'
  simpa only [← Scheme.Hom.comp_apply, hc] using hx'

#print axioms paired_c3_route_n_component_noncontainment
end HodgeLean.Foundations.Program.G32Native

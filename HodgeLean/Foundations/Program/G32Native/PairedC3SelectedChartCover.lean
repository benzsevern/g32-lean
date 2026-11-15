import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedChartUnion
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

/-- The selected chart union identities hold around every scheme point
of the retained residue hyperplane, using Jacobson coverage.
Source: Hartshorne, Algebraic Geometry, II.3 and II.7.13. -/
theorem paired_c3_selected_chart_union_at_point
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r)
    (x : ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ))
    (hx : x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support) :
    let σ := (P.T.b i).left
    let I := (P.C.slices i.castSucc).left.ker.comap σ
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    ∃ (U : (P.T.B i.castSucc).left.affineOpens)
      (V₁ V₂ : (P.T.B i.succ).left.affineOpens),
      (P.C.slices i.castSucc).left x ∈ U.1 ∧
      V₁.1 ⊔ V₂.1 = σ ⁻¹ᵁ U.1 ∧
      (∀ V ∈ ({V₁, V₂} : Set (P.T.B i.succ).left.affineOpens),
        I.ideal V = (P.C.slices i.succ).left.ker.ideal V ⊓
          ((K.comap σ).ideal V ⊔ I.ideal V)) := by
  dsimp only
  let PP : Over (Spec ↧ℂ) := Over.mk
    (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))
  letI : IsProjective PP.hom := s0_projective_space_projective _ _
  letI : JacobsonSpace (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)) := LocallyOfFiniteType.jacobsonSpace PP.hom
  let σ := (P.T.b i).left
  let I := (P.C.slices i.castSucc).left.ker.comap σ
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let 𝒜 : Set (P.T.B i.castSucc).left.affineOpens := {U |
    ∃ V₁ V₂ : (P.T.B i.succ).left.affineOpens,
      V₁.1 ⊔ V₂.1 = σ ⁻¹ᵁ U.1 ∧
      ∀ V ∈ ({V₁, V₂} : Set (P.T.B i.succ).left.affineOpens),
        I.ideal V = (P.C.slices i.succ).left.ker.ideal V ⊓
          ((K.comap σ).ideal V ⊔ I.ideal V)}
  let O : (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)).Opens := ⨆ U : 𝒜, (P.C.slices i.castSucc).left ⁻¹ᵁ U.val.1
  have hcov : ((s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support :
      Set (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ))) ⊆ (O : Set _) := by
    apply G32Native.paired_c3_closed_point_cover
      (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support.isClosed O.isOpen
    intro z hz hclosed
    let p : ComplexPoint PP := Over.homMk (pointOfClosedPoint PP.hom z hclosed)
      (pointOfClosedPoint_comp PP.hom z hclosed)
    have hp : p.underlying = z := pointOfClosedPoint_apply PP.hom z hclosed _
    obtain ⟨U, V₁, V₂, hzU, hcover, hcalc⟩ :=
      paired_c3_selected_chart_union R P i hi p (by rwa [hp])
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨⟨U, V₁, V₂, hcover, hcalc⟩, ?_⟩
    change (P.C.slices i.castSucc).left z ∈ U.1
    simpa only [Point.underlying_map, hp] using hzU
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hx)
  obtain ⟨V₁, V₂, hcover, hcalc⟩ := U.property
  exact ⟨U.val, V₁, V₂, hxU, hcover, hcalc⟩

#print axioms paired_c3_selected_chart_union_at_point
end HodgeLean.Foundations.Program.ResidueSelected

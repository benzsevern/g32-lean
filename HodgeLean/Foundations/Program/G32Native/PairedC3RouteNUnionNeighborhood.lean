import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNChartUnion

/-! # Actual total-transform identities on the two selected single-pair charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- Every point over the centre-slice intersection has an actual affine
neighborhood on which the required total-transform ideal identity holds.
Source: Hartshorne, Algebraic Geometry, II.7.13;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_route_n_union_neighborhood
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r)
    (y : (P.T.B i.succ).left)
    (hslice : (P.T.b i).left y ∈ (P.C.slices i.castSucc).left.ker.support)
    (hcentre : (P.T.b i).left y ∈
      (P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).support) :
    let σ := (P.T.b i).left
    let I := (P.C.slices i.castSucc).left.ker.comap σ
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    ∃ V : (P.T.B i.succ).left.affineOpens, y ∈ V.1 ∧
      I.ideal V = (P.C.slices i.succ).left.ker.ideal V ⊓
        ((K.comap σ).ideal V ⊔ I.ideal V) := by
  dsimp only
  letI := P.C.sliceImmersion i.castSucc
  have hrange : (P.T.b i).left y ∈ Set.range (P.C.slices i.castSucc).left := by
    have h := hslice
    change (P.T.b i).left y ∈ ((P.C.slices i.castSucc).left.ker.support : Set _) at h
    rw [Scheme.Hom.support_ker] at h
    rwa [(P.C.slices i.castSucc).left.isClosedEmbedding.isClosed_range.closure_eq] at h
  obtain ⟨x, hx⟩ := hrange
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
  have hKres : (P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap
      (P.C.slices i.castSucc).left =
        s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i) := by
    rw [Scheme.IdealSheafData.comap_sup, hp.1, hp.2, sup_idem]
  have hxH : x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support := by
    rw [← hKres, Scheme.IdealSheafData.support_comap]
    change (P.C.slices i.castSucc).left x ∈
      ((P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).support : Set _)
    rw [hx]
    exact hcentre
  obtain ⟨U, V₁, V₂, hxU, hcover, hcalc⟩ :=
    paired_c3_route_n_chart_union R P i x hxH
  have hy : y ∈ V₁.1 ⊔ V₂.1 := by
    rw [hcover]
    change (P.T.b i).left y ∈ U.1
    rwa [hx] at hxU
  rcases hy with hy | hy
  · exact ⟨V₁, hy, hcalc V₁ (Set.mem_insert _ _)⟩
  · exact ⟨V₂, hy, hcalc V₂ (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

#print axioms paired_c3_route_n_union_neighborhood
end HodgeLean.Foundations.Program.G32Native

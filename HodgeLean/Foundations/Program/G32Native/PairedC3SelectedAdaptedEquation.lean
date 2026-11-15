import HodgeLean.Foundations.Program.G32Native.PairedC3AffineSliceCoefficient
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedReesCharts

/-! # Adapted kernel equations along the retained slice tower -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- At every unprocessed pair, the retained residue equality supplies an
adapted equation in the actual kernel of the slice section map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4;
Hartshorne, Algebraic Geometry, II.3 and II.7.13. -/
theorem paired_c3_selected_adapted_equation
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin (R.r + 1)) (j : Fin R.r) (hij : i.val ≤ j.val)
    (U : (P.T.B i).left.affineOpens) (u v : Γ((P.T.B i).left, U))
    (hu : (P.T.D i ⟨2 * j.val, by omega⟩).ideal U = Ideal.span {u})
    (hv : (P.T.D i ⟨2 * j.val + 1, by omega⟩).ideal U = Ideal.span {v}) :
    ∃ a : Γ((P.T.B i).left, U),
      ((P.C.slices i).left.app U.1).hom (u - a * v) = 0 := by
  letI := P.C.sliceImmersion i
  have hp := paired_c3_selected_unprocessed_restrictions R P i j hij
  exact G32Native.paired_c3_affine_slice_coefficient (P.C.slices i).left
    _ _ (hp.1.trans hp.2.symm) U u v hu hv

#print axioms paired_c3_selected_adapted_equation
/-- The adapted branch equation belongs to the actual ideal sheaf of the
retained slice on the chosen ambient affine open.
Source: Hartshorne, Algebraic Geometry, II.3 and II.5. -/
theorem paired_c3_selected_adapted_ideal
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin (R.r + 1)) (j : Fin R.r) (hij : i.val ≤ j.val)
    (U : (P.T.B i).left.affineOpens) (u v : Γ((P.T.B i).left, U))
    (hu : (P.T.D i ⟨2 * j.val, by omega⟩).ideal U = Ideal.span {u})
    (hv : (P.T.D i ⟨2 * j.val + 1, by omega⟩).ideal U = Ideal.span {v}) :
    ∃ a : Γ((P.T.B i).left, U),
      u - a * v ∈ (P.C.slices i).left.ker.ideal U := by
  letI := P.C.sliceImmersion i
  obtain ⟨a, ha⟩ := paired_c3_selected_adapted_equation R P i j hij U u v hu hv
  refine ⟨a, ?_⟩
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  exact ha

#print axioms paired_c3_selected_adapted_ideal
/-- The last selected branch chart supplies an ambient coefficient and an
adapted equation in the penultimate slice ideal at every retained residue point.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.7.13. -/
theorem paired_c3_selected_last_adapted_neighborhood
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r)
    (x : ComplexPoint (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))))
    (hx : x.underlying ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support) :
    ∃ (U : (P.T.B i.castSucc).left.affineOpens)
      (u v a : Γ((P.T.B i.castSucc).left, U)),
      (Point.map (P.C.slices i.castSucc) x).underlying ∈ U.1 ∧
      (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal U = Ideal.span {u} ∧
      (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = Ideal.span {v} ∧
      u - a * v ∈ (P.C.slices i.castSucc).left.ker.ideal U := by
  obtain ⟨U, u, v, hxU, hu, hv, _⟩ :=
    paired_c3_selected_last_rees_charts R P i hi x hx
  obtain ⟨a, ha⟩ := paired_c3_selected_adapted_ideal R P i.castSucc i le_rfl U u v hu hv
  exact ⟨U, u, v, a, hxU, hu, hv, ha⟩

#print axioms paired_c3_selected_last_adapted_neighborhood
end HodgeLean.Foundations.Program.ResidueSelected

import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRestrictions
import HodgeLean.Foundations.Program.G32Native.PairedC3SliceImageSmooth
import HodgeLean.Foundations.Program.G32Native.PairedC3IntersectionDimension
import HodgeLean.Foundations.Program.G32Native.EulerModel.CoordinateHyperplaneModels
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension

/-! # Smooth dimensions of the actual selected slice and its residue divisor -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24


/-- The reduced residue hyperplane retains its actual smooth relative dimension.
Source: Hartshorne, Algebraic Geometry, II.7 and III.10. -/
theorem paired_c3_residue_hyperplane_relative_dimension
    (k : ℕ) (hk : 0 < k) (j : Fin (k + 1)) :
    SmoothOfRelativeDimension (k - 1)
      ((s2e_s2b_residueIdeal k j).subschemeι ≫
        ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) := by
  obtain ⟨E⟩ := G32Native.EulerModel.residue_hyperplane_projective_model k hk j
  letI : SmoothOfRelativeDimension (k - 1)
      (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ)) :=
    s0_complex_projective_relative_dimension (k - 1)
  change SmoothOfRelativeDimension (k - 1)
    (s2c_subscheme (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
      (s2e_s2b_residueIdeal k j)).hom
  rw [← Over.w E.hom]
  change SmoothOfRelativeDimension (k - 1)
    (E.hom.left ≫ ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ))
  simpa only [zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + (k - 1))
      (E.hom.left ≫ ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ)))

/-- The actual kernel image of each retained slice is smooth of dimension k.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4;
Hartshorne, Algebraic Geometry, II.5 and III.10. -/
theorem paired_c3_selected_slice_image_dimension
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin (R.r + 1)) :
    SmoothOfRelativeDimension R.P.k
      ((P.C.slices i).left.ker.subschemeι ≫ (P.T.B i).hom) := by
  letI := P.C.sliceImmersion i
  letI : SmoothOfRelativeDimension R.P.k
      (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))).hom :=
    s0_complex_projective_relative_dimension R.P.k
  exact G32Native.paired_c3_slice_image_relative_dimension (P.C.slices i) R.P.k

/-- The penultimate centre-slice intersection has dimension k minus one,
using the retained reduced hyperplane as a scheme.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4;
Hartshorne, Algebraic Geometry, II.3 and III.10. -/
theorem paired_c3_selected_centre_slice_dimension
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    SmoothOfRelativeDimension (R.P.k - 1)
      (((P.C.slices i.castSucc).left.ker ⊔ K).subschemeι ≫ (P.T.B i.castSucc).hom) := by
  dsimp only
  letI := P.C.sliceImmersion i.castSucc
  let H := s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  have hK : K.comap (P.C.slices i.castSucc).left = H := by
    have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
    rw [Scheme.IdealSheafData.comap_sup, hp.1, hp.2, sup_idem]
  letI : SmoothOfRelativeDimension (R.P.k - 1)
      (H.subschemeι ≫ (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))).hom) :=
    paired_c3_residue_hyperplane_relative_dimension R.P.k R.P.act.cyc_positive
      (P.C.residue.indices i)
  exact G32Native.paired_c3_intersection_relative_dimension
    (P.C.slices i.castSucc) K H hK (R.P.k - 1)

#print axioms paired_c3_residue_hyperplane_relative_dimension
#print axioms paired_c3_selected_slice_image_dimension
#print axioms paired_c3_selected_centre_slice_dimension
end HodgeLean.Foundations.Program.ResidueSelected

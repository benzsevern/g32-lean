import HodgeLean.Foundations.Program.G32Native.PairedC3InitialFlagDefs
import HodgeLean.Foundations.Program.G32Native.PairedC3InitialFibreGeometry
import HodgeLean.Foundations.Program.G32Native.PairedC3SmoothConormalFlag

/-! # The stage-zero conormal flag -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
variable {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)

/-- B0.1, with B0.2 transported from the full initial Abel fibre frame.
The sequence is short exact, including injectivity at its left end.
Source: Hartshorne, Algebraic Geometry, II.8.12;
ACGH, Geometry of Algebraic Curves I, IV.1–IV.3;
`paired_c3_full_abel_fibre_conormal` for the genus-rank first term.
Checked: assembly from the retained full fibre and the natural smooth
conormal flag, with the original slice source retained. -/
theorem paired_c3_initial_flag_exact_aux (hr : 0 < R.r) :
    Nonempty (PairedC3InitialFlag R P) := by
  obtain ⟨⟨fibre, inclusion, hover, coordinates, hfibre, hinclusion, hcomp, frame⟩⟩ :=
    paired_c3_initial_fibre_geometry R P hr
  let eP := s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))
  let qbase : pairedC3Proj R.P.k ⟶ Spec ↧ℂ :=
    eP.hom ≫ ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ)
  let fbase := ProjectiveSpace.toBase (Fin (R.P.k + R.r)) (Spec ↧ℂ)
  haveI : Smooth (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ)) :=
    paired_c3_projective_smooth (R.P.k + 1) (by omega)
  haveI : Smooth qbase := by
    dsimp only [qbase]
    infer_instance
  haveI : Smooth fbase := paired_c3_projective_smooth (R.P.k + R.r) (by omega)
  haveI : Smooth (P.T.B 0).hom := P.T.inst21 0
  have hj : inclusion ≫ fbase = qbase := by
    change inclusion ≫ ProjectiveSpace.toBase (Fin (R.P.k + R.r)) (Spec ↧ℂ) = _
    rw [← hover, ← Category.assoc, hcomp, Category.assoc, Over.w (P.C.slices 0)]
    rfl
  haveI : IsClosedImmersion fibre := hfibre
  haveI : IsClosedImmersion inclusion := hinclusion
  let f : (Scheme.Modules.pullback inclusion).obj (s2c_conormal fibre) ⟶
      s2c_conormal (inclusion ≫ fibre) :=
    Conormal.comparisonMap fibre (inclusion ≫ fibre) (𝟙 _) inclusion
      (by rw [Category.comp_id])
  let g : s2c_conormal (inclusion ≫ fibre) ⟶ s2c_conormal inclusion :=
    ((Scheme.Modules.pullbackId _).app (s2c_conormal (inclusion ≫ fibre))).inv ≫
      Conormal.comparisonMap (inclusion ≫ fibre) inclusion fibre (𝟙 _)
        (by rw [Category.id_comp])
  have hseq : ∃ w : f ≫ g = 0, (ShortComplex.mk f g w).ShortExact :=
    paired_c3_smooth_conormal_flag_aux (pairedC3Proj R.P.k)
      (ProjectiveSpace (Fin (R.P.k + R.r)) (Spec ↧ℂ)) (P.T.B 0).left
      qbase fbase (P.T.B 0).hom fibre inclusion hover hj
  obtain ⟨w, hw⟩ := hseq
  let seq : ShortComplex (pairedC3Proj R.P.k).Modules := ShortComplex.mk f g w
  refine ⟨{
    fibre := fibre
    inclusion := inclusion
    linearCoordinates := coordinates
    fibreImmersion := hfibre
    inclusionImmersion := hinclusion
    comp := hcomp
    sequence := seq
    exact := hw
    leftTerm := Iso.refl ((Scheme.Modules.pullback inclusion).obj (s2c_conormal fibre))
    middleTerm := Iso.refl (s2c_conormal (inclusion ≫ fibre))
    stageTerm := ?_
    rightTerm := Iso.refl (s2c_conormal inclusion)
    firstMap := (Category.comp_id f).trans (Category.id_comp f).symm
    secondMap := (Category.comp_id g).trans (Category.id_comp g).symm
    fullFibreFrame := frame }⟩
  exact eqToIso (congrArg (fun a => s2c_conormal a) hcomp) ≪≫
    (s2e_conormal_source_iso (P.C.slices 0).left eP).symm

end HodgeLean.Foundations.Program.G32Native

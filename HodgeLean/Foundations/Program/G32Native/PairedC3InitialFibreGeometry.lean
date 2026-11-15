import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveFactorCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3InitialFullFibre
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import HodgeLean.Foundations.Program.SchoenCycleC2ConormalIsoHelpers

/-! # Retaining the stage-zero full fibre and its slice inclusion -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6
  G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst18
variable {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The full initial fibre geometry, before forming its conormal flag.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(ii). -/
structure PairedC3InitialFibreGeometry where
  fibre : ProjectiveSpace (Fin (R.P.k + R.r)) (Spec ↧ℂ) ⟶ (P.T.B 0).left
  inclusion : pairedC3Proj R.P.k ⟶ ProjectiveSpace (Fin (R.P.k + R.r)) (Spec ↧ℂ)
  fibreOver : fibre ≫ (P.T.B 0).hom =
    ProjectiveSpace.toBase (Fin (R.P.k + R.r)) (Spec ↧ℂ)
  linearCoordinates : PairedC3ProjectiveFactorCoordinates R.P.k (R.P.k + R.r - 1) _
    ((s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))).inv ≫ inclusion)
  fibreImmersion : IsClosedImmersion fibre
  inclusionImmersion : IsClosedImmersion inclusion
  comp : inclusion ≫ fibre =
    (s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))).hom ≫ (P.C.slices 0).left
  fullFibreFrame : s2c_conormal fibre ≅
    (SheafOfModules.free (R :=
      (ProjectiveSpace (Fin (R.P.k + R.r)) (Spec ↧ℂ)).ringCatSheaf)
      (Fin (R.P.k + 1 - R.r)))

/-- Transport the full-system factorization to the supplied stage-zero
ambient scheme and to the polynomial projective slice.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(ii). -/
theorem paired_c3_initial_fibre_geometry (hr : 0 < R.r) :
    Nonempty (PairedC3InitialFibreGeometry R P) := by
  let γ := eqToHom (congrArg (g3_power R.Z) R.hselected.symm) ≫ R.γ
  obtain ⟨hγ, hsurj, hquot⟩ := s2e_symmetric_quotient_reindex R.Z R.B₀
    (R.h + 1) (2 * R.P.k) R.hselected.symm R.γ R.hγinv R.hγsurj R.hγ
  haveI : IsFinite γ.left := by dsimp only [γ, Over.comp_left]; infer_instance
  haveI : IsClosedImmersion (P.C.slices 0).left := P.C.sliceImmersion 0
  let ℓ := P.C.slices 0 ≫ P.T.e₀.hom
  haveI : IsClosedImmersion ℓ.left := by dsimp only [ℓ, Over.comp_left]; infer_instance
  obtain ⟨f, hf, ⟨ef⟩, i, hi, hcomp, ⟨coords⟩⟩ := paired_c3_initial_full_fibre_marked R.Z R.B₀
    R.P.k R.r hr _ _ γ hγ hsurj hquot ℓ P.C.residue
  let eP := s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))
  let eB := (Over.forget (Spec ↧ℂ)).mapIso P.T.e₀.symm
  let fibre := f.left ≫ eB.hom
  let inc := eP.hom ≫ i.left
  haveI : IsClosedImmersion f.left := hf
  haveI : IsClosedImmersion i.left := hi
  refine ⟨{
    fibre := fibre
    inclusion := inc
    fibreOver := by
      change (f.left ≫ P.T.e₀.inv.left) ≫ (P.T.B 0).hom = _
      rw [Category.assoc, Over.w P.T.e₀.inv, Over.w f]
      rfl
    linearCoordinates := by
      change PairedC3ProjectiveFactorCoordinates R.P.k (R.P.k + R.r - 1) _
        (eP.inv ≫ (eP.hom ≫ i.left))
      rw [eP.inv_hom_id_assoc]
      exact coords
    fibreImmersion := inferInstance
    inclusionImmersion := inferInstance
    comp := ?_
    fullFibreFrame := s2e_conormal_target_iso f.left eB ≪≫ ef }⟩
  have heB : P.T.e₀.hom.left ≫ P.T.e₀.inv.left = 𝟙 _ :=
    congrArg Over.Hom.left P.T.e₀.hom_inv_id
  change (eP.hom ≫ i.left) ≫ (f.left ≫ P.T.e₀.inv.left) =
    eP.hom ≫ (P.C.slices 0).left
  have h := congrArg (fun t => eP.hom ≫ t.left ≫ P.T.e₀.inv.left) hcomp
  simpa only [ℓ, Over.comp_left, Category.assoc, heB, Category.comp_id] using h

#print axioms paired_c3_initial_fibre_geometry
end HodgeLean.Foundations.Program.G32Native

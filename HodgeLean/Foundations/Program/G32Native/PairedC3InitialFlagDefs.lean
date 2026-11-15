import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveFactorCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects

/-! # The stage-zero conormal flag -/
noncomputable section
set_option maxHeartbeats 400000
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

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Geometric maps and the exact conormal sequence on the original slice.
The fibre dimension is k+r-1, rather than the selected dimension k.
Source: Hartshorne, Algebraic Geometry, II.8.12;
Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(ii). -/
structure PairedC3InitialFlag where
  fibre : ProjectiveSpace (Fin (R.P.k + R.r)) (Spec ↧ℂ) ⟶ (P.T.B 0).left
  inclusion : pairedC3Proj R.P.k ⟶ ProjectiveSpace (Fin (R.P.k + R.r)) (Spec ↧ℂ)
  linearCoordinates : PairedC3ProjectiveFactorCoordinates R.P.k (R.P.k + R.r - 1) _
    ((s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))).inv ≫ inclusion)
  fibreImmersion : IsClosedImmersion fibre
  inclusionImmersion : IsClosedImmersion inclusion
  comp : inclusion ≫ fibre =
    (s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))).hom ≫ (P.C.slices 0).left
  sequence : ShortComplex (pairedC3Proj R.P.k).Modules
  exact : sequence.ShortExact
  leftTerm : sequence.X₁ ≅ (Scheme.Modules.pullback inclusion).obj (s2c_conormal fibre)
  middleTerm : sequence.X₂ ≅ s2c_conormal (inclusion ≫ fibre)
  stageTerm : sequence.X₂ ≅ pairedC3StageConormal P 0
  rightTerm : sequence.X₃ ≅ s2c_conormal inclusion
  firstMap : sequence.f ≫ middleTerm.hom = leftTerm.hom ≫
    Conormal.comparisonMap fibre (inclusion ≫ fibre) (𝟙 _) inclusion
      (by rw [Category.comp_id])
  secondMap : sequence.g ≫ rightTerm.hom = middleTerm.hom ≫
    ((Scheme.Modules.pullbackId _).app (s2c_conormal (inclusion ≫ fibre))).inv ≫
      Conormal.comparisonMap (inclusion ≫ fibre) inclusion fibre (𝟙 _)
        (by rw [Category.id_comp])
  fullFibreFrame : s2c_conormal fibre ≅
    (SheafOfModules.free (R :=
      (ProjectiveSpace (Fin (R.P.k + R.r)) (Spec ↧ℂ)).ringCatSheaf)
      (Fin (R.P.k + 1 - R.r)))

/-- B0.2: restrict the retained full-fibre frame to the selected slice. -/
def PairedC3InitialFlag.fibreFrame (F : PairedC3InitialFlag R P) :
    (Scheme.Modules.pullback F.inclusion).obj (s2c_conormal F.fibre) ≅
      pairedC3SplitBundle R.P.k (R.P.k + 1 - R.r) 0 :=
  (Scheme.Modules.pullback F.inclusion).mapIso F.fullFibreFrame ≪≫
    SheafOfModules.pullbackObjFreeIso F.inclusion.toRingCatSheafHom
      (Fin (R.P.k + 1 - R.r))


end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.G32Native.PairedC3InitialFlagDefs
import HodgeLean.Foundations.Program.G32Native.PairedC3FactorCoordinateDimension

/-! # Coordinate normalization of the supplied full-fibre inclusion -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
variable {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)

/-- Normalize the actual inclusion by changing coordinates on its full
fibre. The source parameterization is retained literally. The ambient
isomorphism is a scheme isomorphism, since the flag's maps are not stated
over the coefficient spectrum.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(ii);
Hartshorne, Algebraic Geometry, II.7.1, projective linear coordinates. -/
theorem paired_c3_initial_flag_coordinate_normalization_aux (hr : 0 < R.r)
    (F : PairedC3InitialFlag R P) :
    ∃ e : ProjectiveSpace (Fin (R.P.k + R.r)) (Spec ↧ℂ) ≅
        ProjectiveSpace (Fin (R.P.k + R.r)) (Spec ↧ℂ),
      F.inclusion ≫ e.hom = pairedC3InitialCoordinateInclusion R.P.k R.r hr := by
  have hn : R.P.k + R.r - 1 + 1 = R.P.k + R.r := by omega
  obtain ⟨e, he⟩ := paired_c3_factor_coordinate_normalization_of_dimension hn _
    F.linearCoordinates (pairedC3InitialCoordinateEmbedding R.P.k R.r hr)
  refine ⟨e, ?_⟩
  have h := congrArg (fun f => (s2_polynomialProjectiveSpaceIso ℂ
    (Fin (R.P.k + 1))).hom ≫ f) he
  simpa only [Category.assoc, Iso.hom_inv_id_assoc,
    pairedC3InitialCoordinateInclusion] using h

end HodgeLean.Foundations.Program.G32Native

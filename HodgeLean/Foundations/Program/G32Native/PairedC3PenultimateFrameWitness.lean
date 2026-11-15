import HodgeLean.Foundations.Program.G32Native.PairedC3PenultimateFrame
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected

/-- A witness of the retained penultimate frame.
Source: Schoen, Compositio Mathematica 65 (1988), proof of Lemma 2.4;
Hartshorne, Algebraic Geometry, III, Theorem 5.1. -/
theorem paired_c3_penultimate_frame_witness
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (last : Fin R.r) (hlast : last.val + 1 = R.r) :
    Nonempty (s2c_conormal (P.C.slices last.castSucc).left ≅
      (SheafOfModules.free (R :=
        (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)).ringCatSheaf)
        (Fin R.P.k) :
        (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)).Modules)) := by
  exact ⟨pairedC3PenultimateFrame R P last hlast⟩

#print axioms paired_c3_penultimate_frame_witness
end HodgeLean.Foundations.Program.G32Native

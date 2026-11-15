import HodgeLean.Foundations.Program.SchoenCycleC1RationalPullbackSquare
import HodgeLean.Foundations.Program.SchoenCycleC1AutomorphismLocalSquare
import HodgeLean.Foundations.Program.SchoenCycleC1RationalPullbackScalars

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- An upstairs rational eigenidentity descends to the specified residual
scheme generator through its actual quotient square. -/
theorem s2e_c1_rational_deck_eigenvalue_descent
    (X W : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral W.left]
    (q : X ⟶ W) (A : X ⟶ X) [IsIso A] (d : W ⟶ W) [IsIso d]
    (hgen : q ≫ d = A ≫ q)
    (qstar : W.left.functionField →+* X.left.functionField)
    (hqstar : ∀ x (r : W.left.presheaf.stalk (q.left x)),
      qstar (algebraMap (W.left.presheaf.stalk (q.left x)) W.left.functionField r) =
        algebraMap (X.left.presheaf.stalk x) X.left.functionField ((q.left.stalkMap x).hom r))
    (z : W.left.functionField) (η : ℂ)
    (heig : s2e_step1_fieldPullback X.left A.left (qstar z) =
      HodgeLean.Foundations.Curves.stalkC (genericPoint X.left) η * qstar z) :
    s2e_step1_fieldPullback W.left d.left z =
      HodgeLean.Foundations.Curves.stalkC (genericPoint W.left) η * z := by
  have hsq : A.left ≫ q.left = q.left ≫ d.left := congrArg Over.Hom.left hgen.symm
  have hcomm := s2e_c1_rational_pullback_square A.left q.left q.left d.left hsq
    (s2e_step1_fieldPullback X.left A.left) qstar qstar
    (s2e_step1_fieldPullback W.left d.left)
    (s2e_c1_automorphism_rational_local_square X.left A.left) hqstar hqstar
    (s2e_c1_automorphism_rational_local_square W.left d.left)
  have heval := RingHom.congr_fun hcomm z
  change s2e_step1_fieldPullback X.left A.left (qstar z) =
    qstar (s2e_step1_fieldPullback W.left d.left z) at heval
  apply qstar.injective
  rw [← heval, heig, map_mul, s2e_c1_rational_pullback_complex_scalars X W q qstar hqstar]

end HodgeLean.Foundations.Program

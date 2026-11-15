import HodgeLean.Foundations.Program.SchoenTowerFibreDefs
import HodgeLean.Foundations.Program.SchoenExceptional
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s2v_projective_points_proper (E K : Over (Spec ↧ℂ))
    [IsProjective E.hom] [IsProjective K.hom] (p : E ⟶ K) :
    IsProperMap (s2c_points.map p) :=
  (Point.continuousMap p).continuous.isProperMap

theorem s2v_projective_sheaf_descent (E K : Over (Spec ↧ℂ))
    [IsProjective E.hom] [IsProjective K.hom] (p : E ⟶ K)
    (F : TopCat.Sheaf AddCommGrpCat (s2c_points.obj E))
    (hF : ∀ (k : ComplexPoint K) (n : ℕ), Subsingleton
      (Sheaf.H ((TopCat.Sheaf.pullback AddCommGrpCat
        (s3_fibreInclusion (s2c_points.map p) k)).obj F) n)) (n : ℕ) :
    Subsingleton (Sheaf.H F n) := by
  letI : T2Space (s2c_points.obj E) := inferInstanceAs (T2Space (ComplexPoint E))
  letI : T2Space (s2c_points.obj K) := inferInstanceAs (T2Space (ComplexPoint K))
  letI : CompactSpace (s2c_points.obj E) := inferInstanceAs (CompactSpace (ComplexPoint E))
  letI : CompactSpace (s2c_points.obj K) := inferInstanceAs (CompactSpace (ComplexPoint K))
  exact s3_proper_fibre_vanishing (s2c_points.obj E) (s2c_points.obj K)
    (s2c_points.map p) (s2v_projective_points_proper E K p) F hF n

end HodgeLean.Foundations.Program

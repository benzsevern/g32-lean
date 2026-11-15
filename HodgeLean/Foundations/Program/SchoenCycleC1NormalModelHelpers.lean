import HodgeLean.Foundations.AlgebraicGeometry.Normalization.ModelComparison
import HodgeLean.Foundations.Program.SchoenBirationalFactor
import Mathlib.AlgebraicGeometry.Normalization

/-! # Identification of finite normal models with relative normalizations -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An integral normal model with the prescribed generic field identifies the
actual relative normalization, retaining both structure maps. -/
theorem s2e_c1_normalization_iso_of_normal_model
    {T X B : Scheme.{0}} [IsIntegral T] [IsIntegral X]
    (f : T ⟶ B) [QuasiCompact f] [QuasiSeparated f]
    (j : T ⟶ X) [IsDominant j] (π : X ⟶ B) [IsIntegralHom π]
    (h : f = j ≫ π) (hnormal : zmtiso_IsNormal X)
    (hgeneric : zmtiso_IsBirational j) :
    ∃ E : f.normalization ≅ X,
      f.toNormalization ≫ E.hom = j ∧ E.hom ≫ π = f.fromNormalization := by
  exact AlgebraicGeometry.Normalization.modelComparison f j π h hnormal hgeneric

end HodgeLean.Foundations.Program

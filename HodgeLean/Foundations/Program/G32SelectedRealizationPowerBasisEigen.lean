import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.FieldTheory.Perfect

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_powerBasis_eigenspace_dimension {F : Type*} [Field F] [Algebra ℚ F]
    [FiniteDimensional ℚ F] (pb : PowerBasis ℚ F) (σ : F →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (Module.End.eigenspace
      ((Algebra.lmul ℚ F pb.gen).baseChange ℂ) (σ pb.gen)) = 1 := by
  classical
  let T := Algebra.lmul ℚ F pb.gen
  have hchar : T.charpoly = minpoly ℚ pb.gen := by
    rw [← LinearMap.charpoly_toMatrix T pb.basis]
    exact charpoly_leftMulMatrix pb
  have hC : (T.baseChange ℂ).charpoly =
      (minpoly ℚ pb.gen).map (algebraMap ℚ ℂ) := by
    rw [LinearMap.charpoly_baseChange, hchar]
  have hsep : ((minpoly ℚ pb.gen).map (algebraMap ℚ ℂ)).Separable :=
    Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ pb.gen)
  have hle := LinearMap.finrank_eigenspace_le (T.baseChange ℂ) (σ pb.gen)
  rw [hC] at hle
  have hupper := Polynomial.rootMultiplicity_le_one_of_separable hsep (σ pb.gen)
  have hroot : ((minpoly ℚ pb.gen).map (algebraMap ℚ ℂ)).IsRoot (σ pb.gen) := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    exact minpoly.aeval_algHom ℚ σ pb.gen
  have heig := (Module.End.hasEigenvalue_iff_isRoot_charpoly (T.baseChange ℂ) _).mpr
    (hC.symm ▸ hroot)
  have hn : Nontrivial (Module.End.eigenspace (T.baseChange ℂ) (σ pb.gen)) :=
    Submodule.nontrivial_iff_ne_bot.mpr heig
  have hpos : 0 < Module.finrank ℂ (Module.End.eigenspace (T.baseChange ℂ) (σ pb.gen)) :=
    Module.finrank_pos_iff.mpr hn
  change Module.finrank ℂ (Module.End.eigenspace (T.baseChange ℂ) (σ pb.gen)) = 1
  omega

end HodgeLean.Foundations.Program

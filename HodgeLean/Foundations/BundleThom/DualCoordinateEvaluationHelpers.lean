import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Analysis.Complex.Basic

/-! # Evaluation in finite dual coordinates

The evaluation formula keeps the original basis and its actual coordinate functionals.
HC no distance; AV milestone no distance. -/

noncomputable section
open Module
namespace HodgeLean.Foundations.BundleThom

/-- Evaluation of an inverse dual-coordinate vector is the finite coordinate pairing.
Source: Hartshorne, Algebraic Geometry, II.8, dual normal and conormal coordinates. -/
theorem i1_dualCoordinateEvaluation {M : Type*} [AddCommGroup M] [Module ℂ M]
    (k : ℕ) (b : Basis (Fin k) ℂ M) (c : Fin k → ℂ) (m : M) :
    b.dualBasis.equivFun.symm c m = ∑ i, c i * b.repr m i := by
  rw [Basis.equivFun_symm_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Basis.dualBasis_apply]

end HodgeLean.Foundations.BundleThom

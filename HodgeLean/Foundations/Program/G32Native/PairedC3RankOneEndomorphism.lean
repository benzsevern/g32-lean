import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Frame-independent scalar coefficients of a rank-one endomorphism -/
noncomputable section
namespace HodgeLean.Foundations.Program.G32Native
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A rank-one endomorphism is multiplication by its actual frame coefficient. -/
theorem paired_c3_rank_one_end_apply (e : R ≃ₗ[R] V) (f : V →ₗ[R] V) (x : V) :
    f x = e.symm (f (e 1)) • x := by
  let g : R →ₗ[R] R := e.symm.toLinearMap.comp (f.comp e.toLinearMap)
  have hg (r : R) : g r = r * g 1 := by
    simpa only [smul_eq_mul, mul_one] using g.map_smul r 1
  apply e.symm.injective
  have hx : e.symm (f x) = g (e.symm x) := by
    dsimp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e.apply_symm_apply]
  rw [hx, hg, e.symm.map_smul]
  exact mul_comm _ _

/-- Changing the frame retains the scalar coefficient of an endomorphism. -/
theorem paired_c3_rank_one_end_coefficient_independent
    (e d : R ≃ₗ[R] V) (f : V →ₗ[R] V) :
    e.symm (f (e 1)) = d.symm (f (d 1)) := by
  have h := (paired_c3_rank_one_end_apply e f (e 1)).symm.trans
    (paired_c3_rank_one_end_apply d f (e 1))
  have hh := congrArg e.symm h
  simpa only [e.symm.map_smul, e.symm_apply_apply, smul_eq_mul, mul_one] using hh

end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.BundleThom.AnalyticNormalDefs
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Finite coordinates for the pointwise dual topology

A finite conormal basis identifies the specified normal fibre topology with the complex model.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.BundleThom

variable {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V)
variable (x : ComplexPoint Q) (k : ℕ)
private local instance : TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x

/-- Dual coordinates of a finite conormal basis respect the fixed pointwise topology.
Source: Hartshorne, Algebraic Geometry, II.8, normal-conormal duality; finite-dimensional duality. -/
def i1_normalBasisHomeomorph (b : Module.Basis (Fin k) ℂ (i1_conormalFibre j x)) :
    i1_normalFibre j x ≃ₜ (Fin k → ℂ) where
  toEquiv := b.dualBasis.equivFun.toEquiv
  continuous_toFun := by
    apply continuous_pi
    intro i
    change Continuous (fun f : i1_normalFibre j x => b.dualBasis.equivFun f i)
    simp only [Module.Basis.dualBasis_equivFun]
    exact (continuous_apply (b i)).comp continuous_induced_dom
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro m
    have heq : (fun y : Fin k → ℂ => b.dualBasis.equivFun.symm y m) =
        (fun y : Fin k → ℂ => ∑ i, y i * b.dualBasis i m) := by
      funext y
      rw [Module.Basis.equivFun_symm_apply]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    change Continuous (fun y : Fin k → ℂ => b.dualBasis.equivFun.symm y m)
    rw [heq]
    exact continuous_finsetSum _ (fun i _ => (continuous_apply i).mul_const _)

end HodgeLean.Foundations.BundleThom

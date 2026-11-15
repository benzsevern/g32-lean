import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section
namespace HodgeLean.Foundations.Program

def g32y_pointwise_eigenspace_equiv {K V W I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (E : V ≃ₗ[K] (I → W)) (A : Module.End K V) (T : Module.End K W)
    (h : ∀ v i, E (A v) i = T (E v i)) (μ : K) :
    Module.End.eigenspace A μ ≃ₗ[K] (I → Module.End.eigenspace T μ) where
  toFun v i := ⟨E v i, Module.End.mem_eigenspace_iff.mpr (by
    rw [← h]
    have hh := congrArg (fun z ↦ E z i) (Module.End.mem_eigenspace_iff.mp v.property)
    simpa only [map_smul, Pi.smul_apply] using hh)⟩
  invFun w := ⟨E.symm (fun i ↦ (w i : W)), Module.End.mem_eigenspace_iff.mpr (by
    apply E.injective
    ext i
    rw [map_smul, Pi.smul_apply, h, E.apply_symm_apply]
    exact Module.End.mem_eigenspace_iff.mp (w i).property)⟩
  left_inv v := by
    apply Subtype.ext
    exact E.symm_apply_apply v
  right_inv w := by
    funext i
    apply Subtype.ext
    exact congrFun (E.apply_symm_apply (fun i ↦ (w i : W))) i
  map_add' v w := by
    ext i
    exact congrFun (E.map_add v w) i
  map_smul' c v := by
    ext i
    exact congrFun (E.map_smul c v) i

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Abdulali.SignCharacterDecomposition
import Mathlib.LinearAlgebra.TensorProduct.Basic

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Abdulali

/-- A normalized vector and covector of the same sign character identify its sector
with a contraction of ordinary fixed tensors after adjoining one determinant factor.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17, reduction of the determinant
sector to full orthogonal invariants by adjoining the top alternating tensor. -/
theorem sign_sector_eq_contracted_fixed
    {G T D : Type*} [Monoid G] [AddCommGroup T] [Module ℂ T]
    [AddCommGroup D] [Module ℂ D]
    (ρ : G →* Module.End ℂ T) (σ : G →* Module.End ℂ D)
    (χ : G →* ℂ) (hχ : ∀ g, χ g * χ g = 1)
    (e : D) (f : D →ₗ[ℂ] ℂ) (hfe : f e = 1)
    (he : ∀ g, σ g e = χ g • e)
    (hf : ∀ g d, f (σ g d) = χ g * f d) :
    let C : T ⊗[ℂ] D →ₗ[ℂ] T :=
      (TensorProduct.rid ℂ T).toLinearMap.comp (TensorProduct.map LinearMap.id f)
    (⨅ g : G, LinearMap.ker (TensorProduct.map (ρ g) (σ g) - LinearMap.id)).map C =
      ⨅ g : G, LinearMap.ker (ρ g - χ g • LinearMap.id) := by
  classical
  dsimp only
  let C : T ⊗[ℂ] D →ₗ[ℂ] T :=
    (TensorProduct.rid ℂ T).toLinearMap.comp (TensorProduct.map LinearMap.id f)
  have hC (t : T) (d : D) : C (t ⊗ₜ[ℂ] d) = f d • t := rfl
  have hcov (g : G) (z : T ⊗[ℂ] D) :
      C (TensorProduct.map (ρ g) (σ g) z) = χ g • ρ g (C z) := by
    have hh : C.comp (TensorProduct.map (ρ g) (σ g)) =
        χ g • (ρ g).comp C := by
      ext t d
      change C (TensorProduct.map (ρ g) (σ g) (t ⊗ₜ[ℂ] d)) =
        χ g • ρ g (C (t ⊗ₜ[ℂ] d))
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.smul_apply,
        hC, hf, map_smul, mul_smul, smul_comm (f d) (χ g)]
    exact LinearMap.congr_fun hh z
  apply le_antisymm
  · rintro t ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hz
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro g
    have hh := hcov g z
    rw [hz g] at hh
    have hh' := congrArg (fun t : T => χ g • t) hh
    rw [smul_smul, hχ g, one_smul] at hh'
    exact hh'.symm
  · intro t ht
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at ht
    refine ⟨t ⊗ₜ[ℂ] e, ?_, ?_⟩
    · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      rw [TensorProduct.map_tmul, ht g, he g]
      simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul,
        smul_smul, hχ g, one_smul]
    · change C (t ⊗ₜ[ℂ] e) = t
      rw [hC, hfe, one_smul]

end HodgeLean.Foundations.Abdulali

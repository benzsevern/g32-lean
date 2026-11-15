import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Field.Rat

/-! # Tensoring a scalar generator with a rational vector space

A scalar basis of the first factor gives the actual pure-tensor insertion
as a bijection for every second factor.
HC no distance; AV milestone no distance. -/

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.BundleResolution

theorem i1_tensorGenerator_bijective {V W : Type} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (u : V)
    (hu : Function.Bijective (LinearMap.toSpanSingleton ℚ V u)) :
    Function.Bijective (TensorProduct.mk ℚ V W u) := by
  let eV := LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℚ V u) hu
  let e : W ≃ₗ[ℚ] V ⊗[ℚ] W := (TensorProduct.lid ℚ W).symm.trans
    (TensorProduct.congr eV (LinearEquiv.refl ℚ W))
  have he : (fun w : W => u ⊗ₜ[ℚ] w) = (e : W → V ⊗[ℚ] W) := by
    funext w
    dsimp only [e, LinearEquiv.trans_apply]
    rw [TensorProduct.lid_symm_apply, TensorProduct.congr_tmul]
    change u ⊗ₜ[ℚ] w = (1 : ℚ) • u ⊗ₜ[ℚ] w
    rw [one_smul]
  change Function.Bijective (fun w : W => u ⊗ₜ[ℚ] w)
  rw [he]
  exact e.bijective

end HodgeLean.Foundations.BundleResolution

import HodgeLean.Blocks.Weil.RationalKernel

noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

open HodgeBlocks HodgeBlocks.WeilAction

theorem g32c_exterior_baseChange_tmul {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (n : ℕ) (a : ℂ) (v : ⋀[ℚ]^n V) :
    exteriorPowerBaseChangeEquiv n (a ⊗ₜ[ℚ] v) = a • complexifyWedge n v := by
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, exteriorPowerBaseChangeEquiv_tmul]

theorem g32c_exterior_baseChange_natural {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    [AddCommGroup W] [Module ℚ W] [Module.Finite ℚ W]
    (n : ℕ) (f : V →ₗ[ℚ] W) :
    (exteriorPowerBaseChangeEquiv (V := W) n).toLinearMap ∘ₗ
        (exteriorPower.map n f).baseChange ℂ =
      exteriorPower.map n (f.baseChange ℂ) ∘ₗ
        (exteriorPowerBaseChangeEquiv (V := V) n).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
    g32c_exterior_baseChange_tmul, map_smul, complexifyWedge_exteriorPower_map]

theorem g32c_exterior_baseChange_symm_natural {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    [AddCommGroup W] [Module ℚ W] [Module.Finite ℚ W]
    (n : ℕ) (f : V →ₗ[ℚ] W) (w : ⋀[ℂ]^n (ℂ ⊗[ℚ] V)) :
    (exteriorPower.map n f).baseChange ℂ ((exteriorPowerBaseChangeEquiv n).symm w) =
      (exteriorPowerBaseChangeEquiv n).symm (exteriorPower.map n (f.baseChange ℂ) w) := by
  apply (exteriorPowerBaseChangeEquiv (V := W) n).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := LinearMap.congr_fun (g32c_exterior_baseChange_natural n f)
    ((exteriorPowerBaseChangeEquiv n).symm w)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h

end HodgeLean.Foundations.Program

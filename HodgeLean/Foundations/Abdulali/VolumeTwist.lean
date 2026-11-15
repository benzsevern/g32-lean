import HodgeLean.Foundations.Abdulali.VolumeTensor
import HodgeLean.Foundations.Program.MilneTensorHelpers

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations HodgeLean.Foundations.Program

/-- Appending the nonzero volume tensor changes the determinant sector into
the fixed sector for every operator whose determinant has square one.
The normalization uses the actual determinant pairing `d!`.
Source: Weyl, The Classical Groups, Chapter II, §9; Procesi, Lie Groups,
Chapter 11, §2 (reduction of SO invariant theory to O and the determinant). -/
theorem volume_twist_fixed_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (n : ℕ) (u : Module.End ℂ V) (hu : u.det ^ 2 = 1)
    (t : ⨂[ℂ]^n V) :
    SchurWeyl.tensorPow (Fin n) u t = u.det • t ↔
      SchurWeyl.tensorPow (Fin (n + Module.finrank ℂ V)) u
        (InvariantsExterior.tensorAppend n (Module.finrank ℂ V)
          (t ⊗ₜ[ℂ] SchurWeyl.detTensorDual ℂ V)) =
      InvariantsExterior.tensorAppend n (Module.finrank ℂ V)
        (t ⊗ₜ[ℂ] SchurWeyl.detTensorDual ℂ V) := by
  let T := ⨂[ℂ]^n V
  let ε := SchurWeyl.detTensorDual ℂ V
  let δ := PiTensorProduct.dualDistrib (SchurWeyl.detTensor ℂ V)
  let C : T ⊗[ℂ] (⨂[ℂ]^(Module.finrank ℂ V) V) →ₗ[ℂ] T :=
    (TensorProduct.rid ℂ T).toLinearMap.comp (δ.lTensor T)
  have hc (x : T) : C (x ⊗ₜ[ℂ] ε) = ((Module.finrank ℂ V).factorial : ℂ) • x := by
    simp [C, ε, δ, SchurWeyl.dualDistrib_detTensor_detTensorDual]
  have hinj : Function.Injective (fun x : T => x ⊗ₜ[ℂ] ε) := by
    intro x y h
    have hh := congrArg C h
    rw [hc, hc] at hh
    have hf : ((Module.finrank ℂ V).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (Module.finrank ℂ V)
    have hhh := congrArg (fun z : T => ((Module.finrank ℂ V).factorial : ℂ)⁻¹ • z) hh
    simpa only [smul_smul, inv_mul_cancel₀ hf, one_smul] using hhh
  rw [m1b_tensorPow_append, volume_tensor_character,
    (InvariantsExterior.tensorAppend n (Module.finrank ℂ V)).injective.eq_iff,
    TensorProduct.tmul_smul]
  change SchurWeyl.tensorPow (Fin n) u t = u.det • t ↔
    (u.det • SchurWeyl.tensorPow (Fin n) u t) ⊗ₜ[ℂ] ε = t ⊗ₜ[ℂ] ε
  rw [hinj.eq_iff]
  constructor
  · intro h
    rw [h, smul_smul, ← pow_two, hu, one_smul]
  · intro h
    have hh := congrArg (fun z => u.det • z) h
    simpa only [smul_smul, ← pow_two, hu, one_smul] using hh

end HodgeLean.Foundations.Abdulali

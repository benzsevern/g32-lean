import HodgeLean.Foundations.Program.MilneTensorDefs
import HodgeLean.Foundations.Program.MilneCentralizerProofs
import HodgeLean.Foundations.Program.G32Native.PaperExteriorPolynomial

noncomputable section
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- The alternating quotient has a simultaneous equivariant section for every
set of endomorphisms, including noninvertible operators and degree zero. -/
theorem exterior_fixed_iff_mem_fixed_tensor_image
    {M : Type*} [AddCommGroup M] [Module ℂ M]
    (S : Set (Module.End ℂ M)) (n : ℕ) (v : ⋀[ℂ]^n M) :
    (∀ u ∈ S, exteriorPower.map n u v = v) ↔
      v ∈ (m1b_fixed S n).map (InvariantsExterior.wedgeQuotient n) := by
  constructor
  · intro hv
    refine Submodule.mem_map.mpr ⟨(n.factorial : ℂ)⁻¹ • exteriorPower.toTensorPower ℂ M n v, ?_, ?_⟩
    · simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      intro u hu
      rw [map_smul]
      change (n.factorial : ℂ)⁻¹ •
        (PiTensorProduct.map (fun _ : Fin n => u))
          (exteriorPower.toTensorPower ℂ M n v) = _
      have hn := LinearMap.congr_fun (m0_tensor_natural n u) v
      simp only [LinearMap.comp_apply] at hn
      rw [hn, hv u hu]
    · rw [map_smul, InvariantsExterior.wedgeQuotient_toTensorPower, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]
  · intro hv u hu
    obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hv
    simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at ht
    rw [← G32Native.paperExterior_wedgeQuotient_tensorPow, ht u hu]

end HodgeLean.Foundations.Abdulali

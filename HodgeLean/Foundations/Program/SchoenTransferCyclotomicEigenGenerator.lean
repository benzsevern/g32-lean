import HodgeLean.Foundations.Program.SchoenTransferCharacterSuppliers
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Any primitive generator determines all simultaneous cyclotomic scalar eigenvectors. -/
theorem s4_cyclotomic_eigenspace_primitive_generator
    {V : Type*} [AddCommGroup V] [Module ℚ V] {m d : ℕ} [NeZero m]
    (e : V ≃ₗ[ℚ] (Fin d → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ)
    (ζ : cyc_Field m) (hζ : IsPrimitiveRoot ζ m) :
    cyc_eigenspace e t = Module.End.eigenspace ((cyc_scalar e ζ).baseChange ℂ) (t ζ) := by
  let pb := hζ.powerBasis ℚ
  apply le_antisymm
  · exact iInf_le _ ζ
  · intro v hv
    simp only [cyc_eigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro a
    obtain ⟨p, hp⟩ := pb.exists_eq_aeval' a
    have hgen : pb.gen = ζ := hζ.powerBasis_gen ℚ
    rw [hgen] at hp
    let ρ : cyc_Field m →ₐ[ℚ] Module.End ℂ (ℂ ⊗[ℚ] V) :=
      (Module.End.baseChangeHom ℚ ℂ V).comp (cyc_rep e)
    have ha : (cyc_scalar e a).baseChange ℂ =
        Polynomial.aeval ((cyc_scalar e ζ).baseChange ℂ) (p.map (algebraMap ℚ ℂ)) := by
      change ρ a = _
      rw [hp, ← Polynomial.aeval_algHom_apply]
      exact Polynomial.aeval_eq_aeval_map
        (IsScalarTower.algebraMap_eq ℚ ℂ (Module.End ℂ (ℂ ⊗[ℚ] V))).symm p (ρ ζ)
    have hs : (p.map (algebraMap ℚ ℂ)).eval (t ζ) = t a := by
      rw [hp, ← Polynomial.aeval_algHom_apply]
      simp only [Polynomial.aeval_def, Polynomial.eval_map, AlgHom.commutes]
    rw [ha, Module.End.aeval_apply_of_mem_apply_eq_smul
      (Module.End.mem_eigenspace_iff.mp hv), hs]

/-- Every complex cyclotomic root is the image of the inverse primitive generator under an embedding. -/
theorem s4_embedding_of_cyclotomic_root (m : ℕ) [NeZero m] (hm : 0 < m)
    (μ : ℂ) (hμ : ((Polynomial.cyclotomic m ℚ).map (algebraMap ℚ ℂ)).IsRoot μ) :
    ∃ t : cyc_Field m →ₐ[ℚ] ℂ,
      t (IsCyclotomicExtension.zeta m ℚ (cyc_Field m))⁻¹ = μ := by
  letI : NeZero m := ⟨hm.ne'⟩
  have hprim : IsPrimitiveRoot μ m := by
    rw [Polynomial.map_cyclotomic] at hμ
    exact Polynomial.isRoot_cyclotomic_iff.mp hμ
  let ζ := IsCyclotomicExtension.zeta m ℚ (cyc_Field m)
  have hζ : IsPrimitiveRoot ζ⁻¹ m := (IsCyclotomicExtension.zeta_spec m ℚ (cyc_Field m)).inv
  let E := hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hm)
  let r : primitiveRoots m ℂ := ⟨μ, (mem_primitiveRoots hm).mpr hprim⟩
  refine ⟨E.symm r, ?_⟩
  have he := congrArg Subtype.val (E.apply_symm_apply r)
  simpa only [E, IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe, r, ζ,
    map_inv₀] using he

end HodgeLean.Foundations.Program

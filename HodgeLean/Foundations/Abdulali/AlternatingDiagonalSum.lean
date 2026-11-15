import HodgeLean.Foundations.Abdulali.VolumeCovectorAlternation

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Equal entries in distinct slots force zero normalized determinant evaluation. -/
theorem normalizedVolumeCovector_tprod_eq_zero_of_eq
    (v : Fin (Module.finrank ℂ V) → V)
    (i j : Fin (Module.finrank ℂ V)) (hij : i ≠ j) (hv : v i = v j) :
    normalizedVolumeCovector (PiTensorProduct.tprod ℂ v) = 0 := by
  apply normalizedVolumeCovector_eq_zero_of_swap i j hij
  rw [SchurWeyl.permRep_tprod]
  congr 1
  funext k
  simp only [Equiv.symm_swap, Equiv.swap_apply_def]
  split_ifs with hki hkj
  · subst k; exact hv.symm
  · subst k; exact hv
  · rfl

/-- Evaluating the diagonal sum against the top covector produces the alternating tensor. -/
theorem normalizedVolumeCovector_diagonal_sum
    (b : Fin (Module.finrank ℂ V) → V) :
    (∑ f : Fin (Module.finrank ℂ V) → Fin (Module.finrank ℂ V),
      normalizedVolumeCovector (PiTensorProduct.tprod ℂ (b ∘ f)) •
        PiTensorProduct.tprod ℂ (b ∘ f)) =
    normalizedVolumeCovector (PiTensorProduct.tprod ℂ b) •
      SchurWeyl.antisymTensor ℂ V _ b := by
  classical
  have hinj (f : Fin (Module.finrank ℂ V) → Fin (Module.finrank ℂ V))
      (hf : normalizedVolumeCovector (PiTensorProduct.tprod ℂ (b ∘ f)) •
        PiTensorProduct.tprod ℂ (b ∘ f) ≠ 0) : Function.Injective f := by
    intro i j h
    by_contra hij
    have hz := normalizedVolumeCovector_tprod_eq_zero_of_eq (b ∘ f) i j hij
      (congrArg b h)
    rw [hz, zero_smul] at hf
    exact hf rfl
  have hsum :
      (∑ σ : Equiv.Perm (Fin (Module.finrank ℂ V)),
        normalizedVolumeCovector (PiTensorProduct.tprod ℂ (b ∘ σ)) •
          PiTensorProduct.tprod ℂ (b ∘ σ)) =
      ∑ f : Fin (Module.finrank ℂ V) → Fin (Module.finrank ℂ V),
        normalizedVolumeCovector (PiTensorProduct.tprod ℂ (b ∘ f)) •
          PiTensorProduct.tprod ℂ (b ∘ f) := by
    refine Finset.sum_bij_ne_zero (fun σ _ _ => ⇑σ) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro σ _ _ τ _ _ h
      exact Equiv.ext (congrFun h)
    · intro f _ hf
      let σ : Equiv.Perm (Fin (Module.finrank ℂ V)) :=
        Equiv.ofBijective f (Finite.injective_iff_bijective.mp (hinj f hf))
      refine ⟨σ, Finset.mem_univ _, ?_, rfl⟩
      exact hf
    · intro σ _ _
      rfl
  rw [← hsum, SchurWeyl.antisymTensor_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hp := normalizedVolumeCovector_perm σ.symm (PiTensorProduct.tprod ℂ b)
  simp only [SchurWeyl.permRep_tprod, Equiv.symm_symm, Equiv.Perm.sign_symm] at hp
  change normalizedVolumeCovector (PiTensorProduct.tprod ℂ (fun i => b (σ i))) = _ at hp
  rw [show b ∘ ⇑σ = (fun i => b (σ i)) from rfl, hp,
    ← Int.cast_smul_eq_zsmul ℂ, smul_smul, mul_comm]

/-- Every top alternating tensor is the chosen volume times its determinant coefficient. -/
theorem antisymTensor_eq_det_smul_volume (b : Fin (Module.finrank ℂ V) → V) :
    SchurWeyl.antisymTensor ℂ V _ b =
      (Module.finBasis ℂ V).det b • SchurWeyl.detTensorDual ℂ V := by
  rw [SchurWeyl.detTensorDual_eq, ← sub_eq_zero,
    ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  have hh := (ℓ.compAlternatingMap (SchurWeyl.antisymTensor ℂ V _)).eq_smul_basis_det
    (Module.finBasis ℂ V)
  have h := congr($hh b)
  simp only [LinearMap.compAlternatingMap_apply, smul_apply, smul_eq_mul] at h
  rw [map_sub, map_smul, h, smul_eq_mul, mul_comm, sub_self]

end HodgeLean.Foundations.Abdulali

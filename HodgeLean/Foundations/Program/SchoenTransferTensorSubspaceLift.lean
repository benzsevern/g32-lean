import HodgeLean.Foundations.Program.SchoenTransferAlternatingTensorRange

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- An injective linear map stays injective on ordered tensor powers. -/
theorem s4_tensor_map_injective {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (n : ℕ) (F : V →ₗ[K] W) (hF : Function.Injective F) :
    Function.Injective (PiTensorProduct.map (fun _ : Fin n => F)) := by
  obtain ⟨G, hG⟩ := F.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hF)
  have he : (PiTensorProduct.map (fun _ : Fin n => G)).comp
      (PiTensorProduct.map (fun _ : Fin n => F)) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hG, PiTensorProduct.map_id]
  intro x y hxy
  have h := congrArg (PiTensorProduct.map (fun _ : Fin n => G)) hxy
  simpa only [← LinearMap.comp_apply, he, LinearMap.id_apply] using h

/-- Tensor permutations commute with applying the same linear map at every factor. -/
theorem s4_tensorPermutation_map {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (n : ℕ) (F : V →ₗ[K] W) (σ : Equiv.Perm (Fin n)) :
    (s4_tensorPermutation n σ).comp (PiTensorProduct.map (fun _ : Fin n => F)) =
      (PiTensorProduct.map (fun _ : Fin n => F)).comp (s4_tensorPermutation n σ) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    s4_tensorPermutation, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod,
    MultilinearMap.domDomCongr_apply]

/-- Tensor alternation is natural in the underlying vector space. -/
theorem s4_tensorAlternation_map {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (n : ℕ) (F : V →ₗ[K] W) :
    (PiTensorProduct.map (fun _ : Fin n => F)).comp (exteriorPower.toTensorPower K V n) =
      (exteriorPower.toTensorPower K W n).comp (exteriorPower.map n F) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.toTensorPower_apply_ιMulti,
    map_sum, Units.smul_def, map_zsmul, PiTensorProduct.map_tprod]
  rfl

/-- An alternating tensor supported on a subspace lifts to the exterior power of that subspace. -/
theorem s4_alternating_tensor_subspace_lift {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (n : ℕ) (U : Submodule K V)
    {z : ⨂[K] i : Fin n, V}
    (hz : z ∈ LinearMap.range (PiTensorProduct.map (fun _ : Fin n => U.subtype)))
    (hσ : ∀ σ : Equiv.Perm (Fin n), s4_tensorPermutation n σ z = σ.sign • z) :
    z ∈ LinearMap.range ((exteriorPower.toTensorPower K V n).comp
      (exteriorPower.map n U.subtype)) := by
  obtain ⟨y, rfl⟩ := hz
  have hi := s4_tensor_map_injective n U.subtype Subtype.val_injective
  have hy (σ : Equiv.Perm (Fin n)) : s4_tensorPermutation n σ y = σ.sign • y := by
    apply hi
    rw [← LinearMap.comp_apply, ← s4_tensorPermutation_map]
    simpa only [LinearMap.comp_apply, Units.smul_def, map_zsmul] using hσ σ
  obtain ⟨w, hw⟩ := s4_mem_tensor_alternation_range n y hy
  refine ⟨w, ?_⟩
  rw [← s4_tensorAlternation_map, LinearMap.comp_apply, hw]

end HodgeLean.Foundations.Program

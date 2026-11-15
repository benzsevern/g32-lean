import HodgeLean.Foundations.Abdulali.TransverseVolumeContraction

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- Mapping the retained factor commutes with covector contraction. -/
theorem covector_contraction_map_left
    {A W U : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (L : A →ₗ[ℂ] W) (ℓ : U →ₗ[ℂ] ℂ) (z : A ⊗[ℂ] U) :
    (TensorProduct.rid ℂ W) (TensorProduct.map LinearMap.id ℓ
      (TensorProduct.map L LinearMap.id z)) =
    L ((TensorProduct.rid ℂ A) (TensorProduct.map LinearMap.id ℓ z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.rid_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Independent labels on the retained slots give exactly one labeled volume. -/
theorem transverseTensor_labeled_volume_contract (r : ℕ)
    (c : Fin (Module.finrank ℂ V) → Fin r) (T : Module.Dual ℂ V →ₗ[ℂ] V) :
    (TensorProduct.rid ℂ _) (TensorProduct.map LinearMap.id normalizedVolumeCovector
      (TensorProduct.map
        (PiTensorProduct.map (fun i => LinearMap.single ℂ (fun _ : Fin r => V) (c i)))
        LinearMap.id (transverseTensor (Module.finrank ℂ V) T))) =
      (((Module.finrank ℂ V).factorial : ℂ)⁻¹ *
        (Module.finBasis ℂ V).det (T ∘ (Module.finBasis ℂ V).dualBasis)) •
          labeledVolume r c := by
  rw [covector_contraction_map_left, transverseTensor_volume_contract,
    tensorMap_detTensor, map_smul, map_smul, smul_smul]
  rfl

/-- In top degree the transverse contraction lies in the specified volume products. -/
theorem transverseTensor_labeled_contract_mem_volumeProducts
    (B : LinearMap.BilinForm ℂ V) (r : ℕ)
    (c : Fin (Module.finrank ℂ V) → Fin r) (T : Module.Dual ℂ V →ₗ[ℂ] V) :
    (TensorProduct.rid ℂ _) (TensorProduct.map LinearMap.id normalizedVolumeCovector
      (TensorProduct.map
        (PiTensorProduct.map (fun i => LinearMap.single ℂ (fun _ : Fin r => V) (c i)))
        LinearMap.id (transverseTensor (Module.finrank ℂ V) T))) ∈
      orthogonalVolumeProducts B r (Module.finrank ℂ V) := by
  rw [transverseTensor_labeled_volume_contract]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨0, zero_add _, 1, PiTensorProduct.tprod ℂ (fun i : Fin 0 => Fin.elim0 i),
    c, Submodule.mem_top, ?_⟩
  simp only [map_one, Module.End.one_apply]
  have hc {m l : ℕ} (h : m = l) (a : ℂ) (v : Fin m → Fin r → V) :
      h ▸ (a • PiTensorProduct.tprod ℂ v) =
        a • PiTensorProduct.tprod ℂ (fun i => v (Fin.cast h.symm i)) := by
    subst l
    rfl
  have ha {m l : ℕ} (h : m = l) (x y : ⨂[ℂ]^m (Fin r → V)) :
      h ▸ (x + y) = (h ▸ x) + (h ▸ y) := by
    subst l
    rfl
  induction labeledVolume (V := V) r c using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    simp only [TensorProduct.tmul_smul, map_smul, InvariantsExterior.tensorAppend_tprod, hc]
    congr 2
    funext i
    simp only [Fin.elim0_append, Function.comp_apply, Fin.cast_cast]
    congr 1
  | add x y hx hy =>
    rw [TensorProduct.tmul_add, map_add, ha, ← hx, ← hy]

end HodgeLean.Foundations.Abdulali

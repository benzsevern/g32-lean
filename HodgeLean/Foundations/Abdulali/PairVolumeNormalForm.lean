import HodgeLean.Foundations.Abdulali.TransverseLabeledVolume

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Retained quadratic products times one independently labeled volume belong to the prescribed span. -/
theorem quadratic_append_labeledVolume_mem (B : LinearMap.BilinForm ℂ V) (r k : ℕ)
    (a : ⨂[ℂ]^k (Fin r → V))
    (ha : a ∈ m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) k)
    (c : Fin (Module.finrank ℂ V) → Fin r)
    (σ : Equiv.Perm (Fin (k + Module.finrank ℂ V))) :
    SchurWeyl.permRep ℂ _ _ σ
      (InvariantsExterior.tensorAppend k (Module.finrank ℂ V) (a ⊗ₜ[ℂ] labeledVolume r c)) ∈
        orthogonalVolumeProducts B r (k + Module.finrank ℂ V) :=
  Submodule.subset_span ⟨k, rfl, σ, a, c, ha, rfl⟩

/-- A transverse block with retained quadratic factors has the required permuted product form. -/
theorem transverse_quadratic_contraction_mem (B : LinearMap.BilinForm ℂ V) (r k : ℕ)
    (a : ⨂[ℂ]^k (Fin r → V))
    (ha : a ∈ m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) k)
    (c : Fin (Module.finrank ℂ V) → Fin r) (T : Module.Dual ℂ V →ₗ[ℂ] V)
    (σ : Equiv.Perm (Fin (k + Module.finrank ℂ V))) :
    SchurWeyl.permRep ℂ _ _ σ
      (InvariantsExterior.tensorAppend k (Module.finrank ℂ V)
        (a ⊗ₜ[ℂ] (TensorProduct.rid ℂ _)
          (TensorProduct.map LinearMap.id normalizedVolumeCovector
            (TensorProduct.map
              (PiTensorProduct.map (fun i => LinearMap.single ℂ (fun _ : Fin r => V) (c i)))
              LinearMap.id (transverseTensor (Module.finrank ℂ V) T))))) ∈
      orthogonalVolumeProducts B r (k + Module.finrank ℂ V) := by
  rw [transverseTensor_labeled_volume_contract, TensorProduct.tmul_smul, map_smul, map_smul]
  exact Submodule.smul_mem _ _ (quadratic_append_labeledVolume_mem B r k a ha c σ)

end HodgeLean.Foundations.Abdulali

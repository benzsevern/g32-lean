import HodgeLean.Foundations.Abdulali.PairVolumeNormalForm
import HodgeLean.Foundations.Program.MilneTensorFamilyProducts
import HodgeLean.Foundations.Program.MilneTensorCopyInjection

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Independent copy labels preserve the prescribed permuted quadratic-volume form. -/
theorem copyTensorIn_perm_append_volume_mem (B : LinearMap.BilinForm ℂ V) (r k : ℕ)
    (a : ⨂[ℂ]^k V) (ha : a ∈ m1b_products (m1b_fixed (m1b_isometries B) 2) k)
    (c : Fin (k + Module.finrank ℂ V) → Fin r)
    (σ : Equiv.Perm (Fin (k + Module.finrank ℂ V))) :
    m1b_copyTensorIn r (k + Module.finrank ℂ V) c
      (SchurWeyl.permRep ℂ V _ σ
        (InvariantsExterior.tensorAppend k (Module.finrank ℂ V)
          (a ⊗ₜ[ℂ] SchurWeyl.detTensorDual ℂ V))) ∈
      orthogonalVolumeProducts B r (k + Module.finrank ℂ V) := by
  rw [m1b_copyTensorIn, m1b_tensorMap_perm, m1b_tensorMap_append]
  change SchurWeyl.permRep ℂ _ _ σ
    (InvariantsExterior.tensorAppend k (Module.finrank ℂ V)
      ((PiTensorProduct.map
        (fun i => LinearMap.single ℂ (fun _ : Fin r => V)
          (c (σ (Fin.castAdd (Module.finrank ℂ V) i))))) a ⊗ₜ[ℂ]
        labeledVolume r (fun j => c (σ (Fin.natAdd k j))))) ∈ _
  apply quadratic_append_labeledVolume_mem
  apply m1b_products_map_family (m1b_fixed (m1b_isometries B) 2)
    (m1b_fixed (m1b_copies r '' m1b_isometries B) 2)
    (Set.range (fun j : Fin r => LinearMap.single ℂ (fun _ : Fin r => V) j))
  · intro g hg q hq
    exact m1b_copyInjection_family_fixed (m1b_isometries B) r 2 g hg q hq
  · intro i
    exact ⟨_, rfl⟩
  · exact ha

end HodgeLean.Foundations.Abdulali

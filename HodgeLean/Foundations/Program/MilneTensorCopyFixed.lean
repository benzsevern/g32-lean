import HodgeLean.Foundations.Program.MilneTensorCopyDecomposition
import HodgeLean.Foundations.Program.MilneTensorFamilyFixed

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_copyTensorOut_fixed (S : Set (Module.End ℂ V)) (r n : ℕ)
    (a : Fin n → Fin r) (t : ⨂[ℂ]^n (Fin r → V))
    (ht : t ∈ m1b_fixed (m1b_copies r '' S) n) :
    m1b_copyTensorOut r n a t ∈ m1b_fixed S n := by
  change PiTensorProduct.map (fun i => (LinearMap.proj (a i) : (Fin r → V) →ₗ[ℂ] V)) t ∈ _
  refine m1b_tensorMap_fixed (V := Fin r → V) (W := V) (m1b_copies r '' S) S n
    (fun i => (LinearMap.proj (a i) : (Fin r → V) →ₗ[ℂ] V)) ?_ t ht
  intro u hu
  exact ⟨m1b_copies r u, ⟨u, hu, rfl⟩, fun _ => rfl⟩

end HodgeLean.Foundations.Program

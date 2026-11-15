import HodgeLean.Foundations.Program.MilneTensorCopyFixed
import HodgeLean.Foundations.Program.MilneTensorCopyInjection
import HodgeLean.Foundations.Program.MilneTensorFamilyProducts

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_copies_generation (S : Set (Module.End ℂ V)) (r n : ℕ)
    (hgen : m1b_fixed S n = m1b_products (m1b_fixed S 2) n) :
    m1b_fixed (m1b_copies r '' S) n =
      m1b_products (m1b_fixed (m1b_copies r '' S) 2) n := by
  let F : Set (V →ₗ[ℂ] (Fin r → V)) :=
    Set.range (fun c : Fin r => LinearMap.single ℂ (fun _ : Fin r => V) c)
  have hquad : ∀ g : Fin 2 → V →ₗ[ℂ] (Fin r → V), (∀ i, g i ∈ F) →
      ∀ b ∈ m1b_fixed S 2, PiTensorProduct.map g b ∈ m1b_fixed (m1b_copies r '' S) 2 :=
    m1b_copyInjection_family_fixed (V := V) S r 2
  apply le_antisymm
  · intro t ht
    rw [← m1b_sum_copyTensorIn_out r n t]
    apply Submodule.sum_mem
    intro a _
    have ha := m1b_copyTensorOut_fixed S r n a t ht
    rw [hgen] at ha
    change PiTensorProduct.map (fun i => LinearMap.single ℂ (fun _ : Fin r => V) (a i))
      (m1b_copyTensorOut r n a t) ∈ _
    apply m1b_products_map_family (V := V) (W := Fin r → V)
      (m1b_fixed S 2) (m1b_fixed (m1b_copies r '' S) 2) F
    · exact hquad
    · intro i
      exact ⟨a i, rfl⟩
    · exact ha
  · exact m1b_products_le_fixed _ n

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.MilneTensorFamilyFixed

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_copyInjection_family_fixed (S : Set (Module.End ℂ V)) (r n : ℕ)
    (g : Fin n → V →ₗ[ℂ] (Fin r → V))
    (hg : ∀ i, g i ∈ Set.range (fun c : Fin r => LinearMap.single ℂ (fun _ : Fin r => V) c))
    (t : ⨂[ℂ]^n V) (ht : t ∈ m1b_fixed S n) :
    PiTensorProduct.map g t ∈ m1b_fixed (m1b_copies r '' S) n := by
  apply m1b_tensorMap_fixed S (m1b_copies r '' S) n g _ t ht
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨u, hu, ?_⟩
  intro i
  obtain ⟨c, hc⟩ := hg i
  rw [← hc]
  apply LinearMap.ext
  intro x
  funext j
  exact LinearMap.apply_single (fun _ : Fin r => u) c j x

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.MilneTensorFamilyFixed
import HodgeLean.Foundations.Program.MilneTensorFamilyProducts
import HodgeLean.Foundations.Program.MilneTensorHelpers

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V W G : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_generation_retract (ρ : G → Module.End ℂ V) (σ : G → Module.End ℂ W)
    (i : V →ₗ[ℂ] W) (p : W →ₗ[ℂ] V) (hpi : p.comp i = LinearMap.id)
    (hi : ∀ g, (σ g).comp i = i.comp (ρ g))
    (hp : ∀ g, (ρ g).comp p = p.comp (σ g)) (n : ℕ)
    (hgen : m1b_fixed (Set.range σ) n = m1b_products (m1b_fixed (Set.range σ) 2) n) :
    m1b_fixed (Set.range ρ) n = m1b_products (m1b_fixed (Set.range ρ) 2) n := by
  have hin (k : ℕ) : ∀ u ∈ Set.range σ, ∃ v ∈ Set.range ρ,
      ∀ _ : Fin k, u.comp i = i.comp v := by
    rintro _ ⟨g, rfl⟩
    exact ⟨ρ g, ⟨g, rfl⟩, fun _ => hi g⟩
  have hout (k : ℕ) : ∀ v ∈ Set.range ρ, ∃ u ∈ Set.range σ,
      ∀ _ : Fin k, v.comp p = p.comp u := by
    rintro _ ⟨g, rfl⟩
    exact ⟨σ g, ⟨g, rfl⟩, fun _ => hp g⟩
  have hquad (f : Fin 2 → W →ₗ[ℂ] V) (hf : ∀ j, f j ∈ ({p} : Set (W →ₗ[ℂ] V)))
      (b : ⨂[ℂ]^2 W) (hb : b ∈ m1b_fixed (Set.range σ) 2) :
      PiTensorProduct.map f b ∈ m1b_fixed (Set.range ρ) 2 := by
    have heq : f = fun _ => p := funext fun j => hf j
    subst f
    exact m1b_tensorMap_fixed _ _ 2 (fun _ => p) (hout 2) b hb
  apply le_antisymm
  · intro t ht
    have hit := m1b_tensorMap_fixed _ _ n (fun _ => i) (hin n) t ht
    rw [hgen] at hit
    have hpt := m1b_products_map_family (m1b_fixed (Set.range σ) 2)
      (m1b_fixed (Set.range ρ) 2) {p} hquad n (fun _ => p) (fun _ => rfl) _ hit
    have hmap : (PiTensorProduct.map (fun _ : Fin n => p)).comp
        (PiTensorProduct.map (fun _ : Fin n => i)) = LinearMap.id := by
      ext v
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        PiTensorProduct.map_tprod, LinearMap.id_apply]
      congr 1
      funext j
      exact LinearMap.congr_fun hpi (v j)
    change ((PiTensorProduct.map (fun _ : Fin n => p)).comp
      (PiTensorProduct.map (fun _ : Fin n => i))) t ∈ _ at hpt
    rwa [hmap, LinearMap.id_apply] at hpt
  · exact m1b_products_le_fixed _ n

end HodgeLean.Foundations.Program

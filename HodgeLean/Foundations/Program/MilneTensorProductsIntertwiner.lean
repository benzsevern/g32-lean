import HodgeLean.Foundations.Program.MilneTensorFamilyProducts
import HodgeLean.Foundations.Program.MilneTensorFamilyFixed

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_products_intertwiner (S : Set (Module.End ℂ V)) (T : Set (Module.End ℂ W))
    (f : V →ₗ[ℂ] W) (hf : ∀ u ∈ T, ∃ v ∈ S, u.comp f = f.comp v)
    (n : ℕ) (t : ⨂[ℂ]^n V) (ht : t ∈ m1b_products (m1b_fixed S 2) n) :
    PiTensorProduct.map (fun _ => f) t ∈ m1b_products (m1b_fixed T 2) n := by
  apply m1b_products_map_family (m1b_fixed S 2) (m1b_fixed T 2) {f}
  · intro g hg b hb
    have heq : g = fun _ => f := funext fun i => hg i
    subst g
    apply m1b_tensorMap_fixed S T 2 (fun _ => f) _ b hb
    intro u hu
    obtain ⟨v, hv, he⟩ := hf u hu
    exact ⟨v, hv, fun _ => he⟩
  · intro i
    rfl
  · exact ht

end HodgeLean.Foundations.Program

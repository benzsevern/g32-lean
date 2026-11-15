import HodgeLean.Foundations.Program.MilneTensorColoredAppend
import HodgeLean.Foundations.Program.MilneTensorProductsIntertwiner
import HodgeLean.Foundations.Program.MilneTensorFixedSlot

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_coloredWordIn_products (S : Set (Module.End ℂ V)) (T : Set (Module.End ℂ W))
    (hS : ∀ k, m1b_fixed S k = m1b_products (m1b_fixed S 2) k)
    (hT : ∀ k, m1b_fixed T k = m1b_products (m1b_fixed T 2) k)
    (n : ℕ) (s : Finset (Fin n))
    (x : ⨂[ℂ] _ : {i // i ∈ s}, V) (y : ⨂[ℂ] _ : {i // i ∉ s}, W)
    (hx : ∀ u ∈ S, SchurWeyl.tensorPow {i // i ∈ s} u x = x)
    (hy : ∀ v ∈ T, SchurWeyl.tensorPow {i // i ∉ s} v y = y) :
    InvariantsExterior.coloredWordIn s (x ⊗ₜ[ℂ] y) ∈
      m1b_products (m1b_fixed (Set.image2 (fun u v => u.prodMap v) S T) 2) n := by
  classical
  let k := Fintype.card {i : Fin n // i ∈ s}
  let l := Fintype.card {i : Fin n // i ∉ s}
  let e : Fin k ≃ {i // i ∈ s} := (Fintype.equivFin _).symm
  let d : Fin l ≃ {i // i ∉ s} := (Fintype.equivFin _).symm
  let a := (PiTensorProduct.reindex ℂ (fun _ => V) e).symm x
  let b := (PiTensorProduct.reindex ℂ (fun _ => W) d).symm y
  have ha : a ∈ m1b_products (m1b_fixed S 2) k := by
    rw [← hS k]
    exact m1b_fixed_reindex_fin S k e x hx
  have hb : b ∈ m1b_products (m1b_fixed T 2) l := by
    rw [← hT l]
    exact m1b_fixed_reindex_fin T l d y hy
  let U := Set.image2 (fun (u : Module.End ℂ V) (v : Module.End ℂ W) => u.prodMap v) S T
  have hi : ∀ u ∈ U, ∃ v ∈ S,
      u.comp (LinearMap.inl ℂ V W) = (LinearMap.inl ℂ V W).comp v := by
    rintro _ ⟨u, hu, v, hv, rfl⟩
    refine ⟨u, hu, ?_⟩
    apply LinearMap.ext
    intro z
    change (u z, v 0) = (u z, 0)
    rw [map_zero]
  have hj : ∀ u ∈ U, ∃ v ∈ T,
      u.comp (LinearMap.inr ℂ V W) = (LinearMap.inr ℂ V W).comp v := by
    rintro _ ⟨u, hu, v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    apply LinearMap.ext
    intro z
    change (u 0, v z) = (0, v z)
    rw [map_zero]
  have hai := m1b_products_intertwiner S U (LinearMap.inl ℂ V W) hi k a ha
  have hbj := m1b_products_intertwiner T U (LinearMap.inr ℂ V W) hj l b hb
  have hp := m1b_products_append (m1b_fixed U 2) k _ hai l _ hbj
  have hins := m1b_coloredWordIn_append n k l s e d a b
  dsimp only at hins
  have ha0 : PiTensorProduct.reindex ℂ (fun _ => V) e a = x :=
    (PiTensorProduct.reindex ℂ (fun _ => V) e).apply_symm_apply x
  have hb0 : PiTensorProduct.reindex ℂ (fun _ => W) d b = y :=
    (PiTensorProduct.reindex ℂ (fun _ => W) d).apply_symm_apply y
  rw [ha0, hb0] at hins
  rw [hins]
  exact m1b_products_reindex _ _ _ hp

end HodgeLean.Foundations.Program

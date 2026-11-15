import HodgeLean.Foundations.Program.MilneTensorOneCopyPolarization
import HodgeLean.Foundations.Program.MilneTensorPolarizationProducts
import HodgeLean.Foundations.Program.MilneTensorCopyGeneration

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_coordinate_generation_of_orbit_polynomials
    (ε : ℂ) (hε : ε ^ 2 = 1)
    (B : LinearMap.BilinForm ℂ (ι → ℂ)) (hB : B.Nondegenerate)
    (hsign : ∀ x y, B y x = ε * B x y)
    (horbit : ∀ Q : Matrix ι ι ℂ, Q.det ≠ 0 → Q.transpose = ε • Q →
      Q.toBilin' ∈ Set.range (m1b_formTransport B))
    (hpoly : ∀ n (f : MultilinearMap ℂ (fun _ : Fin n => Fin 1 → ι → ℂ) ℂ),
      (∀ u ∈ m1b_isometries B, ∀ v, f (fun s => m1b_copies 1 u (v s)) = f v) →
      ∃ P : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin 1 × ι))) ℂ,
        ∀ (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin 1 → ι → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun s c => e.symm (v s c)))
    (r n : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries B) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n := by
  apply m1b_copies_generation
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨k, hk⟩ := hn
    have hnk : n = k * 2 := by omega
    clear hk
    subst n
    apply le_antisymm _ (m1b_products_le_fixed _ _)
    intro t ht
    let f := m1b_tensorFunction B (k * 2) t
    have hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun s => u (v s)) = f v := by
      intro u hu v
      exact m1b_tensorFunction_fixed B (k * 2) (m1b_isometries B) (fun _ h => h) t ht u hu v
    let f₁ : MultilinearMap ℂ (fun _ : Fin (k * 2) => Fin 1 → ι → ℂ) ℂ :=
      f.compLinearMap (fun _ => LinearMap.proj (0 : Fin 1))
    have hf₁ : ∀ u ∈ m1b_isometries B, ∀ v,
        f₁ (fun s => m1b_copies 1 u (v s)) = f₁ v := by
      intro u hu v
      exact hf u hu (fun s => v s 0)
    obtain ⟨P, hP⟩ := hpoly (k * 2) f₁ hf₁
    obtain ⟨J, hJ, hdiag⟩ := m1b_covariant_polarization_of_orbit_polynomial
      ε hε B hB hsign k f hf P hP horbit
    exact m1b_tensor_mem_products_of_polarization B hB k t J hJ hdiag
  · rw [m1b_fixed_odd _ (m1b_isometries_neg_one B) n hn, m1b_products_odd _ n hn]

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.TorusAlgebraizationB52TracedProducts

noncomputable section
namespace HodgeLean.Foundations.Program
open scoped TensorProduct

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)

theorem b52_descentTrace_apply_sum (k n : ℕ) (hn : n ≠ 0)
    (r : (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range) → Λ)
    (hr : ∀ q, QuotientAddGroup.mk (r q) = q)
    (t : b5_sections Λ F hF Q (k * n ^ 2)) (z : b5_V Λ F) :
    letI := b52_finite_lattice_quotient Λ n hn
    letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
    (b52_descentTrace Λ F hF Q hherm himag hcocycle k n hn t).val z =
      (Fintype.card (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range) : ℂ)⁻¹ *
        ∑ q, (b5_factor Λ F hF Q (r q) z ^ k)⁻¹ *
          t.val ((n : ℂ)⁻¹ • (z + b5_lattice Λ F (r q))) := by
  letI := b52_finite_lattice_quotient Λ n hn
  letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  change (b52_averageEnd
    (b52_descentQuotientHom Λ F hF Q hherm himag hcocycle k n hn) t).val
      ((n : ℂ)⁻¹ • z) = _
  simp only [b52_averageEnd, LinearMap.smul_apply, LinearMap.sum_apply,
    Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  conv_lhs => rw [← hr q]
  change (b5_factor Λ F hF Q (r q) ((n : ℂ) • ((n : ℂ)⁻¹ • z)) ^ k)⁻¹ *
    t.val ((n : ℂ)⁻¹ • z + (n : ℂ)⁻¹ • b5_lattice Λ F (r q)) = _
  rw [smul_smul, mul_inv_cancel₀ hn', one_smul, ← smul_add]

theorem b52_sum_products_of_separate_sums
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u v : ι → κ → ℂ) (a b : κ → ℂ) :
    ∑ i, (∑ q, a q * u i q) * (∑ q, b q * v i q) =
      ∑ q, ∑ r, (a q * b r) * ∑ i, u i q * v i r := by
  classical
  conv_rhs => rw [Finset.sum_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  ring

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.NumeratorJetLaurent

/-! # Coefficients of the polynomial part of a frame product

At every parameter, the coefficient `j` of the polynomial part of `D_θ qᵀr` is
`Σ_{jj, k} (Σ_a c_{4a+jj} Λ_{a,k,j}) · G_{jj,k}`, where `G_{jj,k}` is the coefficient `k` of the
polynomial part of `D_θ q_{jj}`: the fixed-pole part through the weights `Λ_{b,i,k}` and the
moving-pole part through the moving moments `Σ_x β_x w_{x,jj} t_x^m`.
-/

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

theorem b65e_rearrange_fixed (dd cc : Fin 9 → ℂ) (Q L : Fin 9 → ℕ → ℂ) :
    ∑ b : Fin 9, ∑ a : Fin 9, dd b * cc a * ∑ k ∈ Finset.range 13, Q b k * L a k =
      ∑ k ∈ Finset.range 13, (∑ a : Fin 9, cc a * L a k) * ∑ b : Fin 9, dd b * Q b k := by
  have e1 : ∀ b a, dd b * cc a * ∑ k ∈ Finset.range 13, Q b k * L a k =
      ∑ k ∈ Finset.range 13, (cc a * L a k) * (dd b * Q b k) := by
    intro b a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have e2 : ∀ k, (∑ a : Fin 9, cc a * L a k) * ∑ b : Fin 9, dd b * Q b k =
      ∑ a : Fin 9, ∑ b : Fin 9, (cc a * L a k) * (dd b * Q b k) := fun k ↦ Finset.sum_mul_sum _ _ _ _
  simp only [e1, e2]
  calc _ = ∑ a : Fin 9, ∑ b : Fin 9, ∑ k ∈ Finset.range 13, (cc a * L a k) * (dd b * Q b k) :=
        Finset.sum_comm
    _ = ∑ a : Fin 9, ∑ k ∈ Finset.range 13, ∑ b : Fin 9, (cc a * L a k) * (dd b * Q b k) :=
        Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem b65e_rearrange_moving (β : Fin 12 → ℂ) (cc : Fin 9 → ℂ) (E : Fin 12 → ℕ → ℂ)
    (L : Fin 9 → ℕ → ℂ) :
    ∑ x : Fin 12, ∑ a : Fin 9, β x * cc a * ∑ k ∈ Finset.range 13, E x k * L a k =
      ∑ k ∈ Finset.range 13, (∑ a : Fin 9, cc a * L a k) * ∑ x : Fin 12, β x * E x k := by
  have e1 : ∀ x a, β x * cc a * ∑ k ∈ Finset.range 13, E x k * L a k =
      ∑ k ∈ Finset.range 13, (cc a * L a k) * (β x * E x k) := by
    intro x a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have e2 : ∀ k, (∑ a : Fin 9, cc a * L a k) * ∑ x : Fin 12, β x * E x k =
      ∑ a : Fin 9, ∑ x : Fin 12, (cc a * L a k) * (β x * E x k) := fun k ↦ Finset.sum_mul_sum _ _ _ _
  simp only [e1, e2]
  calc _ = ∑ a : Fin 9, ∑ x : Fin 12, ∑ k ∈ Finset.range 13, (cc a * L a k) * (β x * E x k) :=
        Finset.sum_comm
    _ = ∑ a : Fin 9, ∑ k ∈ Finset.range 13, ∑ x : Fin 12, (cc a * L a k) * (β x * E x k) :=
        Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem b65e_denominator_natDegree (p : Fin 12 → ℂ) (θ : ℂ) :
    (b65q_denominator (b65p_poles p θ)).natDegree = 13 := by
  rw [b65q_denominator, b65e_branch_degree]
  decide

theorem b65e_erasedD_natDegree (p : Fin 12 → ℂ) (θ : ℂ) (x : Fin 12) :
    (b65e_erasedD p θ x).natDegree = 12 := by
  rw [b65e_erasedD, b65e_branch_degree]
  simp

/-- **Expansion of the numerator coefficients** at one parameter, for arbitrary coefficient
vectors and left vectors. -/
theorem b65e_numerator_expand (p : Fin 12 → ℂ) (θ : ℂ)
    (w : Fin 12 → Fin 4 → ℂ) (c : Fin 36 → ℂ) (d : Fin 48 → ℂ) (j : ℕ) :
    (b65e_polyPart (b65q_product (b65p_poles p θ) p w c d)).coeff j =
      ∑ jj : Fin 4, ∑ k ∈ Finset.range 13,
        (∑ a : Fin 9, c ⟨4 * a.val + jj.val, by omega⟩ * ((b65e_LamQ a k j : ℚ) : ℂ)) *
        ((∑ b : Fin 9, d ⟨4 * b.val + jj.val, by omega⟩ *
            ∑ i ∈ Finset.range 14, (b65q_denominator (b65p_poles p θ)).coeff i *
              ((b65e_LamQ b i k : ℚ) : ℂ)) +
          ∑ m ∈ Finset.range (13 - k),
            (b65q_denominator (b65p_poles p θ)).coeff (k + 1 + m) *
              ∑ x : Fin 12, ((∑ v : Fin 6,
                d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * p x ^ v.val) * w x jj) *
                b65p_poles p θ (Sum.inr x) ^ m) := by
  have hD : (b65q_denominator (b65p_poles p θ)).natDegree = 13 := b65e_denominator_natDegree p θ
  have h1 : ∀ b a : Fin 9, b65e_polyPart (algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator (b65p_poles p θ)) /
      algebraMap ℂ[X] (RatFunc ℂ) (b65e_fixedFactor b * b65e_fixedFactor a)) =
      ((b65q_denominator (b65p_poles p θ)) /ₘ b65e_fixedFactor b) /ₘ b65e_fixedFactor a := by
    intro b a
    rw [b65e_polyPart_div _ _ ((b65e_fixedFactor_monic b).mul (b65e_fixedFactor_monic a)),
      b65e_divByMonic_mul _ _ _ (b65e_fixedFactor_monic b) (b65e_fixedFactor_monic a)]
  have h2 : ∀ (x : Fin 12) (a : Fin 9), b65e_polyPart (algebraMap ℂ[X] (RatFunc ℂ)
      (b65e_erasedD p θ x) / algebraMap ℂ[X] (RatFunc ℂ) (b65e_fixedFactor a)) =
      b65e_erasedD p θ x /ₘ b65e_fixedFactor a := fun x a ↦
    b65e_polyPart_div _ _ (b65e_fixedFactor_monic a)
  have hq : ∀ b : Fin 9, ((b65q_denominator (b65p_poles p θ)) /ₘ b65e_fixedFactor b).natDegree < 13 := by
    intro b
    rw [natDegree_divByMonic _ (b65e_fixedFactor_monic b), hD]
    have : 1 ≤ (b65e_fixedFactor b).natDegree := by
      rw [b65e_fixedFactor, natDegree_pow, natDegree_X_sub_C, mul_one]
      fin_cases b <;> decide
    omega
  have h3 : ∀ (b a : Fin 9), (((b65q_denominator (b65p_poles p θ)) /ₘ b65e_fixedFactor b) /ₘ b65e_fixedFactor a).coeff j =
      ∑ k ∈ Finset.range 13, (∑ i ∈ Finset.range 14, (b65q_denominator (b65p_poles p θ)).coeff i * ((b65e_LamQ b i k : ℚ) : ℂ)) *
        ((b65e_LamQ a k j : ℚ) : ℂ) := by
    intro b a
    rw [b65e_divFixed_coeff a _ 13 (by omega) (hq b)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [b65e_divFixed_coeff b _ 14 le_rfl (by omega)]
  have h4 : ∀ (x : Fin 12) (a : Fin 9), (b65e_erasedD p θ x /ₘ b65e_fixedFactor a).coeff j =
      ∑ k ∈ Finset.range 13, (∑ m ∈ Finset.range (13 - k), (b65q_denominator (b65p_poles p θ)).coeff (k + 1 + m) *
        b65p_poles p θ (Sum.inr x) ^ m) * ((b65e_LamQ a k j : ℚ) : ℂ) := by
    intro x a
    rw [b65e_divFixed_coeff a _ 13 (by omega) (by rw [b65e_erasedD_natDegree]; omega)]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [b65e_synthetic _ _ _ (b65e_erasedD_mul p θ x) (by rw [b65e_erasedD_natDegree]) k
      (by have := Finset.mem_range.mp hk; omega)]
  rw [b65e_product_expand]
  simp only [b65e_polyPart_sum, b65e_polyPart_add, b65e_polyPart_C_mul, h1, h2,
    finsetSum_coeff, coeff_add, coeff_smul, smul_eq_mul, h3, h4]
  refine Finset.sum_congr rfl fun jj _ ↦ ?_
  rw [b65e_rearrange_fixed, b65e_rearrange_moving, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← mul_add]
  congr 2
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  ring_nf
  exact Finset.sum_congr rfl fun v _ ↦ by ring

end HodgeLean.Foundations.Program

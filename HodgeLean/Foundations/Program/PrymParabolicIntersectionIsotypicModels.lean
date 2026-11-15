import HodgeLean.Foundations.Program.PrymParabolicIntersectionIsotypicCup

noncomputable section
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem hga_coordCup_of_integral_models
    (c c' : hg_eqCocycles hg4_sigmaK b4b_root)
    (α β γ δ : hg2_Edge b4b_Group 13 → ℤ)
    (hα : hg2_delta1 ℤ ℤ b4b_root α = 0)
    (hβ : hg2_delta1 ℤ ℤ b4b_root β = 0)
    (he : ∀ z : LinearMap.ker (hg2_bd1 ℤ b4b_root),
      hg6_pairVec c.1 z.1 0 = -((z.1.sum (fun ε n ↦ n * α ε) : ℤ) : hp_K) +
        QuadraticAlgebra.omega * ((z.1.sum (fun ε n ↦ n * β ε) : ℤ) : hp_K))
    (he' : ∀ z : LinearMap.ker (hg2_bd1 ℤ b4b_root),
      hg6_pairVec c'.1 z.1 0 = -((z.1.sum (fun ε n ↦ n * γ ε) : ℤ) : hp_K) +
        QuadraticAlgebra.omega * ((z.1.sum (fun ε n ↦ n * δ ε) : ℤ) : hp_K)) :
    hg6_coordCup b4b_root 0 0 c.1 c'.1 =
      (hga_cupEval ℤ b4b_root α γ : hp_K) -
        QuadraticAlgebra.omega * (hga_cupEval ℤ b4b_root α δ : hp_K) +
        QuadraticAlgebra.omega * (hga_cupEval ℤ b4b_root β γ : hp_K) +
        3 * (hga_cupEval ℤ b4b_root β δ : hp_K) := by
  have hω : (QuadraticAlgebra.omega : hp_K) ^ 2 = -3 := by
    rw [sq]
    ext <;> simp <;> rfl
  have hstar : star (QuadraticAlgebra.omega : hp_K) = -QuadraticAlgebra.omega := by
    ext <;> simp <;> rfl
  have hleft : hg2_delta1 hp_K hp_K b4b_root
      (fun ε ↦ -(α ε : hp_K) - QuadraticAlgebra.omega * (β ε : hp_K)) = 0 := by
    simpa only [neg_mul, sub_eq_add_neg] using
      hga_cocycle_quadratic_combination hp_K b4b_root (-QuadraticAlgebra.omega) α β hα hβ
  have hright : hg2_delta1 hp_K hp_K b4b_root (fun ε ↦ c'.1 ε 0) = 0 :=
    hg6_coord_mem hg4_sigmaK b4b_root c' 0
  rw [hga_coordCup_eq_cupEval]
  rw [hga_field_cupEval_eq_of_cycle_evaluations
    (fun ε ↦ star (c.1 ε 0))
    (fun ε ↦ -(α ε : hp_K) - QuadraticAlgebra.omega * (β ε : hp_K))
    (fun ε ↦ c'.1 ε 0)
    (fun ε ↦ -(γ ε : hp_K) + QuadraticAlgebra.omega * (δ ε : hp_K)) hleft hright]
  · rw [hga_cupEval_quadratic_expansion hp_K b4b_root _ hω]
    simp only [hga_cupEval_intCast]
  · intro z
    have hs : z.1.sum (fun ε n ↦ (n : hp_K) * star (c.1 ε 0)) =
        star (hg6_pairVec c.1 z.1 0) := by
      simp [hg6_pairVec, Finsupp.sum, Finset.sum_apply, star_sum, star_mul, mul_comm]
    rw [hs, he z]
    have hh := hga_integral_combination_evaluation hp_K z.1 α β (-QuadraticAlgebra.omega)
    simp only [neg_mul, sub_eq_add_neg] at hh ⊢
    rw [hh]
    simp [hstar]
  · intro z
    have hs : z.1.sum (fun ε n ↦ (n : hp_K) * c'.1 ε 0) = hg6_pairVec c'.1 z.1 0 := by
      simp [hg6_pairVec, Finsupp.sum, Finset.sum_apply]
    rw [hs, he' z, hga_integral_combination_evaluation]

#print axioms hga_coordCup_of_integral_models
end HodgeLean.Foundations.Program

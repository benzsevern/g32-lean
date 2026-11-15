import HodgeLean.Foundations.Program.PrymVariationRootArithmetic

/-! # B6-3a: root calculation obligations -/

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b63_root_prefix_product_aux  :
    ((List.ofFn b4b_root).take 8).prod = 1 := by
  simp [b4b_root]

theorem b63_root_tail_product_aux  :
    ((List.ofFn b4b_root).drop 8 |>.take 4).prod = (b4b_generators 2) ^ 2 := by
  exact b63_tail_list_eq.trans b63_tail_group_eq

theorem b63_root_generators_aux (k : Fin 4) :
    b4b_generators k ∈ Subgroup.closure (Set.range b4b_root) := by
  let H := Subgroup.closure (Set.range b4b_root)
  have hr (i : Fin 13) : b4b_root i ∈ H :=
    Subgroup.subset_closure ⟨i, rfl⟩
  change b4b_generators k ∈ H
  fin_cases k
  · change b4b_root 0 ∈ H
    exact hr 0
  · change b4b_root 3 ∈ H
    exact hr 3
  · change b4b_generators 2 ∈ H
    rw [← b63_generator_two_root_word_eq]
    change b4b_root 0 * b4b_root 4 * b4b_root 7 * b4b_root 8 *
      b4b_root 3 * b4b_root 12 * b4b_root 2 * b4b_root 6 ∈ H
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
      (H.mul_mem (H.mul_mem (hr 0) (hr 4)) (hr 7)) (hr 8)) (hr 3)) (hr 12)) (hr 2)) (hr 6)
  · change b4b_generators 3 ∈ H
    rw [← b63_generator_three_root_word_eq]
    change b4b_root 0 * b4b_root 2 * b4b_root 11 * b4b_root 2 *
      b4b_root 12 * b4b_root 6 ∈ H
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
      (H.mul_mem (hr 0) (hr 2)) (hr 11)) (hr 2)) (hr 12)) (hr 6)

private theorem b63_conj_reflection (w : List (Fin 4)) :
    g32h_ConjIn (g32R1 g32h_omega) (b4b_toMatrix (b4b_reflection w)) := by
  let h : b4b_Group := (w.map b4b_generators).prod
  refine ⟨b4b_toMatrix h, h.property, b4b_toMatrix h⁻¹, (h⁻¹).property, ?_, ?_⟩
  · rw [← map_mul]
    simp
  · change b4b_toMatrix (b4b_reflection w) =
      b4b_toMatrix h * b4b_toMatrix (b4b_generators 0) * b4b_toMatrix h⁻¹
    rw [← map_mul, ← map_mul]
    rfl

private theorem b63_conj_swap :
    g32h_ConjIn (g32R1 g32h_omega) (b4b_toMatrix (b4b_generators 1)⁻¹) := by
  refine ⟨b4b_toMatrix b63_class_swap_word, b63_class_swap_word.property,
    b4b_toMatrix b63_class_swap_word⁻¹, (b63_class_swap_word⁻¹).property, ?_, ?_⟩
  · rw [← map_mul]
    simp
  · change b4b_toMatrix ((b4b_generators 1)⁻¹) =
      b4b_toMatrix b63_class_swap_word * b4b_toMatrix (b4b_generators 0) *
        b4b_toMatrix b63_class_swap_word⁻¹
    rw [← map_mul, ← map_mul, b63_class_swap_eq]

theorem b63_root_positive_class_aux (j : Fin 6) :
    g32h_ConjIn (g32R1 g32h_omega)
      (b4b_toMatrix (b4b_root (b63_positiveSlot j))) := by
  fin_cases j
  · change g32h_ConjIn (g32R1 g32h_omega) (b4b_toMatrix (b4b_root 0))
    rw [show b4b_root 0 = b4b_generators 0 from rfl]
    simpa only [b4b_reflection, List.map_nil, List.prod_nil, one_mul, inv_one, mul_one]
      using b63_conj_reflection []
  · simpa [b63_positiveSlot, b4b_root] using b63_conj_swap
  · simpa [b63_positiveSlot, b4b_root] using b63_conj_reflection [2]
  · simpa [b63_positiveSlot, b4b_root] using b63_conj_reflection [3]
  · simpa [b63_positiveSlot, b4b_root] using b63_conj_reflection [1, 3, 1]
  · simpa [b63_positiveSlot, b4b_root] using b63_conj_reflection [3, 2]

private theorem b63_conj_inverse_reflection (w : List (Fin 4)) :
    g32h_ConjIn (g32R2 g32h_omega) (b4b_toMatrix (b4b_reflection w)⁻¹) := by
  let k : b4b_Group := (w.map b4b_generators).prod
  let h : b4b_Group := k * b63_class_swap_word⁻¹
  let h' : b4b_Group := b63_class_swap_word * k⁻¹
  have ha : (b4b_generators 0)⁻¹ =
      b63_class_swap_word⁻¹ * b4b_generators 1 * b63_class_swap_word := by
    calc
      (b4b_generators 0)⁻¹ = b63_class_swap_word⁻¹ *
          (b63_class_swap_word * (b4b_generators 0)⁻¹ *
            b63_class_swap_word⁻¹) * b63_class_swap_word := by group
      _ = _ := by rw [b63_class_swap_inverse_eq]
  refine ⟨b4b_toMatrix h, h.property, b4b_toMatrix h', h'.property, ?_, ?_⟩
  · rw [← map_mul]
    simp [h, h']
  · change b4b_toMatrix (b4b_reflection w)⁻¹ =
      b4b_toMatrix h * b4b_toMatrix (b4b_generators 1) * b4b_toMatrix h'
    rw [← map_mul, ← map_mul]
    apply congrArg b4b_toMatrix
    simp [b4b_reflection, h, h', k, ha]
    group

theorem b63_root_negative_class_aux (j : Fin 6) :
    g32h_ConjIn (g32R2 g32h_omega)
      (b4b_toMatrix (b4b_root (b63_negativeSlot j))) := by
  fin_cases j
  · change g32h_ConjIn (g32R2 g32h_omega) (b4b_toMatrix (b4b_root 1))
    rw [show b4b_root 1 = (b4b_reflection [])⁻¹ by
      simp [b4b_root, b4b_reflection]]
    exact b63_conj_inverse_reflection []
  · change g32h_ConjIn (g32R2 g32h_omega) (b4b_toMatrix (b4b_root 3))
    rw [show b4b_root 3 = b4b_generators 1 from rfl]
    exact ⟨1, one_mem _, 1, one_mem _, by simp, by simp [b4b_generators, b4b_toMatrix]⟩
  · simpa [b63_negativeSlot, b4b_root] using b63_conj_inverse_reflection [2]
  · simpa [b63_negativeSlot, b4b_root] using b63_conj_inverse_reflection [3]
  · simpa [b63_negativeSlot, b4b_root] using b63_conj_inverse_reflection [0, 0, 2]
  · simpa [b63_negativeSlot, b4b_root] using b63_conj_inverse_reflection [3, 2, 1]

private theorem b63_conj_pow (h a : b4b_Group) (n : ℕ) :
    (h * a * h⁻¹) ^ n = h * a ^ n * h⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, ih]
      group

private theorem b63_order_conj (h a : b4b_Group) :
    orderOf (h * a * h⁻¹) = orderOf a := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [b63_conj_pow]
  constructor
  · intro hn
    calc
      a ^ n = h⁻¹ * (h * a ^ n * h⁻¹) * h := by group
      _ = 1 := by rw [hn]; simp
  · intro hn
    rw [hn]
    simp

private theorem b63_order_reflection (w : List (Fin 4)) :
    orderOf (b4b_reflection w) = orderOf (b4b_generators 0) := by
  exact b63_order_conj (w.map b4b_generators).prod (b4b_generators 0)

private theorem b63_generator_zero_order : orderOf (b4b_generators 0) = 3 := by
  apply orderOf_eq_prime b63_generator_zero_cube
  intro h
  have he := congrArg (fun z : b4b_Group => b4b_toMatrix z 0 0) h
  simp [b4b_generators, b4b_toMatrix, g32R1] at he
  have hw := g32h_omega_sq_add
  rw [show g32h_omega = 1 by linear_combination 3 * he] at hw
  norm_num at hw

private theorem b63_generator_one_order : orderOf (b4b_generators 1) = 3 := by
  apply orderOf_eq_prime b63_generator_one_cube
  intro h
  have he := congrArg (fun z : b4b_Group => b4b_toMatrix z 0 0) h
  simp [b4b_generators, b4b_toMatrix, g32R2] at he
  have hw := g32h_omega_sq_add
  have : g32h_omega = -2 := by linear_combination -3 * he
  rw [this] at hw
  norm_num at hw

private theorem b63_generator_two_square_order : orderOf ((b4b_generators 2) ^ 2) = 2 := by
  apply orderOf_eq_prime
  · calc
      ((b4b_generators 2) ^ 2) ^ 2 = (b4b_generators 2) ^ 4 := by group
      _ = 1 := b63_generator_two_fourth
  · intro h
    have he := congrArg (fun z : b4b_Group => b4b_toMatrix z 3 3) h
    change (g32X g32h_omega ^ 2) 3 3 = (1 : Matrix (Fin 4) (Fin 4) ℂ) 3 3 at he
    rw [pow_two] at he
    rw [papers3b_x_sq g32h_omega g32h_omega_sq_add] at he
    norm_num at he

theorem b63_root_order_aux (j : Fin 13) :
    orderOf (b4b_root j) = if j = 12 then 2 else 3 := by
  fin_cases j
  · change orderOf (b4b_generators 0) = 3
    exact b63_generator_zero_order
  · change orderOf (b4b_generators 0)⁻¹ = 3
    simpa using b63_generator_zero_order
  · change orderOf (b4b_generators 1)⁻¹ = 3
    simpa using b63_generator_one_order
  · change orderOf (b4b_generators 1) = 3
    exact b63_generator_one_order
  · change orderOf (b4b_reflection [2]) = 3
    rw [b63_order_reflection, b63_generator_zero_order]
  · change orderOf (b4b_reflection [2])⁻¹ = 3
    rw [orderOf_inv, b63_order_reflection, b63_generator_zero_order]
  · change orderOf (b4b_reflection [3]) = 3
    rw [b63_order_reflection, b63_generator_zero_order]
  · change orderOf (b4b_reflection [3])⁻¹ = 3
    rw [orderOf_inv, b63_order_reflection, b63_generator_zero_order]
  · change orderOf (b4b_reflection [1, 3, 1]) = 3
    rw [b63_order_reflection, b63_generator_zero_order]
  · change orderOf (b4b_reflection [0, 0, 2])⁻¹ = 3
    rw [orderOf_inv, b63_order_reflection, b63_generator_zero_order]
  · change orderOf (b4b_reflection [3, 2]) = 3
    rw [b63_order_reflection, b63_generator_zero_order]
  · change orderOf (b4b_reflection [3, 2, 1])⁻¹ = 3
    rw [orderOf_inv, b63_order_reflection, b63_generator_zero_order]
  · change orderOf ((b4b_generators 2) ^ 2) = 2
    exact b63_generator_two_square_order

end HodgeLean.Foundations.Program

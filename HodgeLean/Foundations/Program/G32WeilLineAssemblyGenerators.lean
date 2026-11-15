import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrices
import HodgeLean.Foundations.Program.G32PropFourSixDefs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

def g32c_reflections : Fin 5 → g32p_G :=
  ![b4b_generators 0, b4b_generators 1,
    b4b_generators 2 * b4b_generators 0 * (b4b_generators 2)⁻¹,
    b4b_generators 3 * b4b_generators 0 * (b4b_generators 3)⁻¹,
    (b4b_generators 3 * b4b_generators 2) * b4b_generators 0 *
      (b4b_generators 3 * b4b_generators 2)⁻¹]

theorem g32c_generator_orders :
    (b4b_generators 0)^3 = 1 ∧ (b4b_generators 1)^3 = 1 ∧
    (b4b_generators 2)^4 = 1 ∧ (b4b_generators 3)^3 = 1 := by
  have hw := g32h_omega_sq_add
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change (g32R1 g32h_omega)^3 = 1
    rw [g32c_g32R1_matrix]
    simpa only [pow_succ, pow_zero, one_mul] using
      (g32c_r_cube_matrix g32h_omega hw).trans (g32c_identity_matrix g32h_omega)
  · apply Subtype.ext
    change (g32R2 g32h_omega)^3 = 1
    rw [g32c_g32R2_matrix]
    simpa only [pow_succ, pow_zero, one_mul] using
      (g32c_s_cube_matrix g32h_omega hw).trans (g32c_identity_matrix g32h_omega)
  · apply Subtype.ext
    change (g32X g32h_omega)^4 = 1
    rw [g32c_g32X_matrix]
    simpa only [pow_succ, pow_zero, one_mul] using
      (g32c_x_four_matrix g32h_omega hw).trans (g32c_identity_matrix g32h_omega)
  · apply Subtype.ext
    change (g32Y g32h_omega)^3 = 1
    rw [g32c_g32Y_matrix]
    simpa only [pow_succ, pow_zero, one_mul] using
      (g32c_y_cube_matrix g32h_omega hw).trans (g32c_identity_matrix g32h_omega)

theorem g32c_generator_inverses :
    (b4b_generators 0)⁻¹ = (b4b_generators 0)^2 ∧
    (b4b_generators 1)⁻¹ = (b4b_generators 1)^2 ∧
    (b4b_generators 2)⁻¹ = (b4b_generators 2)^3 ∧
    (b4b_generators 3)⁻¹ = (b4b_generators 3)^2 := by
  obtain ⟨hr, hs, hx, hy⟩ := g32c_generator_orders
  exact ⟨inv_eq_of_mul_eq_one_left (by simpa only [← pow_succ] using hr),
    inv_eq_of_mul_eq_one_left (by simpa only [← pow_succ] using hs),
    inv_eq_of_mul_eq_one_left (by simpa only [← pow_succ] using hx),
    inv_eq_of_mul_eq_one_left (by simpa only [← pow_succ] using hy)⟩

theorem g32c_reflection_matrices :
    ∀ i : Fin 5, b4b_toMatrix (g32c_reflections i) =
      ![g32c_M0 g32h_omega, g32c_M1 g32h_omega, g32c_M10 g32h_omega,
        g32c_M12 g32h_omega, g32c_M16 g32h_omega] i := by
  obtain ⟨_, _, hx, hy⟩ := g32c_generator_inverses
  have hw := g32h_omega_sq_add
  have hm0 : b4b_toMatrix (b4b_generators 0) = g32c_M0 g32h_omega :=
    g32c_g32R1_matrix _
  have hm1 : b4b_toMatrix (b4b_generators 1) = g32c_M1 g32h_omega :=
    g32c_g32R2_matrix _
  have hm2 : b4b_toMatrix (b4b_generators 2) = g32c_M2 g32h_omega :=
    g32c_g32X_matrix _
  have hm3 : b4b_toMatrix (b4b_generators 3) = g32c_M3 g32h_omega :=
    g32c_g32Y_matrix _
  have hxi : b4b_toMatrix (b4b_generators 2)⁻¹ = g32c_M7 g32h_omega := by
    rw [hx, map_pow, hm2]
    simpa only [pow_succ, pow_zero, one_mul] using g32c_x_inv_matrix _ hw
  have hyi : b4b_toMatrix (b4b_generators 3)⁻¹ = g32c_M8 g32h_omega := by
    rw [hy, map_pow, hm3]
    simpa only [pow_succ, pow_zero, one_mul] using g32c_y_inv_matrix _ hw
  intro i
  fin_cases i
  · exact hm0
  · exact hm1
  · change b4b_toMatrix (_ * _ * _) = _
    rw [map_mul, map_mul, hm2, hm0, hxi]
    exact g32c_reflection2_matrix _ hw
  · change b4b_toMatrix (_ * _ * _) = _
    rw [map_mul, map_mul, hm3, hm0, hyi]
    exact g32c_reflection3_matrix _ hw
  · change b4b_toMatrix (_ * _ * _) = _
    rw [mul_inv_rev, map_mul, map_mul, map_mul, map_mul, hm3, hm2, hm0, hxi, hyi]
    have hc := g32c_reflection4_matrix g32h_omega hw
    simp only [mul_assoc] at hc
    simp only [mul_assoc]
    exact hc

theorem g32c_reflection_words :
    b4b_generators 2 =
      ([0,3,4,1,4,0,3,4,1,0,3,1].map g32c_reflections).prod ∧
    b4b_generators 3 =
      ([0,1,4,0,1,3,4,2,0,4].map g32c_reflections).prod := by
  have hw := g32h_omega_sq_add
  constructor
  · apply Subtype.ext
    change b4b_toMatrix (b4b_generators 2) =
      b4b_toMatrix (([0,3,4,1,4,0,3,4,1,0,3,1].map g32c_reflections).prod)
    rw [map_list_prod]
    simp only [List.map_map, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Function.comp_apply, g32c_reflection_matrices, mul_one]
    change g32X g32h_omega = _
    rw [g32c_g32X_matrix]
    have hc := (g32c_word_x_matrix g32h_omega hw).symm
    simp only [mul_assoc] at hc
    exact hc
  · apply Subtype.ext
    change b4b_toMatrix (b4b_generators 3) =
      b4b_toMatrix (([0,1,4,0,1,3,4,2,0,4].map g32c_reflections).prod)
    rw [map_list_prod]
    simp only [List.map_map, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Function.comp_apply, g32c_reflection_matrices, mul_one]
    change g32Y g32h_omega = _
    rw [g32c_g32Y_matrix]
    have hc := (g32c_word_y_matrix g32h_omega hw).symm
    simp only [mul_assoc] at hc
    exact hc

theorem g32c_second_reflection_conjugate :
    let h := b4b_generators 0 * b4b_generators 0 * b4b_generators 1
    h * (b4b_generators 0)⁻¹ * h⁻¹ = b4b_generators 1 := by
  obtain ⟨hr, hs, _, _⟩ := g32c_generator_inverses
  have hw := g32h_omega_sq_add
  have hm0 : b4b_toMatrix (b4b_generators 0) = g32c_M0 g32h_omega :=
    g32c_g32R1_matrix _
  have hm1 : b4b_toMatrix (b4b_generators 1) = g32c_M1 g32h_omega :=
    g32c_g32R2_matrix _
  have hri : b4b_toMatrix (b4b_generators 0)⁻¹ = g32c_M42 g32h_omega := by
    rw [hr, map_pow, hm0]
    rw [pow_two]
    exact g32c_r_inv_matrix g32h_omega hw
  have hsi : b4b_toMatrix (b4b_generators 1)⁻¹ = g32c_M40 g32h_omega := by
    rw [hs, map_pow, hm1]
    rw [pow_two]
    exact g32c_s_inv_matrix g32h_omega hw
  dsimp only
  rw [hr]
  apply Subtype.ext
  change b4b_toMatrix ((b4b_generators 0 * b4b_generators 0 * b4b_generators 1) *
    (b4b_generators 0)^2 * (b4b_generators 0 * b4b_generators 0 * b4b_generators 1)⁻¹) =
      b4b_toMatrix (b4b_generators 1)
  simp only [mul_inv_rev, map_mul, map_pow, pow_two, hm0, hm1, hri, hsi]
  have hc := g32c_conjugacy_matrix g32h_omega hw
  simp only [mul_assoc] at hc
  simp only [mul_assoc]
  exact hc

theorem g32c_fixed_by_reflections {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ g32p_G V) (v : V)
    (hv : ∀ i, ρ (g32c_reflections i) v = v) : ∀ g, ρ g v = v := by
  have hprod (L : List (Fin 5)) : ρ ((L.map g32c_reflections).prod) v = v := by
    induction L with
    | nil => simp only [List.map_nil, List.prod_nil, map_one, Module.End.one_apply]
    | cons a L ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih, hv]
  have hx := hprod [0,3,4,1,4,0,3,4,1,0,3,1]
  have hy := hprod [0,1,4,0,1,3,4,2,0,4]
  rw [← g32c_reflection_words.1] at hx
  rw [← g32c_reflection_words.2] at hy
  have hbase : ∀ i, ρ (b4b_generators i) v = v := by
    intro i
    fin_cases i
    · exact hv 0
    · exact hv 1
    · exact hx
    · exact hy
  intro g
  exact Submonoid.closure_induction
    (motive := fun m hm => ρ (⟨m, hm⟩ : g32p_G) v = v)
    (fun m hm => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · exact hbase 0
      · exact hbase 1
      · exact hbase 2
      · exact hbase 3)
    (by change ρ 1 v = v; rw [map_one]; rfl)
    (fun a b ha hb hpa hpb => by
      change ρ ((⟨a, ha⟩ : g32p_G) * ⟨b, hb⟩) v = v
      rw [map_mul]
      rw [Module.End.mul_apply, hpb, hpa]) g.2

end HodgeLean.Foundations.Program

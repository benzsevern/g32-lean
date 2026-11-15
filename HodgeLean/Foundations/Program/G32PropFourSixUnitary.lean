import HodgeLean.Foundations.Program.G32PropFourSixDual
import HodgeLean.Foundations.Program.G32PropFourSixPacked0190

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
open scoped Matrix
set_option maxHeartbeats 400000

theorem g32p_archive_generator_unitary_0 :
    star ((g32p_archiveGenerators 0).submatrix g32p_archiveCoordinates g32p_archiveCoordinates) *
      (g32p_archiveGenerators 0).submatrix g32p_archiveCoordinates g32p_archiveCoordinates = 1 := by
  have hs : (starRingEnd ℂ) g32h_omega = -1 - g32h_omega := conj_omega _ g32h_omega_sq_add
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := star_ofNat 2
  have h3 : (starRingEnd ℂ) (3 : ℂ) = 3 := star_ofNat 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32p_archiveGenerators, g32p_archiveCoordinates, Matrix.submatrix, Matrix.of_apply,
      Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hs, h2, h3] <;>
    ring_nf <;> (try (simp only [HurwitzPrymRex_omega_pow.1])) <;> ring

theorem g32p_archive_generator_unitary_1 :
    star ((g32p_archiveGenerators 1).submatrix g32p_archiveCoordinates g32p_archiveCoordinates) *
      (g32p_archiveGenerators 1).submatrix g32p_archiveCoordinates g32p_archiveCoordinates = 1 := by
  have hs : (starRingEnd ℂ) g32h_omega = -1 - g32h_omega := conj_omega _ g32h_omega_sq_add
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := star_ofNat 2
  have h3 : (starRingEnd ℂ) (3 : ℂ) = 3 := star_ofNat 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32p_archiveGenerators, g32p_archiveCoordinates, Matrix.submatrix, Matrix.of_apply,
      Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hs, h2, h3] <;>
    ring_nf <;> (try (simp only [HurwitzPrymRex_omega_pow.1])) <;> ring

theorem g32p_archive_generator_unitary_2 :
    star ((g32p_archiveGenerators 2).submatrix g32p_archiveCoordinates g32p_archiveCoordinates) *
      (g32p_archiveGenerators 2).submatrix g32p_archiveCoordinates g32p_archiveCoordinates = 1 := by
  have hs : (starRingEnd ℂ) g32h_omega = -1 - g32h_omega := conj_omega _ g32h_omega_sq_add
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := star_ofNat 2
  have h3 : (starRingEnd ℂ) (3 : ℂ) = 3 := star_ofNat 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32p_archiveGenerators, g32p_archiveCoordinates, Matrix.submatrix, Matrix.of_apply,
      Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hs, h2, h3] <;>
    ring_nf <;> (try (simp only [HurwitzPrymRex_omega_pow.1])) <;> ring

theorem g32p_archive_generator_unitary_3 :
    star ((g32p_archiveGenerators 3).submatrix g32p_archiveCoordinates g32p_archiveCoordinates) *
      (g32p_archiveGenerators 3).submatrix g32p_archiveCoordinates g32p_archiveCoordinates = 1 := by
  have hs : (starRingEnd ℂ) g32h_omega = -1 - g32h_omega := conj_omega _ g32h_omega_sq_add
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := star_ofNat 2
  have h3 : (starRingEnd ℂ) (3 : ℂ) = 3 := star_ofNat 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32p_archiveGenerators, g32p_archiveCoordinates, Matrix.submatrix, Matrix.of_apply,
      Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hs, h2, h3] <;>
    ring_nf <;> (try (simp only [HurwitzPrymRex_omega_pow.1])) <;> ring

theorem g32p_archive_generator_unitary (k : Fin 4) :
    star ((g32p_archiveGenerators k).submatrix g32p_archiveCoordinates g32p_archiveCoordinates) *
      (g32p_archiveGenerators k).submatrix g32p_archiveCoordinates g32p_archiveCoordinates = 1 := by
  fin_cases k
  · exact g32p_archive_generator_unitary_0
  · exact g32p_archive_generator_unitary_1
  · exact g32p_archive_generator_unitary_2
  · exact g32p_archive_generator_unitary_3

theorem g32p_actual_matrix_unitary (g : g32p_G) :
    star (b4b_toMatrix g) * b4b_toMatrix g = 1 := by
  have hg : b4b_toMatrix g ∈ Submonoid.closure (Set.range (fun i : Fin 4 =>
      (g32p_archiveGenerators i).submatrix g32p_archiveCoordinates g32p_archiveCoordinates)) := by
    rw [g32p_archive_matrix_closure]
    exact g.property
  generalize hm : b4b_toMatrix g = m at hg ⊢
  clear hm
  induction hg using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨k, rfl⟩ := ha
    exact g32p_archive_generator_unitary k
  | one => simp only [star_one, one_mul]
  | mul a b ha hb iha ihb =>
    rw [star_mul]
    calc
      star b * star a * (a * b) = star b * (star a * a) * b := by simp only [mul_assoc]
      _ = 1 := by rw [iha, mul_one, ihb]

theorem g32p_group_unitary (g : g32p_G) :
    b4b_toMatrix g ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have h : g32h_G ≤ Matrix.unitaryGroup (Fin 4) ℂ := by
    apply Submonoid.closure_le.mpr
    intro M hM
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · exact papers_g32_r1_unitary _ g32h_omega_sq_add
    · exact papers_g32_r2_unitary _ g32h_omega_sq_add
    · exact papers_g32_x_unitary _ g32h_omega_sq_add
    · exact papers_g32_y_unitary _ g32h_omega_sq_add
  exact h g.property

theorem g32p_group_inverse_matrix (g : g32p_G) :
    b4b_toMatrix g⁻¹ = (b4b_toMatrix g)ᴴ := by
  have hu := Matrix.mem_unitaryGroup_iff.mp (g32p_group_unitary g)
  have hi : b4b_toMatrix g * b4b_toMatrix g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact (HurwitzPrymRex_g32_isUnit _ g.property).mul_left_cancel (hi.trans hu.symm)

theorem g32p_rhoDual_conjugate (g : g32p_G) :
    g32p_rhoDual.character g = star (g32p_rho.character g) := by
  rw [g32p_rhoDual_character, g32p_rho_character, g32p_group_inverse_matrix,
    Matrix.trace_conjTranspose, g32p_rho_character]

theorem g32p_rhoDual_not_selfDual : ¬ g32p_SelfDual g32p_rhoDual := by
  intro h
  apply g32p_rho_not_selfDual
  intro g
  have hg := h g
  rw [g32p_rhoDual_conjugate, star_star] at hg
  exact hg.symm

end HodgeLean.Foundations.Program

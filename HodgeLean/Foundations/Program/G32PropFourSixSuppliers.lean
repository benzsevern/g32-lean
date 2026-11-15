import HodgeLean.Foundations.Program.G32PropFourSixCharacters

noncomputable section

open HodgeLean.Papers

namespace HodgeLean.Foundations.Program

theorem g32p_zpowers_generator (g : g32p_G) :
    ∀ x : Subgroup.zpowers g,
      x ∈ Subgroup.zpowers (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) := by
  rintro ⟨x, hx⟩
  obtain ⟨n, rfl⟩ := hx
  exact ⟨n, Subtype.ext (by rfl)⟩

def g32p_cyclicCharacter (g : g32p_G) :
    Subgroup.zpowers g →* Multiplicative (ZMod (orderOf g)) :=
  (zmodMulEquivOfGenerator (g32p_zpowers_generator g) (Nat.card_zpowers g)).symm.toMonoidHom

def g32p_cyclicSupplier (g : g32p_G) (hg : 3 ≤ orderOf g) : g32p_Supplier where
  H := Subgroup.zpowers g
  m := orderOf g
  three_le := hg
  χ := g32p_cyclicCharacter g
  surjective :=
    (zmodMulEquivOfGenerator (g32p_zpowers_generator g) (Nat.card_zpowers g)).symm.surjective

theorem g32p_reflection_cube : (g32p_classDatum 0) ^ 3 = 1 := by
  apply Subtype.ext
  change g32R1 g32h_omega ^ 3 = 1
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32R1, Matrix.mul_apply, Fin.sum_univ_four] <;>
    papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add

theorem g32p_reflection_order : orderOf (g32p_classDatum 0) = 3 := by
  apply orderOf_eq_prime g32p_reflection_cube
  intro hh
  have he := congrArg (fun g : g32p_G => (g : Matrix (Fin 4) (Fin 4) ℂ) 0 0) hh
  change (g32h_omega + 2) / 3 = 1 at he
  have hroot := g32h_omega_sq_add
  have hw : g32h_omega = 1 := by linear_combination 3 * he
  rw [hw] at hroot
  norm_num at hroot

def g32p_reflectionSupplier : g32p_Supplier :=
  g32p_cyclicSupplier (g32p_classDatum 0) (by rw [g32p_reflection_order])

theorem g32p_reflectionSupplier_order : Nat.card g32p_reflectionSupplier.H = 3 := by
  change Nat.card (Subgroup.zpowers (g32p_classDatum 0)) = 3
  rw [Nat.card_zpowers, g32p_reflection_order]

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32PropFourSixNatural
import HodgeLean.Foundations.Program.G32PropFourSixSuppliers

noncomputable section

open CategoryTheory HodgeLean.Papers

namespace HodgeLean.Foundations.Program

theorem g32p_dual_simple {G : Type} [Group G] [Fintype G]
    (V : FDRep ℂ G) (hV : Simple V) : Simple (FDRep.of (Representation.dual V.ρ)) := by
  apply (FDRep.simple_iff_char_is_norm_one _).mpr
  simpa only [FDRep.char_dual, inv_inv, mul_comm] using
    (FDRep.simple_iff_char_is_norm_one V).mp hV

def g32p_rhoDual : FDRep ℂ g32p_G := FDRep.of (Representation.dual g32p_rho.ρ)

theorem g32p_rhoDual_simple : Simple g32p_rhoDual :=
  g32p_dual_simple g32p_rho g32p_rho_simple

theorem g32p_rhoDual_character (g : g32p_G) :
    g32p_rhoDual.character g = g32p_rho.character g⁻¹ :=
  FDRep.char_dual _ _

theorem g32p_rhoDual_character_reflection :
    g32p_rhoDual.character (g32p_classDatum 0) = 3 + g32h_omega ^ 2 := by
  rw [g32p_rhoDual_character]
  have hi : (g32p_classDatum 0)⁻¹ = (g32p_classDatum 0) ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ'] using g32p_reflection_cube
  rw [hi, g32p_rho_character, map_pow]
  change Matrix.trace (g32R1 g32h_omega ^ 2) = _
  norm_num [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four, g32R1]
  papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add

theorem g32p_rhoDual_not_iso : ¬ Nonempty (g32p_rhoDual ≅ g32p_rho) := by
  rintro ⟨h⟩
  have he := congrFun (FDRep.char_iso h) (g32p_classDatum 0)
  rw [g32p_rhoDual_character_reflection, g32p_rho_character_reflection] at he
  have hw : g32h_omega ^ 2 = g32h_omega := by linear_combination he
  have hz : g32h_omega = 1 ∨ g32h_omega = 0 := by
    have hp : g32h_omega * (g32h_omega - 1) = 0 := by linear_combination hw
    rcases mul_eq_zero.mp hp with h0 | h1
    · exact Or.inr h0
    · exact Or.inl (sub_eq_zero.mp h1)
  rcases hz with h | h <;> have hs := g32h_omega_sq_add <;> rw [h] at hs <;> norm_num at hs

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.NumeratorJetFixedContractionEvaluation
import HodgeLean.Foundations.Program.NumeratorJetFixedRecurrenceCertificates

/-! # Fixed-pole field assembly from weighted moving traces -/

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

/-- Natural indexing of the stored complex residue coefficients. -/
def b65e_storedResidue (p : Fin 12 → ℂ) (n : ℕ) :=
  b65e_residueJet p (Fin.ofNat 8 n)

/-- The finite rational contraction evaluates to the stored fixed-pole field. -/
theorem b65e_fixedContraction_field (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (n : Fin 7) (k : Fin 4) (i j : Fin 4) :
    (b65e_fixedContractionQ n k i j : ℂ) =
      b65e_fieldCoeff p (b65e_storedResidue p) n (.inl k) i j := by
  unfold b65e_fieldCoeff
  rw [Fintype.sum_sum_type]
  have hz : (∑ r : Fin 4, if (Sum.inl r : Fin 4 ⊕ Fin 12) = .inl k then (0 : ℂ) else
      ∑ a ∈ Finset.range (n.val + 1), b65e_poleRatioCoeff p (.inl k) (.inl r) a *
      ((∑ t : Fin 4, ∑ b ∈ Finset.range (n.val - a + 1),
        b65e_storedResidue p b (.inl r) i t *
        b65e_storedResidue p (n.val - a - b) (.inl k) t j) -
       (∑ t : Fin 4, ∑ b ∈ Finset.range (n.val - a + 1),
        b65e_storedResidue p b (.inl k) i t *
        b65e_storedResidue p (n.val - a - b) (.inl r) t j))) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    split_ifs
    · rfl
    · apply Finset.sum_eq_zero
      intro a _
      simp only [b65e_poleRatioCoeff, b65p_velocity, Sum.elim_inl,
        Pi.zero_apply, sub_self, zero_div, zero_mul]
  rw [hz, zero_add]
  simp only [reduceCtorEq, ite_false]
  rw [← Finset.sum_fiberwise Finset.univ b65q_fibreIndex]
  unfold b65e_fixedContractionQ
  push_cast
  apply Finset.sum_congr rfl
  intro e _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a < 7 := by have := Finset.mem_range.mp ha; omega
  have hav : (Fin.ofNat 7 a).val = a := by simp [Fin.ofNat_eq_cast, Nat.mod_eq_of_lt ha']
  simp_rw [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  all_goals
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
  · rw [← b65e_weightedMovingQ_sum p O (Fin.ofNat 7 a) (Fin.ofNat 8 b) e k i t]
    simp only [hav, b65e_storedResidue, b65e_residueJet, Matrix.map_apply,
      Rat.coe_castHom]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    ring
  · rw [← b65e_weightedMovingQ_sum p O (Fin.ofNat 7 a)
      (Fin.ofNat 8 (n.val - a - b)) e k t j]
    simp only [hav, b65e_storedResidue, b65e_residueJet, Matrix.map_apply,
      Rat.coe_castHom]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

/-- The stored higher fixed-pole entries satisfy the actual finite field recurrence. -/
theorem b65e_fixed_stored_step (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (n : Fin 6) (k i j : Fin 4) :
    b65e_fieldCoeff p (b65e_storedResidue p) n.succ (.inl k) i j =
      (n.val + 2 : ℂ) * (b65e_fixedJet n.succ.succ k i j : ℂ) := by
  rw [← b65e_fixedContraction_field p O n.succ k i j,
    b65e_fixedContraction_table]
  push_cast
  rfl

/-- Agreement through order n+1 transports the fixed-pole recurrence to order n+2. -/
theorem b65e_fixed_coeff_next (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {P : (Fin 4 ⊕ Fin 12) → Fin 4 → Fin 4 → FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : ∀ q i j, HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) (P q i j) 0)
    (n : Fin 6)
    (hcoeff : ∀ a ≤ n.val + 1, ∀ q i j,
      (P q i j).coeff a = b65e_storedResidue p a q i j)
    (k i j : Fin 4) :
    (P (.inl k) i j).coeff (n.val + 2) = (b65e_fixedJet n.succ.succ k i j : ℂ) := by
  apply mul_left_cancel₀ (show (n.val + 2 : ℂ) ≠ 0 by
    exact_mod_cast (by omega : n.val + 2 ≠ 0))
  have h := b65e_residue_coeff_recurrence p O hP (n.val + 1) (.inl k) i j
  have hc : ∀ a ≤ n.val + 1,
      (fun q i j ↦ (P q i j).coeff a) = b65e_storedResidue p a := by
    intro a ha
    funext q i j
    exact hcoeff a ha q i j
  rw [b65e_fieldCoeff_congr p (n.val + 1) hc] at h
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
    h.trans (b65e_fixed_stored_step p O n k i j)

end HodgeLean.Foundations.Program

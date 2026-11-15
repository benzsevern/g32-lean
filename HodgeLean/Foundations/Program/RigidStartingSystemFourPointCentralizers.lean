import HodgeLean.Foundations.Program.RigidStartingSystemExponentialClasses
import HodgeLean.Foundations.Program.RigidStartingSystemCentralizers

noncomputable section
open Matrix
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b65r_local_centralizer_card (i : Fin 4) :
    Nat.card {p : Fin 4 × Fin 4 //
      b65r_localEigenvalues g32h_omega i p.1 = b65r_localEigenvalues g32h_omega i p.2} =
      (![10,10,6,8] : Fin 4 → ℕ) i := by
  classical
  have hw := g32h_omega_sq_add
  have hw1 : g32h_omega ≠ 1 := by intro h; rw [h] at hw; norm_num at hw
  have hw21 : g32h_omega^2 ≠ 1 := by
    intro h
    have he : g32h_omega = -2 := by linear_combination hw-h
    rw [he] at h
    norm_num at h
  have hw12 : g32h_omega ≠ g32h_omega^2 := by
    intro h
    have he : g32h_omega = -(1/2 : ℂ) := by linear_combination (1/2)*hw+(1/2)*h
    rw [he] at h
    norm_num at h
  have hI1 : Complex.I ≠ (-1 : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hII : Complex.I ≠ -Complex.I := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have h1I : (-1 : ℂ) ≠ -Complex.I := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ]
  fin_cases i <;>
    norm_num [Fin.sum_univ_succ, b65r_localEigenvalues, hw1, hw1.symm, hw21, hw21.symm,
      hw12, hw12.symm, hI1, hI1.symm, hII, hII.symm, h1I, h1I.symm]

theorem b65r_printed_centralizer_finrank (i : Fin 4) :
    Module.finrank ℂ (b65r_centralizer (b4b_toMatrix (b4b_generators i))) =
      (![10,10,6,8] : Fin 4 → ℕ) i := by
  have hG : b4b_toMatrix (b4b_generators i) * (b65r_targetUnit i).val =
      (b65r_targetUnit i).val * diagonal (b65r_localEigenvalues g32h_omega i) := by
    change b4b_toMatrix (b4b_generators i) * b65r_targetBasis g32h_omega i = _
    rw [b65r_printed_matrix]
    exact b65r_target_eigenbasis g32h_omega g32h_omega_sq_add i
  rw [b65r_centralizer_finrank_eigenbasis _ (b65r_targetUnit i) _ hG,
    b65r_local_centralizer_card]

theorem b65r_printed_index :
    b65r_index (fun i ↦ b4b_toMatrix (b4b_generators i)) = 2 := by
  simp only [b65r_index, b65r_printed_centralizer_finrank, Fin.sum_univ_succ]
  norm_num

end HodgeLean.Foundations.Program

module

public import Mathlib.Basic.Complex.Basic
public import HodgeLean.Foundations.Program.KernelFramesProofs

/-! Implication from the explicit rational base systems to their ranks, nonzero blocks,
kernel bases and base numerator coordinates. The family dictionary and frame comparison
remain separate targets.
HC no distance; AV milestone no distance. -/
@[expose] public section

noncomputable section
namespace HodgeLean.Foundations.Program
open Matrix

/-- The base Laurent system has the printed rank.
Source: G32 v0.16, Lemma kernel(3), Subsection 5.5(5)–(6). -/
theorem b65k_r_rank :
    b65k_rSystem.rank = 33 := b65k_r_rank_aux

example := @b65k_r_rank

/-- The first independent row selection gives a nonsingular pivot block.
Source: G32 v0.16, Lemma kernel(3), Subsection 5.5(5)–(6). -/
theorem b65k_r_block :
    b65k_rBlock.det ≠ 0 := b65k_r_block_aux

example := @b65k_r_block

/-- Inverse-block columns form the kernel basis with the specified free coordinates.
Source: G32 v0.16, Lemma kernel(3), Subsection 5.5(5)–(6). -/
theorem b65k_r_basis :
    LinearIndependent ℚ (fun f : Fin 3 => fun i => b65k_rKernel i f) ∧
    Submodule.span ℚ (Set.range (fun f : Fin 3 => fun i => b65k_rKernel i f)) =
      LinearMap.ker b65k_rSystem.mulVecLin ∧
    (∀ a f : Fin 3, b65k_rKernel (b65k_rFree a) f = if a = f then 1 else 0) := b65k_r_basis_aux

example := @b65k_r_basis

/-- The base Laurent system has the printed rank.
Source: G32 v0.16, Lemma kernel(3), Subsection 5.5(5)–(6). -/
theorem b65k_q_rank :
    b65k_qSystem.rank = 45 := b65k_q_rank_aux

example := @b65k_q_rank

/-- The first independent row selection gives a nonsingular pivot block.
Source: G32 v0.16, Lemma kernel(3), Subsection 5.5(5)–(6). -/
theorem b65k_q_block :
    b65k_qBlock.det ≠ 0 := b65k_q_block_aux

example := @b65k_q_block

/-- Inverse-block columns form the kernel basis with the specified free coordinates.
Source: G32 v0.16, Lemma kernel(3), Subsection 5.5(5)–(6). -/
theorem b65k_q_basis :
    LinearIndependent ℚ (fun f : Fin 3 => fun i => b65k_qKernel i f) ∧
    Submodule.span ℚ (Set.range (fun f : Fin 3 => fun i => b65k_qKernel i f)) =
      LinearMap.ker b65k_qSystem.mulVecLin ∧
    (∀ a f : Fin 3, b65k_qKernel (b65k_qFree a) f = if a = f then 1 else 0) := b65k_q_basis_aux

example := @b65k_q_basis

/-- The infinity equations rule out the rank-zero replacement.
Source: G32 v0.16, Subsection 5.5(5). -/
example : b65k_rSystem ≠ 0 ∧ b65k_qSystem ≠ 0 := by
  constructor
  · intro h
    have hentry := congrArg (fun M : Matrix (Fin 45) (Fin 36) ℚ => M 41 0) h
    norm_num [b65k_rSystem] at hentry
  · intro h
    have hentry := congrArg (fun M : Matrix (Fin 57) (Fin 48) ℚ => M 53 0) h
    norm_num [b65k_qSystem] at hentry

/-- The free-coordinate selections have three distinct entries.
Source: G32 v0.16, Subsection 5.5(6). -/
example : Function.Injective b65k_rFree ∧ Function.Injective b65k_qFree := by
  constructor <;> intro a b h <;> fin_cases a <;> fin_cases b <;>
    norm_num [b65k_rFree, b65k_qFree] at *

/-- All base contractions have denominator one and degree at most nine.
Source: G32 v0.16, Lemma numerators, Subsection 5.5(7). -/
theorem b65k_base_numerator :
    ∀ a b : Fin 3, (b65k_baseProduct a b).denom = 1 ∧
      (b65k_baseNumerator a b).natDegree ≤ 9 := b65k_base_numerator_aux

example := @b65k_base_numerator

/-- The ordered ten coefficient columns reconstruct the base contraction.
Source: G32 v0.16, Lemma numerators, Subsection 5.5(7). -/
theorem b65k_base_coefficients :
    ∀ a b : Fin 3,
      (∑ j : Fin 10, RatFunc.C (b65k_baseMatrix (finProdFinEquiv (a,b)) j) *
        RatFunc.X^j.val) = b65k_baseProduct a b := b65k_base_coefficients_aux

example := @b65k_base_coefficients

/-- Each inverse-block column has a nonzero prescribed coordinate independently of the targets.
Source: G32 v0.16, Lemma kernel(3), Subsection 5.5(6). -/
example (f : Fin 3) : b65k_rKernel (b65k_rFree f) f = 1 := by
  fin_cases f
  all_goals norm_num [b65k_rKernel, b65k_rFree, b65k_rPivot, Fin.sum_univ_succ]
  all_goals decide

example (f : Fin 3) : b65k_qKernel (b65k_qFree f) f = 1 := by
  fin_cases f
  all_goals norm_num [b65k_qKernel, b65k_qFree, b65k_qPivot, Fin.sum_univ_succ]
  all_goals decide

/-- The base array defines a map with the input and output dimensions of the period derivative.
Source: G32 v0.16, Subsection 5.5(7); g32r_PeriodMap.codiff. -/
example : (Fin 10 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ) :=
  (b65k_baseMatrix.map (Rat.castHom ℂ)).mulVecLin

end HodgeLean.Foundations.Program

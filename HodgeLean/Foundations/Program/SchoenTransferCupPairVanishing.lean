import HodgeLean.Foundations.Program.SchoenTransferComplexCup
import HodgeLean.Adapters.HodgeFromCupLeftProofs

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- A degree-one factor pairing to zero with one entry annihilates the iterated cup.
Source: Hatcher, Algebraic Topology, §3.2, associativity and graded commutativity. -/
theorem s4_cupC_iterated_zero (μ : CupProduct X) :
    ∀ (n : ℕ) (x : ℂ ⊗[ℚ] HQ X 1) (v : Fin n → ℂ ⊗[ℚ] HQ X 1) (j : Fin n),
      μ.cupC (show 1 + 1 = 2 from rfl) x (v j) = 0 →
      μ.cupC (Nat.add_comm 1 n) x (μ.cupMultiC n v) = 0
  | 0, _, _, j, _ => j.elim0
  | n + 1, x, v, j, hp => by
      rw [CupProduct.cupMultiC_succ,
        ← cupC_assoc μ (rfl : 1 + 1 = 2) (Nat.add_comm 1 n)
          (by omega) (Nat.add_comm 1 (n + 1))]
      cases j using Fin.cases with
      | zero => rw [hp, map_zero, LinearMap.zero_apply]
      | succ j =>
          have hs : μ.cupC (rfl : 1 + 1 = 2) x (v 0) =
              - μ.cupC rfl (v 0) x := by
            simpa only [Nat.mul_one, pow_one, neg_one_smul] using
              hlredA_cupC_comm μ (rfl : 1 + 1 = 2) rfl (v 0) x
          rw [hs, map_neg, LinearMap.neg_apply,
            cupC_assoc μ (rfl : 1 + 1 = 2) (Nat.add_comm 1 n)
              (by omega) (Nat.add_comm 1 (n + 1))]
          have ih := s4_cupC_iterated_zero μ n x (Fin.tail v) j hp
          rw [ih, map_zero, neg_zero]

/-- A zero pairing between two distinct degree-one factors annihilates their full cup.
Source: Hatcher, Algebraic Topology, §3.2, associativity and graded commutativity. -/
theorem s4_cupMultiC_zero_of_pair (μ : CupProduct X) :
    ∀ (n : ℕ) (v : Fin n → ℂ ⊗[ℚ] HQ X 1) (i j : Fin n), i ≠ j →
      μ.cupC (show 1 + 1 = 2 from rfl) (v i) (v j) = 0 → μ.cupMultiC n v = 0
  | 0, _, i, _, _, _ => i.elim0
  | n + 1, v, i, j, hij, hp => by
      rw [CupProduct.cupMultiC_succ]
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j => exact s4_cupC_iterated_zero μ n (v 0) (Fin.tail v) j hp
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              have hs := hlredA_cupC_comm μ (rfl : 1 + 1 = 2) rfl (v i.succ) (v 0)
              have hp' : μ.cupC (rfl : 1 + 1 = 2) (v 0) (v i.succ) = 0 := by
                rw [hp, smul_zero] at hs
                exact hs
              exact s4_cupC_iterated_zero μ n (v 0) (Fin.tail v) i hp'
          | succ j =>
              have hn : i ≠ j := fun he => hij (congrArg Fin.succ he)
              rw [s4_cupMultiC_zero_of_pair μ n (Fin.tail v) i j hn hp, map_zero]

end HodgeLean.Foundations.Program

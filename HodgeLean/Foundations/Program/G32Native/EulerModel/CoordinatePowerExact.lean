import HodgeLean.Foundations.Program.G32Native.EulerModel.CoordinatePowerSpan

/-! # Exact powers from normalized coordinate hyperplanes -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Exact singleton normalization determines the coefficient-one cup power of every positive-codimension actual coordinate intersection. -/
theorem coordinate_power_of_singleton_normalization
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (H : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint Q)) 2)
    (hH : ∀ (j : Fin (k + 1)) (hj : ({j} : Finset (Fin (k + 1))).card ≤ k),
      cupComparison Q 2 (coordinate_class_at_degree Q k eQ {j} hj 1
        (Finset.card_singleton j)) = H)
    (n : ℕ) (T : Finset (Fin (k + 1))) (hT : T.card ≤ k) (hn : T.card = n) (hpos : 0 < n) :
    cupComparison Q (2 * n) (coordinate_class_at_degree Q k eQ T hT n hn) =
      s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H n := by
  classical
  induction n using Nat.strong_induction_on generalizing T with
  | h n ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hn
        have hpow : s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H 1 = H := by
          change HodgeLean.Foundations.Singular.cup _ (Nat.add_zero 2) H
            (HodgeLean.Foundations.Singular.unit _) = H
          exact HodgeLean.Foundations.Singular.cup_one _ H
        rw [hpow]
        exact hH j hT
      | succ n =>
        obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
        let U := T.erase j
        have hU : U.card = n + 1 := by
          dsimp only [U]
          rw [Finset.card_erase_of_mem hj, hn]
          omega
        have hUb : U.card ≤ k := (Finset.card_le_card (Finset.erase_subset j T)).trans hT
        have hsing : ({j} : Finset (Fin (k + 1))).card ≤ k := by
          simp only [Finset.card_singleton]; omega
        have hUnion : U ∪ ({j} : Finset (Fin (k + 1))) = T := by
          rw [Finset.union_comm]
          simp only [Finset.singleton_union, U, Finset.insert_erase hj]
        have hUnionb : (U ∪ ({j} : Finset (Fin (k + 1)))).card ≤ k := by
          rw [hUnion]; exact hT
        have hUnionc : (U ∪ ({j} : Finset (Fin (k + 1)))).card = (n + 1) + 1 := by
          rw [hUnion, hn]
        have hr := ih (n + 1) (by omega) U hUb hU (by omega)
        have hs := hH j hsing
        have hprod := coordinate_class_at_degree_cup Q k eQ U {j} hUb hsing hUnionb
          (n + 1) 1 hU (Finset.card_singleton j) hUnionc
        have hmap := congrArg (cupComparison Q (2 * (n + 1 + 1))) hprod
        rw [cupComparison_cup, hr, hs] at hmap
        have hcomm : HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint Q))
            (show 2 * (n + 1) + 2 = 2 * (n + 1 + 1) by omega)
            (s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H (n + 1)) H =
          HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint Q))
            (show 2 + 2 * (n + 1) = 2 * (n + 1 + 1) by omega)
            H (s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H (n + 1)) := by
          simpa only [pow_mul, neg_one_sq, one_pow, one_smul] using
            HodgeLean.Foundations.Singular.cup_comm_graded (TopCat.of (ComplexPoint Q))
              (show 2 + 2 * (n + 1) = 2 * (n + 1 + 1) by omega)
              (show 2 * (n + 1) + 2 = 2 * (n + 1 + 1) by omega)
              H (s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H (n + 1))
        rw [hcomm] at hmap
        simpa only [hUnion, s2e_hyperplanePower] using hmap.symm

#print axioms coordinate_power_of_singleton_normalization
end HodgeLean.Foundations.Program.G32Native.EulerModel

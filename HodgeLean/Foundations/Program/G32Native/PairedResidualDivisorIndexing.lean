import HodgeLean.Foundations.Program.G32Native.PairedResidualResidueRank

/-! # Literal multiplicity indices of an effective divisor -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The support-indexed coefficient space has exactly one index per divisor
multiplicity, without reducing repeated points.
Source: Forster, Lectures on Riemann Surfaces, §18. -/
theorem residual_effective_divisor_support_cardinality
    {C : Type} (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) {n : ℕ}
    (hn : b4c_deg D = (n : ℤ)) :
    Fintype.card (Σ i : D.support, Fin (Int.toNat (D i.1))) = n := by
  classical
  have he : (Fintype.card (Σ i : D.support, Fin (Int.toNat (D i.1))) : ℤ) = b4c_deg D := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    simp_rw [Int.toNat_of_nonneg (hD _)]
    exact Finset.sum_attach D.support (fun p => D p)
  exact_mod_cast he.trans hn

#print axioms residual_effective_divisor_support_cardinality

/-- The literal support multiplicities enumerate the original integer divisor.
Source: Forster, Lectures on Riemann Surfaces, §18. -/
theorem residual_effective_divisor_support_enumeration
    {C : Type} (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) {n : ℕ}
    (hn : b4c_deg D = (n : ℤ)) :
    ∃ ι : (Σ i : D.support, Fin (Int.toNat (D i.1))) ≃ Fin n,
      D = ∑ j, Finsupp.single (ι.symm j).1.1 (1 : ℤ) := by
  classical
  let ι : (Σ i : D.support, Fin (Int.toNat (D i.1))) ≃ Fin n :=
    Fintype.equivOfCardEq (by
      simpa only [Fintype.card_fin] using residual_effective_divisor_support_cardinality D hD hn)
  refine ⟨ι, ?_⟩
  have hs : (∑ i : D.support, Finsupp.single i.1 (D i.1)) = D :=
    (Finset.sum_attach D.support (fun p => Finsupp.single p (D p))).trans D.sum_single
  have hm (i : D.support) :
      (∑ _ : Fin (Int.toNat (D i.1)), Finsupp.single i.1 (1 : ℤ)) =
        Finsupp.single i.1 (D i.1) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finsupp.smul_single, nsmul_eq_mul, mul_one, Int.toNat_of_nonneg (hD i.1)]
  calc
    D = ∑ i : D.support, Finsupp.single i.1 (D i.1) := hs.symm
    _ = ∑ i : D.support, ∑ _ : Fin (Int.toNat (D i.1)), Finsupp.single i.1 (1 : ℤ) :=
      Finset.sum_congr rfl (fun i _ => (hm i).symm)
    _ = ∑ t : Σ i : D.support, Fin (Int.toNat (D i.1)), Finsupp.single t.1.1 (1 : ℤ) := by
      rw [Fintype.sum_sigma]
    _ = ∑ j, Finsupp.single (ι.symm j).1.1 (1 : ℤ) := (ι.symm.sum_comp _).symm

#print axioms residual_effective_divisor_support_enumeration
end HodgeLean.Foundations.Program.G32Native

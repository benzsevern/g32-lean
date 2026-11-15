import HodgeLean.Foundations.Program.SchoenCycleElementaryIdealPowers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Positive elementary coefficients belong to the root-coordinate ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_positive_elementary_mem_origin
    {σ : Type*} [Fintype σ] (k : ℕ) (hk : 0 < k) :
    esymm σ ℂ k ∈ idealOfVars σ ℂ := by
  classical
  unfold esymm
  apply Ideal.sum_mem
  intro s hs
  have hcard : s.card = k := (Finset.mem_powersetCard.mp hs).2
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (hcard ▸ hk)
  rw [← Finset.prod_erase_mul _ _ hi]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

#print axioms s2e_positive_elementary_mem_origin
end HodgeLean.Foundations.Program

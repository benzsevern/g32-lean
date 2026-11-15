import HodgeLean.Foundations.Program.SchoenTowerI2aMonicCoordinates
import HodgeLean.Foundations.Program.SchoenTowerI2aBranchEvaluationDescent

/-! # Simultaneous branch products on the descended symmetric coefficient chart
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Distinct specified branch products occupy prescribed etale coordinate slots on the actual descended coefficient algebra.
Source: Schoen (1988), Lemma 2.2; Vieta's formula and invertible branch evaluation coordinates. -/
theorem s2v_i2a_etale_symmetric_branch_products
    (k B D : Type) [Field k] [Infinite k] [CommRing B] [Nontrivial B]
    [CommRing D] [Algebra k B] [Algebra k D]
    (n : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] D) (hcEt : c.toRingHom.Etale)
    (q : D →ₐ[k] B) (z : Fin n → B)
    (hc : ∀ j, q (c (MvPolynomial.X j)) =
      MvPolynomial.aeval (R := k) z (MvPolynomial.esymm (Fin n) k (j.val + 1)))
    {J : Type} [Finite J] (κ : J ↪ Fin n) (b : J → k) (hb : Function.Injective b) :
    ∃ cBranch : MvPolynomial (Fin n) k →ₐ[k] D, cBranch.toRingHom.Etale ∧
      ∀ j, q (cBranch (MvPolynomial.X (κ j))) =
        ∏ i, (algebraMap k B (b j) - z i) := by
  obtain ⟨cMon, hcMonEt, hcMon⟩ := s2v_i2a_etale_monic_coefficient_chart k B D n c hcEt q z hc
  obtain ⟨cBranch, hcBranchEt, hcoords⟩ :=
    s2v_i2a_etale_selected_branch_evaluations k D n cMon hcMonEt κ b hb
  refine ⟨cBranch, hcBranchEt, ?_⟩
  intro j
  rw [hcoords j]
  exact s2v_i2a_descended_branch_evaluation n cMon q z hcMon (b j)

/-- Distinct branch values occurring among the actual root evaluations select distinct coordinate slots.
Source: Elementary finite root selection and injectivity of the specified branch values. -/
theorem s2v_i2a_present_branch_slots
    {k J : Type*} (n : ℕ) (values : Fin n → k) (b : J → k)
    (hb : Function.Injective b) (hpresent : ∀ j, ∃ i, values i = b j) :
    ∃ κ : J ↪ Fin n, ∀ j, values (κ j) = b j := by
  classical
  choose f hf using hpresent
  refine ⟨⟨f, ?_⟩, hf⟩
  intro i j hij
  apply hb
  exact (hf i).symm.trans ((congrArg values hij).trans (hf j))

end HodgeLean.Foundations.Program

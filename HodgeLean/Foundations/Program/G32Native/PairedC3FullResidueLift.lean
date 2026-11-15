import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.ThirdKindDivisor

/-! # Arbitrary complex residues in the full simple-pole system -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TauCeti.Contour
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped Manifold ContDiff Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Every complex residue vector of total zero occurs in the full
simple-pole differential system on the specified marked points.
Source: Forster, Lectures on Riemann Surfaces, §18, differentials of the
third kind; Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(i). -/
theorem paired_c3_full_residue_lift (h : Module.finrank ℂ E = 1)
    (n : ℕ) (y : Fin (n + 1) → C) (hy : Function.Injective y)
    (a : Fin (n + 1) → ℂ) (ha : ∑ i, a i = 0) :
    ∃ w : b4c_MeroForm E C h,
      (∀ i, b4c_res (hE := h) w (y i) = a i) ∧
      (∀ p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w p) 0) ∧
      ∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc h w p) 0 := by
  classical
  have hne (i : Fin n) : y (Fin.last n) ≠ y i.castSucc := by
    intro he
    have hi := congrArg Fin.val (hy he)
    simp only [Fin.val_last, Fin.val_castSucc] at hi
    omega
  choose v hv using fun i : Fin n =>
    s2e_regular_two_point_differential h (y (Fin.last n)) (y i.castSucc) (hne i)
  let w : b4c_MeroForm E C h :=
    ⟨∑ i : Fin n, a i.castSucc • (v i : TangentBundle 𝓘(ℂ, E) C → ℂ),
      meromorphicForm_finite_linear_combination h v (fun i => a i.castSucc)⟩
  have hloc (p : C) : HurwitzPrymRR_loc h w p =
      ∑ i : Fin n, a i.castSucc • HurwitzPrymRR_loc h (v i) p := by
    funext z
    simp only [w, HurwitzPrymRR_loc, b4cov_coef, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j
    change b4c_res (hE := h)
      (∑ i : Fin n, a i.castSucc • (v i : TangentBundle 𝓘(ℂ, E) C → ℂ)) (y j) = _
    rw [s2e_residue_linear_combination]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [fun i => (hv i).1, mul_neg, mul_one, Finset.sum_neg_distrib]
      rw [Fin.sum_univ_castSucc] at ha
      exact neg_eq_iff_add_eq_zero.mpr ha
    · have hr (i : Fin n) : b4c_res (hE := h) (v i) (y j.castSucc) =
          if i = j then 1 else 0 := by
        by_cases hij : i = j
        · subst i
          simp only [ite_true]
          exact (hv j).2.1
        · rw [ite_eq_right hij]
          apply residue_eq_zero_of_analyticAt
          apply (hv i).2.2.2
          · exact (hne j).symm
          · intro he
            exact hij (Fin.castSucc_injective n (hy he.symm))
      simp only [hr, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
  · intro p
    rw [hloc]
    apply s2e_meromorphic_order_sum_lower_bound Finset.univ _ 0 (-1)
    · intro i _
      exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a i.castSucc) 0).meromorphicAt.smul
        ((v i).property.2 p)
    · intro i _
      by_cases hai : a i.castSucc = 0
      · rw [hai, zero_smul]
        change (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun _ : ℂ => (0 : ℂ)) 0
        rw [meromorphicOrderAt_const, ite_eq_left rfl]
        exact le_top
      · rw [meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hai]
        exact (hv i).2.2.1 p
  · intro p hp
    rw [hloc]
    apply Finset.analyticAt_sum Finset.univ
    intro i _
    exact analyticAt_const.smul ((hv i).2.2.2 p
      (fun he => hp ⟨Fin.last n, he.symm⟩)
      (fun he => hp ⟨i.castSucc, he.symm⟩))

#print axioms paired_c3_full_residue_lift
end HodgeLean.Foundations.Program.G32Native

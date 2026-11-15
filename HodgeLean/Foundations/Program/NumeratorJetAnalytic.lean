import HodgeLean.Foundations.Program.NumeratorJetAlgebra
import HodgeLean.Foundations.Program.KernelFramesFamily

noncomputable section
open Polynomial Set Metric
namespace HodgeLean.Foundations.Program

theorem b65e_polyPart_sum {ι : Type*} (S : Finset ι) (f : ι → RatFunc ℂ) :
    b65e_polyPart (∑ i ∈ S, f i) = ∑ i ∈ S, b65e_polyPart (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [b65e_polyPart]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, b65e_polyPart_add, ih]

def b65e_fixedFactor (a : Fin 9) : ℂ[X] :=
  (X - C (b65p_fixedPole (b65k_poleIndex a))) ^ b65k_poleOrder a

def b65e_erasedD (p : Fin 12 → ℂ) (θ : ℂ) (x : Fin 12) : ℂ[X] :=
  X * ∏ y ∈ Finset.univ.erase x, (X - C (b65p_poles p θ (Sum.inr y)))

theorem b65e_fixedFactor_monic (a : Fin 9) : (b65e_fixedFactor a).Monic :=
  (monic_X_sub_C _).pow _

theorem b65e_erasedD_mul (p : Fin 12 → ℂ) (θ : ℂ) (x : Fin 12) :
    (X - C (b65p_poles p θ (Sum.inr x))) * b65e_erasedD p θ x =
      b65q_denominator (b65p_poles p θ) := by
  rw [b65e_erasedD, b65q_denominator, mul_left_comm,
    Finset.mul_prod_erase Finset.univ (fun y : Fin 12 ↦ X - C (b65p_poles p θ (Sum.inr y))) (Finset.mem_univ x)]

theorem b65e_product_expand (p : Fin 12 → ℂ) (θ : ℂ)
    (w : Fin 12 → Fin 4 → ℂ) (c : Fin 36 → ℂ) (d : Fin 48 → ℂ) :
    b65q_product (b65p_poles p θ) p w c d =
      ∑ j : Fin 4,
        ((∑ b : Fin 9, ∑ a : Fin 9,
          RatFunc.C (d ⟨4 * b.val + j.val, by omega⟩ * c ⟨4 * a.val + j.val, by omega⟩) *
            (algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator (b65p_poles p θ)) /
              algebraMap ℂ[X] (RatFunc ℂ) (b65e_fixedFactor b * b65e_fixedFactor a))) +
        ∑ x : Fin 12, ∑ a : Fin 9,
          RatFunc.C (((∑ v : Fin 6,
            d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * p x ^ v.val) * w x j) *
              c ⟨4 * a.val + j.val, by omega⟩) *
            (algebraMap ℂ[X] (RatFunc ℂ) (b65e_erasedD p θ x) /
              algebraMap ℂ[X] (RatFunc ℂ) (b65e_fixedFactor a))) := by
  unfold b65q_product b65q_qVector b65q_principal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [add_mul, mul_add]
  congr 1
  · rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [b65p_poles, Sum.elim_inl]
    simp only [b65e_fixedFactor, map_mul, map_pow, map_sub, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C, div_eq_mul_inv]
    ring
  · rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hD := congrArg (algebraMap ℂ[X] (RatFunc ℂ)) (b65e_erasedD_mul p θ x)
    simp only [map_mul, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] at hD
    have hne : RatFunc.X - RatFunc.C (b65p_poles p θ (Sum.inr x)) ≠ 0 := by
      simpa only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
        RatFunc.algebraMap_ne_zero (monic_X_sub_C (b65p_poles p θ (Sum.inr x))).ne_zero
    have hF : algebraMap ℂ[X] (RatFunc ℂ) (b65e_fixedFactor a) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (b65e_fixedFactor_monic a).ne_zero
    rw [← hD]
    simp only [b65p_poles, Sum.elim_inl, b65e_fixedFactor, map_pow, map_sub,
      RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_mul] at hF hne ⊢
    field_simp [hne, hF]

theorem b65e_branch_coeff_an {s : Set ℂ} (p : Fin 12 → ℂ)
    (S : Finset (Fin 12)) (j : ℕ) :
    AnalyticOnNhd ℂ (fun θ ↦
      (X * ∏ x ∈ S, (X - C (b65p_poles p θ (Sum.inr x)))).coeff j) s := by
  apply b65e_analytic_mul_coeff _ _ (fun k ↦ analyticOnNhd_const) _ j
  exact b65e_analytic_prod_coeff S _ (fun x ↦ by
    simp only [b65p_poles, Sum.elim_inr]
    exact analyticOnNhd_const.add (analyticOnNhd_id.mul analyticOnNhd_const))

theorem b65e_branch_degree (p : Fin 12 → ℂ) (S : Finset (Fin 12)) (θ : ℂ) :
    (X * ∏ x ∈ S, (X - C (b65p_poles p θ (Sum.inr x)))).natDegree = 1 + S.card := by
  have hprod := monic_prod_of_monic S _ (fun x _ ↦ monic_X_sub_C (b65p_poles p θ (Sum.inr x)))
  rw [monic_X.natDegree_mul hprod, natDegree_X,
    natDegree_prod_of_monic S _ (fun x _ ↦ monic_X_sub_C (b65p_poles p θ (Sum.inr x)))]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]

theorem b65e_term_an {s : Set ℂ} (F : ℂ → ℂ[X]) (B : ℂ[X]) (hB : B.Monic)
    (d : ℕ) (hdeg : ∀ θ, (F θ).natDegree < d)
    (hF : ∀ k, AnalyticOnNhd ℂ (fun θ ↦ (F θ).coeff k) s)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s) (j : ℕ) :
    AnalyticOnNhd ℂ (fun θ ↦ (b65e_polyPart (RatFunc.C (f θ) *
      (algebraMap ℂ[X] (RatFunc ℂ) (F θ) / algebraMap ℂ[X] (RatFunc ℂ) B))).coeff j) s := by
  simp only [b65e_polyPart_C_mul, b65e_polyPart_div _ _ hB, Polynomial.coeff_smul, smul_eq_mul]
  exact hf.mul (b65e_analytic_div_coeff F B d hdeg hF j)

theorem b65e_product_coeff_an {s : Set ℂ} (p : Fin 12 → ℂ)
    (w : ℂ → Fin 12 → Fin 4 → ℂ) (c : ℂ → Fin 36 → ℂ) (d : ℂ → Fin 48 → ℂ)
    (hw : ∀ x j, AnalyticOnNhd ℂ (fun θ ↦ w θ x j) s)
    (hc : ∀ i, AnalyticOnNhd ℂ (fun θ ↦ c θ i) s)
    (hd : ∀ i, AnalyticOnNhd ℂ (fun θ ↦ d θ i) s) (k : ℕ) :
    AnalyticOnNhd ℂ (fun θ ↦
      (b65e_polyPart (b65q_product (b65p_poles p θ) p (w θ) (c θ) (d θ))).coeff k) s := by
  have hD : ∀ θ, (b65q_denominator (b65p_poles p θ)).natDegree < 14 := by
    intro θ
    rw [b65q_denominator, b65e_branch_degree]
    decide
  have hE : ∀ x θ, (b65e_erasedD p θ x).natDegree < 14 := by
    intro x θ
    rw [b65e_erasedD, b65e_branch_degree]
    simp
  simp only [b65e_product_expand, b65e_polyPart_sum, b65e_polyPart_add,
    Polynomial.finsetSum_coeff, Polynomial.coeff_add]
  apply b65q_an_sum Finset.univ
  intro j _
  apply AnalyticOnNhd.add
  · apply b65q_an_sum Finset.univ
    intro b _
    apply b65q_an_sum Finset.univ
    intro a _
    exact b65e_term_an _ _ ((b65e_fixedFactor_monic b).mul (b65e_fixedFactor_monic a))
      14 hD (fun n ↦ b65e_branch_coeff_an p Finset.univ n)
      _ ((hd _).mul (hc _)) k
  · apply b65q_an_sum Finset.univ
    intro x _
    apply b65q_an_sum Finset.univ
    intro a _
    apply b65e_term_an _ _ (b65e_fixedFactor_monic a) 14 (hE x)
      (fun n ↦ b65e_branch_coeff_an p (Finset.univ.erase x) n) _ _ k
    apply AnalyticOnNhd.mul _ (hc _)
    apply AnalyticOnNhd.mul _ (hw x j)
    exact b65q_an_sum Finset.univ (fun v _ ↦ (hd _).mul analyticOnNhd_const)

theorem b65e_entries_analytic (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      ∀ i : Fin 9, ∀ j : Fin 10,
        AnalyticOnNhd ℂ (fun θ ↦ b65e_numerator p O.residue θ i j) (ball 0 ε) := by
  obtain ⟨r, hr, hrr, hR, hQ, _⟩ := b65q_frames p O
  obtain ⟨t, ht, _, _, hw, _⟩ := b65q_normalizations p O
  refine ⟨min r t, lt_min hr ht, (min_le_left r t).trans hrr, ?_⟩
  intro i j
  let a := ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1
  let b := ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2
  exact b65e_product_coeff_an p (b65q_left O.residue)
    (fun θ l ↦ b65q_rFrame p O.residue θ l a)
    (fun θ l ↦ b65q_qFrame p O.residue θ l b)
    (fun x l ↦ (hw x l).mono (ball_subset_ball (min_le_right r t)))
    (fun l ↦ (hR l a).mono (ball_subset_ball (min_le_left r t)))
    (fun l ↦ (hQ l b).mono (ball_subset_ball (min_le_left r t))) j.val


end HodgeLean.Foundations.Program

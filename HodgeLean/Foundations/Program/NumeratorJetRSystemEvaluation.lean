import HodgeLean.Foundations.Program.NumeratorJetGaugeEvaluation

/-! # Taylor coefficients of the r-system along the path -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

local notation "ι" => Rat.castHom ℂ

/-- Taylor coefficients of an analytic germ times a constant. -/
theorem b65e_T_mul_const_coeff (f : ℂ → ℂ) (c : ℂ) (hf : AnalyticAt ℂ f 0) (d : ℕ) :
    PowerSeries.coeff d (b65q_T (fun θ ↦ f θ * c) 0) = PowerSeries.coeff d (b65q_T f 0) * c := by
  rw [b65q_T_mul (g := fun _ ↦ c) hf analyticAt_const, b65q_T_const, PowerSeries.coeff_mul_C]

/-- The Taylor coefficients of a principal Laurent entry with fixed poles are the rational
principal entry of the Taylor coefficients. -/
theorem b65e_principalEntry_T (p : Fin 12 → ℂ) (K : ℂ → Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (KQ : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℚ) (d : ℕ)
    (hK : ∀ k m, m ≤ 5 → ∀ i j, AnalyticAt ℂ (fun θ ↦ K θ k m i j) 0)
    (hKQ : ∀ k m, m ≤ 5 → b65e_TC (fun θ ↦ K θ k m) d = (KQ k m).map ι)
    (k j : Fin 4) (n : ℤ) (hn : n ≤ 2) (c : Fin 36) :
    PowerSeries.coeff d (b65q_T (fun θ ↦ b65q_principalEntry (b65p_poles p θ) (K θ) k j n c) 0) =
      ((b65q_principalEntryQ KQ k j n c : ℚ) : ℂ) := by
  have ho := b65q_poleOrder_le ⟨c.val / 4, by omega⟩
  unfold b65q_principalEntry b65q_principalEntryQ
  simp only [b65q_poles_inl]
  split_ifs with h1 h2 h3
  · have h := congrFun (congrFun (hKQ k (n + b65k_poleOrder ⟨c.val / 4, by omega⟩).toNat
      (by omega)) j) ⟨c.val % 4, by omega⟩
    simp only [b65e_TC, Matrix.of_apply, Matrix.map_apply] at h
    rw [h, Rat.coe_castHom]
  · rw [b65q_T_const, PowerSeries.coeff_C]
    split_ifs <;> simp
  · have hs := b65q_T_sum (a := 0) (Finset.range (n.toNat + 1))
      (f := fun l θ ↦ K θ k (n.toNat - l) j ⟨c.val % 4, by omega⟩ *
        ((-1 : ℂ) ^ l * ((b65k_poleOrder ⟨c.val / 4, by omega⟩ + l - 1).choose l : ℂ) *
          ((((b65k_fixed k : ℚ) : ℂ) -
            ((b65k_fixed (b65k_poleIndex ⟨c.val / 4, by omega⟩) : ℚ) : ℂ)) ^
              (b65k_poleOrder ⟨c.val / 4, by omega⟩ + l))⁻¹))
      (h := fun l hl ↦ (hK k (n.toNat - l) (by omega) j ⟨c.val % 4, by omega⟩).mul
        analyticAt_const)
    rw [hs, map_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro l hl
    rw [b65e_T_mul_const_coeff _ _ (hK k (n.toNat - l) (by omega) j ⟨c.val % 4, by omega⟩)]
    have h := congrFun (congrFun (hKQ k (n.toNat - l) (by omega)) j) ⟨c.val % 4, by omega⟩
    simp only [b65e_TC, Matrix.of_apply, Matrix.map_apply] at h
    rw [h, Rat.coe_castHom]
  · rw [b65q_T_const, PowerSeries.coeff_C]
    split_ifs <;> simp

/-- Order-`n` Taylor coefficients of the r-system, from the stored r-coefficient jets. -/
def b65e_rSystemJetQ (n : ℕ) : Matrix (Fin 45) (Fin 36) ℚ := fun r c ↦
  if h : r.val < 41 then
    b65q_principalEntryQ (fun k m ↦ b65e_rCoeffJetQ k (Fin.ofNat 6 m) (Fin.ofNat 8 n))
      (b65q_rRow ⟨r.val, h⟩).1 (b65q_rRow ⟨r.val, h⟩).2.1 (b65q_rRow ⟨r.val, h⟩).2.2 c
  else if n = 0 then b65q_infinityEntryQ ⟨r.val - 41, by omega⟩ c else 0

/-- The r-system along the path has the stored Taylor coefficients through order seven. -/
theorem b65e_rFamily_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∀ n < 8, b65e_TC (fun θ ↦ b65q_rFamily p O.residue θ) n = (b65e_rSystemJetQ n).map ι := by
  obtain ⟨ε, hε, -, ht, hne, hA, hP, hPi, -⟩ := b65e_family_hyps p O
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  intro n hn
  ext r c
  simp only [b65e_TC, Matrix.of_apply, Matrix.map_apply, b65q_rFamily, b65q_rSystem,
    b65e_rSystemJetQ]
  split_ifs with h hn0
  · rw [b65e_principalEntry_T p (fun θ ↦ b65q_rCoeff (b65p_poles p θ) (b65q_res O.residue θ)
        (b65q_basis O.residue θ)) _ n
      (fun k m _ i j ↦ b65q_rCoeff_an (P := fun θ k ↦ b65q_basis O.residue θ k) ht hne hA hP hPi
        k m i j 0 h0)
      (fun k m hm ↦ b65e_rCoeff_TC p O k m (by omega) n hn) _ _ _ (b65q_rRow_le _) c,
      Rat.coe_castHom]
  · rw [b65q_T_const, PowerSeries.coeff_C]
    simp only [hn0, ↓reduceIte]
    rw [b65q_infinityEntry_cast, Rat.coe_castHom]
  · rw [b65q_T_const, PowerSeries.coeff_C]
    simp [hn0]

end HodgeLean.Foundations.Program

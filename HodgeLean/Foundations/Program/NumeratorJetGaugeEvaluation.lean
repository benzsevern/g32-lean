import HodgeLean.Foundations.Program.NumeratorJetGaugePole0
import HodgeLean.Foundations.Program.NumeratorJetGaugePole1
import HodgeLean.Foundations.Program.NumeratorJetGaugePole2
import HodgeLean.Foundations.Program.NumeratorJetGaugePole3
import HodgeLean.Foundations.Program.NumeratorJetRegularEvaluation

/-! # Taylor coefficients of the gauges and Laurent coefficient series -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

local notation "ι" => Rat.castHom ℂ

/-- The analytic hypotheses of the 5d family on a good disc. -/
theorem b65e_family_hyps (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ q, AnalyticOnNhd ℂ (fun θ ↦ b65p_poles p θ q) (ball 0 ε)) ∧
      (∀ θ ∈ ball (0 : ℂ) ε, ∀ q k, q ≠ Sum.inl k →
        b65p_poles p θ q - b65p_poles p θ (Sum.inl k) ≠ 0) ∧
      (∀ q, b65q_MatAn (ball 0 ε) fun θ ↦ b65q_res O.residue θ q) ∧
      (∀ k, b65q_MatAn (ball 0 ε) fun θ ↦ b65q_basis O.residue θ k) ∧
      (∀ k, b65q_MatAn (ball 0 ε) fun θ ↦ (b65q_basis O.residue θ k)⁻¹) ∧
      (∀ x i, AnalyticOnNhd ℂ (fun θ ↦ b65q_left O.residue θ x i) (ball 0 ε)) := by
  obtain ⟨ε, hε, hεr, hgood⟩ := b65q_good_disc O
  obtain ⟨hPa, hwa, hpt⟩ := b65q_normalizations_on O hεr hgood
  have hsub : ball (0 : ℂ) ε ⊆ ball 0 O.radius := ball_subset_ball hεr
  have hP : ∀ k, b65q_MatAn (ball 0 ε) fun θ ↦ b65q_basis O.residue θ k := fun k i j ↦ hPa k i j
  refine ⟨ε, hε, hεr, b65q_poles_an p _, fun θ hθ q k hq ↦
    sub_ne_zero.mpr fun h ↦ hq (O.poles_injective θ (hsub hθ) h),
    fun q ↦ (b65q_MatAn.res O q).mono hsub, hP, fun k ↦ (hP k).inv fun θ hθ ↦
      ((isUnit_iff_isUnit_det _).mp ((hpt θ hθ).1 k).1).ne_zero, hwa⟩

/-- Casting a rational convolution. -/
theorem b65e_map_convQ {l m n : Type*} [Fintype m] (A : ℕ → Matrix l m ℚ)
    (B : ℕ → Matrix m n ℚ) (k : ℕ) :
    (b65e_convQ A B k).map ι =
      ∑ a ∈ Finset.range (k + 1), (A a).map ι * (B (k - a)).map ι :=
  b65e_map_conv A B k

/-- Taylor coefficients of a product, with both factors identified through order seven. -/
theorem b65e_TC_mul_stored {l m n : Type*} [Fintype m] {F : ℂ → Matrix l m ℂ}
    {G : ℂ → Matrix m n ℂ} (hF : ∀ i j, AnalyticAt ℂ (fun θ ↦ F θ i j) 0)
    (hG : ∀ i j, AnalyticAt ℂ (fun θ ↦ G θ i j) 0) (A : ℕ → Matrix l m ℚ)
    (B : ℕ → Matrix m n ℚ) (hA : ∀ a < 8, b65e_TC F a = (A a).map ι)
    (hB : ∀ a < 8, b65e_TC G a = (B a).map ι) :
    ∀ k < 8, b65e_TC (fun θ ↦ F θ * G θ) k = (b65e_convQ A B k).map ι := by
  intro k hk
  rw [b65e_TC_mul hF hG, b65e_map_convQ]
  apply Finset.sum_congr rfl
  intro a ha
  have := Finset.mem_range.mp ha
  rw [hA a (by omega), hB (k - a) (by omega)]

/-- The conjugated regular-part checks assembled over the poles. -/
theorem b65e_conjJet_table (k : Fin 4) (l : Fin 5) (n : Fin 8) :
    b65e_conjJetQ k l n =
      b65e_convQ (b65e_basisInvN k) (b65e_convQ (b65e_taylorN k l) (b65e_basisN k)) n := by
  fin_cases k
  · exact b65e_conjJet_table_0 l n
  · exact b65e_conjJet_table_1 l n
  · exact b65e_conjJet_table_2 l n
  · exact b65e_conjJet_table_3 l n

/-- The conjugated regular-part coefficients have the stored jets. -/
theorem b65e_conj_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k : Fin 4) (l : ℕ) (hl : l < 5) :
    ∀ n < 8, b65e_TC (fun θ ↦ (b65q_basis O.residue θ k)⁻¹ *
        b65q_taylor (b65p_poles p θ) (b65q_res O.residue θ) k l * b65q_basis O.residue θ k) n =
      (b65e_conjN k l n).map ι := by
  obtain ⟨ε, hε, -, ht, hne, hA, hP, hPi, -⟩ := b65e_family_hyps p O
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  have hG := b65q_taylor_an ht hne hA k l
  intro n hn
  have hfun : (fun θ ↦ (b65q_basis O.residue θ k)⁻¹ *
      b65q_taylor (b65p_poles p θ) (b65q_res O.residue θ) k l * b65q_basis O.residue θ k) =
      fun θ ↦ (b65q_basis O.residue θ k)⁻¹ *
        (b65q_taylor (b65p_poles p θ) (b65q_res O.residue θ) k l * b65q_basis O.residue θ k) := by
    funext θ
    rw [Matrix.mul_assoc]
  rw [hfun, b65e_TC_mul_stored (fun i j ↦ hPi k i j 0 h0)
    (fun i j ↦ (hG.mul (hP k)) i j 0 h0) (b65e_basisInvN k)
    (b65e_convQ (b65e_taylorN k l) (b65e_basisN k)) (b65e_basisInv_TC p O k)
    (b65e_TC_mul_stored (fun i j ↦ hG i j 0 h0) (fun i j ↦ hP k i j 0 h0) _ _
      (fun a ha ↦ b65e_taylor_TC p O k l hl a ha) (b65e_basis_TC p O k)) n hn]
  have hlv : ((Fin.ofNat 5 l : Fin 5) : ℕ) = l := by simp [Nat.mod_eq_of_lt hl]
  have hnv : ((Fin.ofNat 8 n : Fin 8) : ℕ) = n := by simp [Nat.mod_eq_of_lt hn]
  have h := b65e_conjJet_table k (Fin.ofNat 5 l) (Fin.ofNat 8 n)
  rw [hlv, hnv] at h
  rw [b65e_conjN, h]

/-- The gauge coefficient of the next index, written with the recursion. -/
theorem b65e_gauge_succ (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) (N : ℕ) :
    b65q_gauge t A P k (N + 1) = Matrix.of fun i j ↦
      if ((N + 1 : ℕ) : ℂ) + b65p_exponents k j - b65p_exponents k i = 0 then 0 else
        (∑ l ∈ Finset.range (N + 1),
            (P⁻¹ * b65q_taylor t A k l * P) * b65q_gauge t A P k (N - l)) i j /
          (((N + 1 : ℕ) : ℂ) + b65p_exponents k j - b65p_exponents k i) := by
  unfold b65q_gauge
  rw [b65q_gaugeUpTo, Function.update_self]
  ext i j
  simp only [Matrix.of_apply]
  split_ifs
  · rfl
  · congr 1
    rw [Finset.sum_congr rfl fun l hl ↦ by
      rw [b65q_gaugeUpTo_stable t A P k (show N - l ≤ N by have := Finset.mem_range.mp hl; omega)]]
    rfl

/-- Taylor coefficients of an entrywise quotient by constants with a zero convention. -/
theorem b65e_TC_entry_div {m n : Type*} (F : ℂ → Matrix m n ℂ) (c : m → n → ℂ)
    (hF : ∀ i j, AnalyticAt ℂ (fun θ ↦ F θ i j) 0) (k : ℕ) :
    b65e_TC (fun θ ↦ Matrix.of fun i j ↦ if c i j = 0 then 0 else F θ i j / c i j) k =
      Matrix.of fun i j ↦ if c i j = 0 then 0 else b65e_TC F k i j / c i j := by
  ext i j
  simp only [b65e_TC, Matrix.of_apply]
  split_ifs with h
  · rw [b65q_T_const, PowerSeries.coeff_C]
    split_ifs <;> rfl
  · have he : (fun θ ↦ F θ i j / c i j) = fun θ ↦ (c i j)⁻¹ * F θ i j := by
      funext θ
      rw [div_eq_inv_mul]
    rw [he, b65q_T_const_mul _ (hF i j), PowerSeries.coeff_C_mul, div_eq_inv_mul]

/-- Casting a finite sum of rational matrices. -/
theorem b65e_map_finsetSum {m n κ : Type*} (s : Finset κ) (M : κ → Matrix m n ℚ) :
    (∑ a ∈ s, M a).map ι = ∑ a ∈ s, (M a).map ι := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, map_sum]

/-- The gauge recursion checks assembled over poles and indices. -/
theorem b65e_gaugeJet_table (k : Fin 4) (m : Fin 6) (n : Fin 8) (hm : m.val ≠ 0) :
    b65e_gaugeJetQ k m n = b65e_gaugeRhsQ k m n := by
  fin_cases k <;> fin_cases m

  · exact absurd rfl hm
  · exact b65e_gaugeJet_table_0_1 n
  · exact b65e_gaugeJet_table_0_2 n
  · exact b65e_gaugeJet_table_0_3 n
  · exact b65e_gaugeJet_table_0_4 n
  · exact b65e_gaugeJet_table_0_5 n
  · exact absurd rfl hm
  · exact b65e_gaugeJet_table_1_1 n
  · exact b65e_gaugeJet_table_1_2 n
  · exact b65e_gaugeJet_table_1_3 n
  · exact b65e_gaugeJet_table_1_4 n
  · exact b65e_gaugeJet_table_1_5 n
  · exact absurd rfl hm
  · exact b65e_gaugeJet_table_2_1 n
  · exact b65e_gaugeJet_table_2_2 n
  · exact b65e_gaugeJet_table_2_3 n
  · exact b65e_gaugeJet_table_2_4 n
  · exact b65e_gaugeJet_table_2_5 n
  · exact absurd rfl hm
  · exact b65e_gaugeJet_table_3_1 n
  · exact b65e_gaugeJet_table_3_2 n
  · exact b65e_gaugeJet_table_3_3 n
  · exact b65e_gaugeJet_table_3_4 n
  · exact b65e_gaugeJet_table_3_5 n

/-- The initial gauge checks assembled over the poles. -/
theorem b65e_gaugeJet_zero (k : Fin 4) (n : Fin 8) :
    b65e_gaugeJetQ k 0 n = if n.val = 0 then 1 else 0 := by
  fin_cases k
  · exact b65e_gaugeJet_zero_0 n
  · exact b65e_gaugeJet_zero_1 n
  · exact b65e_gaugeJet_zero_2 n
  · exact b65e_gaugeJet_zero_3 n

/-- The normal-form gauge coefficients have the stored jets. -/
theorem b65e_gauge_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k : Fin 4) :
    ∀ m < 6, ∀ n < 8, b65e_TC (fun θ ↦
        b65q_gauge (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ k) k m) n =
      (b65e_gaugeN k m n).map ι := by
  obtain ⟨ε, hε, -, ht, hne, hA, hP, hPi, -⟩ := b65e_family_hyps p O
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  have hGa : ∀ m i j, AnalyticAt ℂ (fun θ ↦
      b65q_gauge (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ k) k m i j) 0 :=
    fun m i j ↦ b65q_gauge_an (P := fun θ k ↦ b65q_basis O.residue θ k) ht hne hA hP hPi k m m
      i j 0 h0
  have hCa : ∀ l i j, AnalyticAt ℂ (fun θ ↦ ((b65q_basis O.residue θ k)⁻¹ *
      b65q_taylor (b65p_poles p θ) (b65q_res O.residue θ) k l * b65q_basis O.residue θ k) i j) 0 :=
    fun l i j ↦ (((hPi k).mul (b65q_taylor_an ht hne hA k l)).mul (hP k)) i j 0 h0
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm n hn
    have hnv : ((Fin.ofNat 8 n : Fin 8) : ℕ) = n := by simp [Nat.mod_eq_of_lt hn]
    cases m with
    | zero =>
      have hf : (fun θ ↦ b65q_gauge (b65p_poles p θ) (b65q_res O.residue θ)
          (b65q_basis O.residue θ k) k 0) = fun _ ↦ (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
        funext θ
        simp [b65q_gauge, b65q_gaugeUpTo]
      rw [hf, b65e_TC_const, b65e_gaugeN, show (Fin.ofNat 6 0 : Fin 6) = 0 from rfl,
        b65e_gaugeJet_zero, hnv]
      split_ifs <;> simp
    | succ N =>
      have hfun := funext fun θ ↦ b65e_gauge_succ (b65p_poles p θ) (b65q_res O.residue θ)
        (b65q_basis O.residue θ k) k N
      rw [hfun, b65e_TC_entry_div _ _ (fun i j ↦ by
        simp only [Matrix.sum_apply]
        exact b65q_anAt_sum _ fun l _ ↦ by
          simp only [Matrix.mul_apply]
          exact b65q_anAt_sum _ fun t _ ↦ (hCa l i t).mul (hGa (N - l) t j))]
      rw [b65e_TC_finsetSum _ _ (fun l _ i j ↦ by
        simp only [Matrix.mul_apply]
        exact b65q_anAt_sum _ fun t _ ↦ (hCa l i t).mul (hGa (N - l) t j))]
      rw [Finset.sum_congr rfl fun l hl ↦ b65e_TC_mul_stored (hCa l) (hGa (N - l)) _ _
        (b65e_conj_TC p O k l (by have := Finset.mem_range.mp hl; omega))
        (fun a ha ↦ ih (N - l) (by omega) (by omega) a ha) n hn]
      have h6 : ((Fin.ofNat 6 (N + 1) : Fin 6) : ℕ) = N + 1 := by
        simp [Nat.mod_eq_of_lt hm]
      rw [b65e_gaugeN, b65e_gaugeJet_table k _ _ (by rw [h6]; omega), h6, hnv]
      ext i j
      simp only [b65e_gaugeRhsQ, Matrix.of_apply, Matrix.map_apply, b65q_exponents_cast,
        Nat.add_sub_cancel]
      rw [← b65e_map_finsetSum, Matrix.map_apply]
      have hc : (((N + 1 : ℕ) : ℂ) + ((b65q_lamQ k j : ℚ) : ℂ) - ((b65q_lamQ k i : ℚ) : ℂ)) =
          ((((N + 1 : ℕ) : ℚ) + b65q_lamQ k j - b65q_lamQ k i : ℚ) : ℂ) := by push_cast; ring
      rw [hc]
      split_ifs with h1 h2 h2
      · simp
      · exact absurd (by exact_mod_cast h1) h2
      · exact absurd (by rw [h2]; simp) h1
      · simp

/-- The inverse-series recursion checks assembled over the poles. -/
theorem b65e_gaugeInvJet_table (k : Fin 4) (m : Fin 6) (n : Fin 8) (hm : m.val ≠ 0) :
    b65e_gaugeInvJetQ k m n = b65e_gaugeInvRhsQ k m n := by
  fin_cases k
  · exact b65e_gaugeInvJet_table_0 m n hm
  · exact b65e_gaugeInvJet_table_1 m n hm
  · exact b65e_gaugeInvJet_table_2 m n hm
  · exact b65e_gaugeInvJet_table_3 m n hm

/-- The initial inverse gauge checks assembled over the poles. -/
theorem b65e_gaugeInvJet_zero (k : Fin 4) (n : Fin 8) :
    b65e_gaugeInvJetQ k 0 n = if n.val = 0 then 1 else 0 := by
  fin_cases k
  · exact b65e_gaugeInvJet_zero_0 n
  · exact b65e_gaugeInvJet_zero_1 n
  · exact b65e_gaugeInvJet_zero_2 n
  · exact b65e_gaugeInvJet_zero_3 n

/-- The inverse-series coefficient of the next index, written with the recursion. -/
theorem b65e_seriesInv_succ (H : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (N : ℕ) :
    b65q_seriesInv H (N + 1) =
      -∑ m ∈ Finset.range (N + 1), H (m + 1) * b65q_seriesInv H (N - m) := by
  unfold b65q_seriesInv
  rw [b65q_seriesInvUpTo, Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [b65q_seriesInvUpTo_stable H (show N - m ≤ N by have := Finset.mem_range.mp hm; omega)]
  rfl

/-- The inverse gauge series has the stored jets. -/
theorem b65e_gaugeInv_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k : Fin 4) :
    ∀ m < 6, ∀ n < 8, b65e_TC (fun θ ↦ b65q_seriesInv (fun m ↦
        b65q_gauge (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ k) k m) m) n =
      (b65e_gaugeInvN k m n).map ι := by
  obtain ⟨ε, hε, -, ht, hne, hA, hP, hPi, -⟩ := b65e_family_hyps p O
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  have hGa' := fun m ↦ b65q_gauge_an (P := fun θ k ↦ b65q_basis O.residue θ k) ht hne hA hP hPi k m m
  have hGa : ∀ m i j, AnalyticAt ℂ (fun θ ↦
      b65q_gauge (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ k) k m i j) 0 :=
    fun m i j ↦ hGa' m i j 0 h0
  have hIa : ∀ m i j, AnalyticAt ℂ (fun θ ↦ b65q_seriesInv (fun m ↦
      b65q_gauge (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ k) k m) m i j) 0 :=
    fun m i j ↦ b65q_seriesInv_an (H := fun θ m ↦
      b65q_gauge (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ k) k m) hGa' m m
        i j 0 h0
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm n hn
    have hnv : ((Fin.ofNat 8 n : Fin 8) : ℕ) = n := by simp [Nat.mod_eq_of_lt hn]
    cases m with
    | zero =>
      have hf : (fun θ ↦ b65q_seriesInv (fun m ↦ b65q_gauge (b65p_poles p θ)
          (b65q_res O.residue θ) (b65q_basis O.residue θ k) k m) 0) =
          fun _ ↦ (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
        funext θ
        simp [b65q_seriesInv, b65q_seriesInvUpTo]
      rw [hf, b65e_TC_const, b65e_gaugeInvN, show (Fin.ofNat 6 0 : Fin 6) = 0 from rfl,
        b65e_gaugeInvJet_zero, hnv]
      split_ifs <;> simp
    | succ N =>
      have hfun := funext fun θ ↦ b65e_seriesInv_succ (fun m ↦ b65q_gauge (b65p_poles p θ)
        (b65q_res O.residue θ) (b65q_basis O.residue θ k) k m) N
      rw [hfun, b65e_TC_neg, b65e_TC_finsetSum _ _ (fun j _ i l ↦ by
        simp only [Matrix.mul_apply]
        exact b65q_anAt_sum _ fun t _ ↦ (hGa (j + 1) i t).mul (hIa (N - j) t l))]
      rw [Finset.sum_congr rfl fun j hj ↦ b65e_TC_mul_stored (hGa (j + 1)) (hIa (N - j)) _ _
        (fun a ha ↦ b65e_gauge_TC p O k (j + 1)
          (by have := Finset.mem_range.mp hj; omega) a ha)
        (fun a ha ↦ ih (N - j) (by omega) (by omega) a ha) n hn]
      have h6 : ((Fin.ofNat 6 (N + 1) : Fin 6) : ℕ) = N + 1 := by
        simp [Nat.mod_eq_of_lt hm]
      rw [b65e_gaugeInvN, b65e_gaugeInvJet_table k _ _ (by rw [h6]; omega), h6, hnv]
      simp only [b65e_gaugeInvRhsQ, Nat.add_sub_cancel]
      rw [Matrix.map_neg _ (map_neg ι), b65e_map_finsetSum]

/-- The r-coefficient checks assembled over the poles. -/
theorem b65e_rCoeffJet_table (k : Fin 4) (m : Fin 6) (n : Fin 8) :
    b65e_rCoeffJetQ k m n = b65e_convQ (b65e_gaugeInvN k m) (b65e_basisInvN k) n := by
  fin_cases k
  · exact b65e_rCoeffJet_table_0 m n
  · exact b65e_rCoeffJet_table_1 m n
  · exact b65e_rCoeffJet_table_2 m n
  · exact b65e_rCoeffJet_table_3 m n

/-- The q-coefficient checks assembled over the poles. -/
theorem b65e_qCoeffJet_table (k : Fin 4) (m : Fin 6) (n : Fin 8) :
    b65e_qCoeffJetQ k m n = (b65e_convQ (b65e_basisN k) (b65e_gaugeN k m) n)ᵀ := by
  fin_cases k
  · exact b65e_qCoeffJet_table_0 m n
  · exact b65e_qCoeffJet_table_1 m n
  · exact b65e_qCoeffJet_table_2 m n
  · exact b65e_qCoeffJet_table_3 m n

/-- The r-coefficient series along the path have the stored jets. -/
theorem b65e_rCoeff_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k : Fin 4) (m : ℕ) (hm : m < 6) :
    ∀ n < 8, b65e_TC (fun θ ↦ b65q_rCoeff (b65p_poles p θ) (b65q_res O.residue θ)
        (b65q_basis O.residue θ) k m) n =
      (b65e_rCoeffJetQ k (Fin.ofNat 6 m) (Fin.ofNat 8 n)).map ι := by
  obtain ⟨ε, hε, -, ht, hne, hA, hP, hPi, -⟩ := b65e_family_hyps p O
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  have hGa' := fun m ↦ b65q_gauge_an (P := fun θ k ↦ b65q_basis O.residue θ k) ht hne hA hP hPi k m m
  intro n hn
  have hnv : ((Fin.ofNat 8 n : Fin 8) : ℕ) = n := by simp [Nat.mod_eq_of_lt hn]
  have h6 : ((Fin.ofNat 6 m : Fin 6) : ℕ) = m := by simp [Nat.mod_eq_of_lt hm]
  unfold b65q_rCoeff
  rw [b65e_TC_mul_stored (F := fun θ ↦ b65q_seriesInv (b65q_gauge (b65p_poles p θ)
      (b65q_res O.residue θ) (b65q_basis O.residue θ k) k) m)
    (G := fun θ ↦ (b65q_basis O.residue θ k)⁻¹) (fun i j ↦ b65q_seriesInv_an (H := fun θ m ↦
      b65q_gauge (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ k) k m) hGa' m m
        i j 0 h0) (fun i j ↦ hPi k i j 0 h0) _ _ (b65e_gaugeInv_TC p O k m hm)
    (b65e_basisInv_TC p O k) n hn, b65e_rCoeffJet_table, h6, hnv]
  rfl

/-- The q-coefficient series along the path have the stored jets. -/
theorem b65e_qCoeff_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k : Fin 4) (m : ℕ) (hm : m < 6) :
    ∀ n < 8, b65e_TC (fun θ ↦ b65q_qCoeff (b65p_poles p θ) (b65q_res O.residue θ)
        (b65q_basis O.residue θ) k m) n =
      (b65e_qCoeffJetQ k (Fin.ofNat 6 m) (Fin.ofNat 8 n)).map ι := by
  obtain ⟨ε, hε, -, ht, hne, hA, hP, hPi, -⟩ := b65e_family_hyps p O
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  have hGa' := fun m ↦ b65q_gauge_an (P := fun θ k ↦ b65q_basis O.residue θ k) ht hne hA hP hPi k m m
  intro n hn
  have hnv : ((Fin.ofNat 8 n : Fin 8) : ℕ) = n := by simp [Nat.mod_eq_of_lt hn]
  have h6 : ((Fin.ofNat 6 m : Fin 6) : ℕ) = m := by simp [Nat.mod_eq_of_lt hm]
  unfold b65q_qCoeff
  rw [b65e_TC_transpose, b65e_TC_mul_stored (F := fun θ ↦ b65q_basis O.residue θ k)
    (G := fun θ ↦ b65q_gauge (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ k) k m)
    (fun i j ↦ hP k i j 0 h0)
    (fun i j ↦ hGa' m i j 0 h0) _ _ (b65e_basis_TC p O k) (b65e_gauge_TC p O k m hm) n hn,
    b65e_qCoeffJet_table, h6, hnv]
  rfl

end HodgeLean.Foundations.Program

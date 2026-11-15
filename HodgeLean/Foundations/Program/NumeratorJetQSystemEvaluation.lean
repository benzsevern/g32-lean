import HodgeLean.Foundations.Program.NumeratorJetLeftEvaluation
import HodgeLean.Foundations.Program.NumeratorJetQBetaCertificates

/-! # Taylor coefficients of the q-system along the path -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

local notation "ι" => Rat.castHom ℂ

/-- A fibre sum of a node power times a coordinate evaluation is a power-moment contraction. -/
theorem b65e_fibre_power_trace (p : Fin 12 → ℂ) (O : b65p_Outputs p) (e : Fin 2) (v : Fin 6)
    (u : Fin 6 → ℚ) :
    ∑ x ∈ b65q_fibreSet e, p x ^ (v : ℕ) * b65e_coordinateEvalQ u (p x) =
      ∑ c : Fin 6, (u c : ℂ) * (b65e_powerMomentQ ⟨c.val + v.val, by omega⟩ e : ℂ) := by
  simp only [b65e_coordinateEvalQ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← b65e_powerMoment_sum p O ⟨c.val + v.val, by omega⟩ e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [pow_add]
  ring

/-- The beta-weight trace checks assembled over poles, fibres and orders. -/
theorem b65e_betaWeight_table (k : Fin 4) (e : Fin 2) (l : Fin 3) (v : Fin 6) (i : Fin 4)
    (n : Fin 8) : b65e_betaWeightQ k e l v i n = b65e_betaWeightFormulaQ k e l v i n := by
  fin_cases k <;> fin_cases e <;> fin_cases l
  · exact b65e_betaWeight_table_0_0_0 v i n
  · exact b65e_betaWeight_table_0_0_1 v i n
  · exact b65e_betaWeight_table_0_0_2 v i n
  · exact b65e_betaWeight_table_0_1_0 v i n
  · exact b65e_betaWeight_table_0_1_1 v i n
  · exact b65e_betaWeight_table_0_1_2 v i n
  · exact b65e_betaWeight_table_1_0_0 v i n
  · exact b65e_betaWeight_table_1_0_1 v i n
  · exact b65e_betaWeight_table_1_0_2 v i n
  · exact b65e_betaWeight_table_1_1_0 v i n
  · exact b65e_betaWeight_table_1_1_1 v i n
  · exact b65e_betaWeight_table_1_1_2 v i n
  · exact b65e_betaWeight_table_2_0_0 v i n
  · exact b65e_betaWeight_table_2_0_1 v i n
  · exact b65e_betaWeight_table_2_0_2 v i n
  · exact b65e_betaWeight_table_2_1_0 v i n
  · exact b65e_betaWeight_table_2_1_1 v i n
  · exact b65e_betaWeight_table_2_1_2 v i n
  · exact b65e_betaWeight_table_3_0_0 v i n
  · exact b65e_betaWeight_table_3_0_1 v i n
  · exact b65e_betaWeight_table_3_0_2 v i n
  · exact b65e_betaWeight_table_3_1_0 v i n
  · exact b65e_betaWeight_table_3_1_1 v i n
  · exact b65e_betaWeight_table_3_1_2 v i n

/-- Taylor coefficients of a left-eigenvector component times a negated inverse pole power. -/
theorem b65e_left_invPower_T (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k : Fin 4) (x : Fin 12)
    (i : Fin 4) (l : ℕ) (hl : l < 5) (m : ℕ) (hm : m < 8) :
    PowerSeries.coeff m (b65q_T (fun θ ↦ b65q_left O.residue θ x i *
        -((b65p_poles p θ (Sum.inr x) - b65p_poles p θ (Sum.inl k)) ^ (l + 1))⁻¹) 0) =
      ∑ b ∈ Finset.range (m + 1),
        b65e_coordinateEvalQ (b65e_leftCoordsQ (b65q_fibreIndex x) i (Fin.ofNat 8 b)) (p x) *
          -b65e_coordinateEvalQ (b65e_invPowerCoordsQ k (b65q_fibreIndex x) (Fin.ofNat 5 l)
            (Fin.ofNat 8 (m - b))) (p x) := by
  obtain ⟨ε, hε, -, -, -, -, -, -, hwa⟩ := b65e_family_hyps p O
  have hne : b65p_poles p 0 (Sum.inr x) - b65p_poles p 0 (Sum.inl k) ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ Sum.inr_ne_inl (O.poles_injective 0 (mem_ball_self O.radius_pos) h)
  have hs : AnalyticAt ℂ (fun θ ↦
      -((b65p_poles p θ (Sum.inr x) - b65p_poles p θ (Sum.inl k)) ^ (l + 1))⁻¹) 0 :=
    ((((b65q_poles_an p univ _) 0 trivial).sub ((b65q_poles_an p univ _) 0 trivial)).pow _).inv
      (pow_ne_zero _ hne) |>.neg
  rw [b65q_T_mul (hwa x i 0 (mem_ball_self hε)) hs, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro b hb
  have hb' := Finset.mem_range.mp hb
  rw [b65e_T_neg_coeff, b65e_invPower_moving_T p O k x l hl (m - b) (by omega)]
  congr 1
  exact congrFun (b65e_left_T p O x b (by omega)) i

/-- The fibre sums of the left-eigenvector and inverse-power products are the stored beta weights. -/
theorem b65e_betaWeight_sum (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k : Fin 4) (e : Fin 2)
    (l : ℕ) (hl : l < 3) (v : Fin 6) (i : Fin 4) (m : ℕ) (hm : m < 8) :
    ∑ x ∈ b65q_fibreSet e, p x ^ (v : ℕ) * ∑ b ∈ Finset.range (m + 1),
      b65e_coordinateEvalQ (b65e_leftCoordsQ e i (Fin.ofNat 8 b)) (p x) *
        -b65e_coordinateEvalQ (b65e_invPowerCoordsQ k e (Fin.ofNat 5 l) (Fin.ofNat 8 (m - b)))
          (p x) =
    (b65e_betaWeightQ k e (Fin.ofNat 3 l) v i (Fin.ofNat 8 m) : ℂ) := by
  have h3 : ((Fin.ofNat 3 l : Fin 3) : ℕ) = l := by simp [Nat.mod_eq_of_lt hl]
  have h8 : ((Fin.ofNat 8 m : Fin 8) : ℕ) = m := by simp [Nat.mod_eq_of_lt hm]
  rw [b65e_betaWeight_table, b65e_betaWeightFormulaQ, h3, h8]
  push_cast
  rw [← Finset.sum_neg_distrib]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hx : ∀ x ∈ b65q_fibreSet e, p x ^ (v : ℕ) *
      (b65e_coordinateEvalQ (b65e_leftCoordsQ e i (Fin.ofNat 8 b)) (p x) *
        -b65e_coordinateEvalQ (b65e_invPowerCoordsQ k e (Fin.ofNat 5 l) (Fin.ofNat 8 (m - b)))
          (p x)) =
      -(p x ^ (v : ℕ) * b65e_coordinateEvalQ (b65e_coordinateMulQ e
        (b65e_leftCoordsQ e i (Fin.ofNat 8 b))
        (b65e_invPowerCoordsQ k e (Fin.ofNat 5 l) (Fin.ofNat 8 (m - b)))) (p x)) := by
    intro x hx
    rw [b65e_coordinateMulQ_eval _ _ _ _ (b65q_fibre_root O e hx)]
    ring
  rw [Finset.sum_congr rfl hx, Finset.sum_neg_distrib, b65e_fibre_power_trace p O e v]

/-- The infinity beta columns along the path have the stored Taylor coefficients. -/
theorem b65e_betaInfinity_T (p : Fin 12 → ℂ) (O : b65p_Outputs p) (i : Fin 4) (e : Fin 2)
    (v : Fin 6) (n : ℕ) (hn : n < 8) :
    PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_betaInfinity p (b65q_left O.residue θ) i e v) 0) =
      (b65e_betaInfQ e v i n : ℂ) := by
  obtain ⟨ε, hε, -, -, -, -, -, -, hwa⟩ := b65e_family_hyps p O
  unfold b65q_betaInfinity
  have hs : b65q_T (fun θ ↦ ∑ x : Fin 12,
      if b65q_fibreIndex x = e then p x ^ v.val * b65q_left O.residue θ x i else 0) 0 =
      ∑ x : Fin 12, b65q_T (fun θ ↦
        if b65q_fibreIndex x = e then p x ^ v.val * b65q_left O.residue θ x i else 0) 0 := by
    apply b65q_T_sum
    intro x _
    split_ifs
    · exact analyticAt_const.mul (hwa x i 0 (mem_ball_self hε))
    · exact analyticAt_const
  rw [hs, map_sum]
  have hterm : ∀ x : Fin 12, PowerSeries.coeff n (b65q_T (fun θ ↦
      if b65q_fibreIndex x = e then p x ^ v.val * b65q_left O.residue θ x i else 0) 0) =
      if b65q_fibreIndex x = e then
        p x ^ v.val * b65e_coordinateEvalQ (b65e_leftCoordsQ e i (Fin.ofNat 8 n)) (p x) else 0 := by
    intro x
    split_ifs with hx
    · rw [b65q_T_const_mul _ (hwa x i 0 (mem_ball_self hε)), PowerSeries.coeff_C_mul,
        congrFun (b65e_left_T p O x n hn) i, hx]
    · rw [b65q_T_const, PowerSeries.coeff_C]
      split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun x _ ↦ hterm x, ← Finset.sum_filter]
  have hfs : Finset.univ.filter (fun x ↦ b65q_fibreIndex x = e) = b65q_fibreSet e := rfl
  rw [hfs, b65e_fibre_power_trace p O e v, b65e_betaInfQ]
  push_cast
  rfl

/-- Taylor coefficients commute with finite sums of analytic scalar germs. -/
theorem b65e_coeff_T_sum {κ : Type*} (s : Finset κ) (f : κ → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) (k : ℕ) :
    PowerSeries.coeff k (b65q_T (fun θ ↦ ∑ i ∈ s, f i θ) 0) =
      ∑ i ∈ s, PowerSeries.coeff k (b65q_T (f i) 0) := by
  rw [b65q_T_sum s hf, map_sum]

/-- Taylor coefficients commute with triple finite sums of analytic scalar germs. -/
theorem b65e_coeff_T_sum3 {κ₁ κ₂ κ₃ : Type*} (s₁ : Finset κ₁) (s₂ : Finset κ₂) (s₃ : Finset κ₃)
    (F : κ₁ → κ₂ → κ₃ → ℂ → ℂ) (k : ℕ)
    (hF : ∀ a ∈ s₁, ∀ b ∈ s₂, ∀ c ∈ s₃, AnalyticAt ℂ (F a b c) 0) :
    PowerSeries.coeff k (b65q_T (fun θ ↦ ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, F a b c θ) 0) =
      ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, PowerSeries.coeff k (b65q_T (F a b c) 0) := by
  rw [b65e_coeff_T_sum _ _ (fun a ha ↦ b65q_anAt_sum _ fun b hb ↦ b65q_anAt_sum _
    fun c hc ↦ hF a ha b hb c hc)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [b65e_coeff_T_sum _ _ (fun b hb ↦ b65q_anAt_sum _ fun c hc ↦ hF a ha b hb c hc)]
  apply Finset.sum_congr rfl
  intro b hb
  rw [b65e_coeff_T_sum _ _ (fun c hc ↦ hF a ha b hb c hc)]

/-- The beta entries along the path have the stored Taylor coefficients. -/
theorem b65e_betaEntry_T (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k j : Fin 4) (n : ℤ)
    (hn : n ≤ 2) (e : Fin 2) (v : Fin 6) (d : ℕ) (hd : d < 8) :
    PowerSeries.coeff d (b65q_T (fun θ ↦ b65q_betaEntry (b65p_poles p θ)
        (b65q_qCoeff (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ)) p
        (b65q_left O.residue θ) k j n e v) 0) =
      (b65e_betaJetQ k j n e v d : ℂ) := by
  obtain ⟨ε, hε, -, ht, hne, hA, hP, hPi, hwa⟩ := b65e_family_hyps p O
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  have hK : ∀ m i, AnalyticAt ℂ (fun θ ↦ b65q_qCoeff (b65p_poles p θ) (b65q_res O.residue θ)
      (b65q_basis O.residue θ) k m j i) 0 := fun m i ↦
    b65q_qCoeff_an (P := fun θ k ↦ b65q_basis O.residue θ k) ht hne hA hP hPi k m j i 0 h0
  have hS : ∀ x l, AnalyticAt ℂ (fun θ ↦
      -((b65p_poles p θ (Sum.inr x) - b65p_poles p θ (Sum.inl k)) ^ (l + 1))⁻¹) 0 := by
    intro x l
    have hne0 : b65p_poles p 0 (Sum.inr x) - b65p_poles p 0 (Sum.inl k) ≠ 0 :=
      sub_ne_zero.mpr fun h ↦ Sum.inr_ne_inl (O.poles_injective 0 (mem_ball_self O.radius_pos) h)
    exact ((((b65q_poles_an p univ _) 0 trivial).sub ((b65q_poles_an p univ _) 0 trivial)).pow
      _).inv (pow_ne_zero _ hne0) |>.neg
  unfold b65q_betaEntry b65e_betaJetQ
  split_ifs with h0n
  · have hfun : (fun θ ↦ ∑ x : Fin 12, if b65q_fibreIndex x = e then p x ^ v.val *
        ∑ l ∈ Finset.range (n.toNat + 1),
          (b65q_qCoeff (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ) k
            (n.toNat - l) *ᵥ b65q_left O.residue θ x) j *
          -((b65p_poles p θ (Sum.inr x) - b65p_poles p θ (Sum.inl k)) ^ (l + 1))⁻¹ else 0) =
        fun θ ↦ ∑ x ∈ b65q_fibreSet e, ∑ l ∈ Finset.range (n.toNat + 1), ∑ i : Fin 4,
          p x ^ v.val * (b65q_qCoeff (b65p_poles p θ) (b65q_res O.residue θ)
            (b65q_basis O.residue θ) k (n.toNat - l) j i *
          (b65q_left O.residue θ x i *
            -((b65p_poles p θ (Sum.inr x) - b65p_poles p θ (Sum.inl k)) ^ (l + 1))⁻¹)) := by
      funext θ
      rw [← Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfun, b65e_coeff_T_sum3]
    swap
    · intro x _ l _ i _
      exact analyticAt_const.mul ((hK _ i).mul ((hwa x i 0 h0).mul (hS x l)))
    have hterm : ∀ x ∈ b65q_fibreSet e, ∀ l ∈ Finset.range (n.toNat + 1), ∀ i : Fin 4,
        PowerSeries.coeff d (b65q_T (fun θ ↦ p x ^ v.val *
          (b65q_qCoeff (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ) k
            (n.toNat - l) j i * (b65q_left O.residue θ x i *
              -((b65p_poles p θ (Sum.inr x) - b65p_poles p θ (Sum.inl k)) ^ (l + 1))⁻¹))) 0) =
        p x ^ v.val * ∑ a ∈ Finset.range (d + 1),
          (b65e_qCoeffJetQ k (Fin.ofNat 6 (n.toNat - l)) (Fin.ofNat 8 a) j i : ℂ) *
          ∑ b ∈ Finset.range (d - a + 1),
            b65e_coordinateEvalQ (b65e_leftCoordsQ e i (Fin.ofNat 8 b)) (p x) *
              -b65e_coordinateEvalQ (b65e_invPowerCoordsQ k e (Fin.ofNat 5 l)
                (Fin.ofNat 8 (d - a - b))) (p x) := by
      intro x hx l hl i
      have hl' := Finset.mem_range.mp hl
      have hxe : b65q_fibreIndex x = e := (Finset.mem_filter.mp hx).2
      have hKf := hK (n.toNat - l) i
      have hgf := (hwa x i 0 h0).mul (hS x l)
      rw [b65q_T_const_mul (f := fun θ ↦ b65q_qCoeff (b65p_poles p θ) (b65q_res O.residue θ)
          (b65q_basis O.residue θ) k (n.toNat - l) j i * (b65q_left O.residue θ x i *
            -((b65p_poles p θ (Sum.inr x) - b65p_poles p θ (Sum.inl k)) ^ (l + 1))⁻¹))
          _ (hKf.mul hgf), PowerSeries.coeff_C_mul,
        b65q_T_mul (f := fun θ ↦ b65q_qCoeff (b65p_poles p θ) (b65q_res O.residue θ)
          (b65q_basis O.residue θ) k (n.toNat - l) j i)
          (g := fun θ ↦ b65q_left O.residue θ x i *
            -((b65p_poles p θ (Sum.inr x) - b65p_poles p θ (Sum.inl k)) ^ (l + 1))⁻¹) hKf hgf,
        PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_range.mp ha
      have hq := congrFun (congrFun (b65e_qCoeff_TC p O k (n.toNat - l) (by omega) a (by omega)) j) i
      simp only [b65e_TC, Matrix.of_apply, Matrix.map_apply, Rat.coe_castHom] at hq
      rw [hq, b65e_left_invPower_T p O k x i l (by omega) (d - a) (by omega), hxe]
    rw [Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun l hl ↦
      Finset.sum_congr rfl fun i _ ↦ hterm x hx l hl i]
    push_cast
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    have hl' := Finset.mem_range.mp hl
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' := Finset.mem_range.mp ha
    rw [← b65e_betaWeight_sum p O k e l (by omega) v i (d - a) (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · rw [b65q_T_const, PowerSeries.coeff_C]
    split_ifs <;> simp

/-- The beta-column checks assembled over the orders. -/
theorem b65e_qBetaJet_table (n : ℕ) (hn : n < 8) :
    b65e_qBetaJetQ (Fin.ofNat 8 n) = b65e_qBetaFormulaQ n := by
  interval_cases n
  · exact b65e_qBetaJet_table_0
  · exact b65e_qBetaJet_table_1
  · exact b65e_qBetaJet_table_2
  · exact b65e_qBetaJet_table_3
  · exact b65e_qBetaJet_table_4
  · exact b65e_qBetaJet_table_5
  · exact b65e_qBetaJet_table_6
  · exact b65e_qBetaJet_table_7

/-- The q-system along the path has the stored Taylor coefficients through order seven. -/
theorem b65e_qFamily_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∀ n < 8, b65e_TC (fun θ ↦ b65q_qFamily p O.residue θ) n = (b65e_qSystemJetQ n).map ι := by
  obtain ⟨ε, hε, -, ht, hne, hA, hP, hPi, -⟩ := b65e_family_hyps p O
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  intro n hn
  ext r c
  simp only [b65e_TC, Matrix.of_apply, Matrix.map_apply, b65q_qFamily, b65q_qSystem,
    b65e_qSystemJetQ]
  split_ifs with h hc hc' hz
  · rw [b65e_principalEntry_T p (fun θ ↦ b65q_qCoeff (b65p_poles p θ) (b65q_res O.residue θ)
        (b65q_basis O.residue θ)) _ n
      (fun k m _ i j ↦ b65q_qCoeff_an (P := fun θ k ↦ b65q_basis O.residue θ k) ht hne hA hP hPi
        k m i j 0 h0)
      (fun k m hm ↦ b65e_qCoeff_TC p O k m (by omega) n hn) _ _ _ (b65q_qRow_le _) _,
      Rat.coe_castHom]
  · rw [b65e_betaEntry_T p O _ _ _ (b65q_qRow_le _) _ _ n hn, b65e_qBetaJet_table n hn,
      Rat.coe_castHom]
    simp only [b65e_qBetaFormulaQ, h, ↓reduceDIte]
  · rw [b65q_T_const, PowerSeries.coeff_C]
    simp only [hz, ↓reduceIte]
    rw [b65q_infinityEntry_cast, Rat.coe_castHom]
  · rw [b65q_T_const, PowerSeries.coeff_C]
    simp only [hz, ↓reduceIte, map_zero]
  · rw [b65e_betaInfinity_T p O _ _ _ n hn, b65e_qBetaJet_table n hn, Rat.coe_castHom]
    simp only [b65e_qBetaFormulaQ, h, ↓reduceDIte]

end HodgeLean.Foundations.Program

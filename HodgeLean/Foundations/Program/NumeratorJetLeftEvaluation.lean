import HodgeLean.Foundations.Program.NumeratorJetLeftCertificates
import HodgeLean.Foundations.Program.NumeratorJetBetaPole0Fibre0
import HodgeLean.Foundations.Program.NumeratorJetBetaPole0Fibre1
import HodgeLean.Foundations.Program.NumeratorJetBetaPole1Fibre0
import HodgeLean.Foundations.Program.NumeratorJetBetaPole1Fibre1
import HodgeLean.Foundations.Program.NumeratorJetBetaPole2Fibre0
import HodgeLean.Foundations.Program.NumeratorJetBetaPole2Fibre1
import HodgeLean.Foundations.Program.NumeratorJetBetaPole3Fibre0
import HodgeLean.Foundations.Program.NumeratorJetBetaPole3Fibre1
import HodgeLean.Foundations.Program.NumeratorJetRSystemEvaluation
import HodgeLean.Foundations.Program.NumeratorJetMovingContractionEvaluation

/-! # Taylor coefficients of the moving left eigenvectors -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

local notation "ι" => Rat.castHom ℂ

/-- Left-eigenvector recursions at a rank-one base residue have unique normalized solutions. -/
theorem b65e_left_unique (A : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (u v : Fin 4 → ℂ) (τ : ℂ)
    (hτ : τ ≠ 0) (hA0 : A 0 = Matrix.of fun i j ↦ u i * v j) (X Y : ℕ → Fin 4 → ℂ) (N : ℕ)
    (hX : ∀ k < N, ∑ a ∈ Finset.range (k + 1), X a ᵥ* A (k - a) = τ • X k)
    (hY : ∀ k < N, ∑ a ∈ Finset.range (k + 1), Y a ᵥ* A (k - a) = τ • Y k)
    (hu : ∀ k < N, X k ⬝ᵥ u = Y k ⬝ᵥ u) :
    ∀ k < N, X k = Y k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hx := hX k hk
    have hy := hY k hk
    rw [Finset.sum_range_succ] at hx hy
    have hs : ∑ a ∈ Finset.range k, X a ᵥ* A (k - a) = ∑ a ∈ Finset.range k, Y a ᵥ* A (k - a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [ih a (Finset.mem_range.mp ha) (by have := Finset.mem_range.mp ha; omega)]
    simp only [Nat.sub_self] at hx hy
    have e1 := eq_sub_of_add_eq' hx
    have e2 := eq_sub_of_add_eq' hy
    rw [← hs] at e2
    have hD : (X k - Y k) ᵥ* A 0 = τ • (X k - Y k) := by
      rw [Matrix.sub_vecMul, e1, e2, smul_sub]
      abel
    have hDu : (X k - Y k) ⬝ᵥ u = 0 := by rw [sub_dotProduct, hu k hk, sub_self]
    have hz : τ • (X k - Y k) = 0 := by
      rw [← hD, hA0]
      ext j
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      rw [show (∑ i, (X k - Y k) i * (u i * v j)) = ((X k - Y k) ⬝ᵥ u) * v j by
        simp only [dotProduct, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring, hDu, zero_mul]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hτ)

/-- Taylor coefficients of a finite sum of products of analytic scalar germs. -/
theorem b65e_T_sum_mul_coeff {κ : Type*} (s : Finset κ) (f g : κ → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) (hg : ∀ i ∈ s, AnalyticAt ℂ (g i) 0) (k : ℕ) :
    PowerSeries.coeff k (b65q_T (fun θ ↦ ∑ i ∈ s, f i θ * g i θ) 0) =
      ∑ a ∈ Finset.range (k + 1), ∑ i ∈ s,
        PowerSeries.coeff a (b65q_T (f i) 0) * PowerSeries.coeff (k - a) (b65q_T (g i) 0) := by
  have hs : b65q_T (fun θ ↦ ∑ i ∈ s, f i θ * g i θ) 0 =
      ∑ i ∈ s, b65q_T (fun θ ↦ f i θ * g i θ) 0 :=
    b65q_T_sum s fun i hi ↦ (hf i hi).mul (hg i hi)
  rw [hs, map_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [b65q_T_mul (hf i hi) (hg i hi), PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The moving left eigenvectors have the stored Taylor coordinates through order seven. -/
theorem b65e_left_T (p : Fin 12 → ℂ) (O : b65p_Outputs p) (x : Fin 12) :
    ∀ n < 8, (fun i ↦ PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_left O.residue θ x i) 0)) =
      fun i ↦ b65e_coordinateEvalQ
        (b65e_leftCoordsQ (b65q_fibreIndex x) i (Fin.ofNat 8 n)) (p x) := by
  obtain ⟨ε, hε, hεr, hgood⟩ := b65q_good_disc O
  obtain ⟨-, hwa, hpt⟩ := b65q_normalizations_on O hεr hgood
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  have hev : ∀ᶠ θ in 𝓝 (0 : ℂ), θ ∈ ball (0 : ℂ) ε := isOpen_ball.mem_nhds h0
  have hx : x ∈ b65q_fibreSet (b65q_fibreIndex x) := by
    simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hz := b65q_fibre_root O _ hx
  set e := b65q_fibreIndex x with he
  have hW : ∀ i, AnalyticAt ℂ (fun θ ↦ b65q_left O.residue θ x i) 0 := fun i ↦ hwa x i 0 h0
  have hR : ∀ i j, AnalyticAt ℂ (fun θ ↦ b65q_res O.residue θ (Sum.inr x) i j) 0 :=
    fun i j ↦ b65q_MatAn.res O _ i j 0 (mem_ball_self O.radius_pos)
  have htr : Matrix.trace (b65q_res O.residue 0 (Sum.inr x)) = ((b65e_traceQ e : ℚ) : ℂ) := by
    rw [b65q_trace_zero_inr]
    rfl
  have hτ : ((b65e_traceQ e : ℚ) : ℂ) ≠ 0 := by
    exact_mod_cast b65q_BQ_trace_ne e
  intro n hn
  refine b65e_left_unique (fun a ↦ b65e_TC (fun θ ↦ b65q_res O.residue θ (Sum.inr x)) a)
    (b65q_u e) (fun j ↦ ((b65k_left e j : ℚ) : ℂ)) _ hτ ?_
    (fun a i ↦ PowerSeries.coeff a (b65q_T (fun θ ↦ b65q_left O.residue θ x i) 0))
    (fun a i ↦ b65e_coordinateEvalQ (b65e_leftCoordsQ e i (Fin.ofNat 8 a)) (p x))
    8 ?_ ?_ ?_ n hn
  · rw [b65e_TC_zero, b65q_res_zero_inr, b65q_uQ_cast]
    ext i j
    simp [b65q_BQ, Matrix.map_apply, he]
  · intro k hk
    ext j
    rw [Finset.sum_apply]
    show ∑ a ∈ Finset.range (k + 1), ∑ i,
        PowerSeries.coeff a (b65q_T (fun θ ↦ b65q_left O.residue θ x i) 0) *
          PowerSeries.coeff (k - a) (b65q_T (fun θ ↦ b65q_res O.residue θ (Sum.inr x) i j) 0) =
      ((b65e_traceQ e : ℚ) : ℂ) * PowerSeries.coeff k (b65q_T (fun θ ↦ b65q_left O.residue θ x j) 0)
    rw [← b65e_T_sum_mul_coeff Finset.univ (fun i θ ↦ b65q_left O.residue θ x i)
      (fun i θ ↦ b65q_res O.residue θ (Sum.inr x) i j) (fun i _ ↦ hW i) (fun i _ ↦ hR i j) k]
    have hc : (fun θ ↦ ∑ i, b65q_left O.residue θ x i * b65q_res O.residue θ (Sum.inr x) i j) =ᶠ[𝓝 0]
        fun θ ↦ ((b65e_traceQ e : ℚ) : ℂ) * b65q_left O.residue θ x j := by
      filter_upwards [hev] with θ hθ
      have h := congrFun ((hpt θ hθ).2 x).2.1 j
      simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at h
      rw [h, htr]
    rw [b65q_T_congr hc, b65q_T_const_mul _ (hW j), PowerSeries.coeff_C_mul]
  · intro k hk
    have hkv : ((Fin.ofNat 8 k : Fin 8) : ℕ) = k := by simp [Nat.mod_eq_of_lt hk]
    ext j
    simp only [Finset.sum_apply, Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul]
    show ∑ a ∈ Finset.range (k + 1), ∑ i,
        b65e_coordinateEvalQ (b65e_leftCoordsQ e i (Fin.ofNat 8 a)) (p x) *
          b65e_TC (fun θ ↦ b65q_res O.residue θ (Sum.inr x)) (k - a) i j =
      ((b65e_traceQ e : ℚ) : ℂ) * b65e_coordinateEvalQ (b65e_leftCoordsQ e j (Fin.ofNat 8 k)) (p x)
    have hE : b65e_coordinateEvalQ (fun c ↦ ∑ a ∈ Finset.range (k + 1), ∑ i : Fin 4,
        b65e_coordinateMulQ e (b65e_leftCoordsQ e i (Fin.ofNat 8 a))
          (fun s ↦ b65e_movingJet (Fin.ofNat 8 (k - a)) e s i j) c) (p x) =
        b65e_coordinateEvalQ (fun c ↦ b65e_traceQ e * b65e_leftCoordsQ e j (Fin.ofNat 8 k) c)
          (p x) := by
      congr 1
      funext c
      have h := b65e_leftJet_eig e j (Fin.ofNat 8 k) c
      simp only [b65e_leftEigLhsQ, hkv] at h
      exact h
    rw [b65e_coordinateEvalQ_finsetSum, b65e_coordinateEvalQ_scale] at hE
    rw [← hE]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' := Finset.mem_range.mp ha
    rw [b65e_coordinateEvalQ_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [b65e_coordinateMulQ_eval _ _ _ _ hz, b65e_res_TC p O _ (k - a) (by omega)]
    congr 1
    rw [← b65e_movingJet_coordinateEval p (k - a) x i j]
  · intro k hk
    have hkv : ((Fin.ofNat 8 k : Fin 8) : ℕ) = k := by simp [Nat.mod_eq_of_lt hk]
    have hl : (fun θ ↦ b65q_left O.residue θ x ⬝ᵥ b65q_u e) =ᶠ[𝓝 0]
        fun _ ↦ ((b65e_traceQ e : ℚ) : ℂ) := by
      filter_upwards [hev] with θ hθ
      rw [((hpt θ hθ).2 x).2.2, htr]
    have hL : (fun i ↦ PowerSeries.coeff k (b65q_T (fun θ ↦ b65q_left O.residue θ x i) 0)) ⬝ᵥ
        b65q_u e = PowerSeries.coeff k (b65q_T (fun θ ↦ b65q_left O.residue θ x ⬝ᵥ b65q_u e) 0) := by
      have hs : b65q_T (fun θ ↦ ∑ i, b65q_left O.residue θ x i * b65q_u e i) 0 =
          ∑ i, b65q_T (fun θ ↦ b65q_left O.residue θ x i * b65q_u e i) 0 :=
        b65q_T_sum _ fun i _ ↦ (hW i).mul analyticAt_const
      simp only [dotProduct]
      rw [hs, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [b65e_T_mul_const_coeff _ _ (hW i)]
    rw [hL, b65q_T_congr hl, b65q_T_const, PowerSeries.coeff_C]
    have hN : b65e_coordinateEvalQ (fun c ↦ ∑ i : Fin 4,
        b65e_leftCoordsQ e i (Fin.ofNat 8 k) c * b65q_uQ e i) (p x) =
        b65e_coordinateEvalQ (fun c ↦ if k = 0 ∧ c = 0 then b65e_traceQ e else 0) (p x) := by
      congr 1
      funext c
      have h := b65e_leftJet_norm e (Fin.ofNat 8 k) c
      simp only [hkv] at h
      exact h
    rw [b65e_coordinateEvalQ_sum] at hN
    simp only [dotProduct, b65q_uQ_cast]
    have hN' : ∑ i, b65e_coordinateEvalQ (b65e_leftCoordsQ e i (Fin.ofNat 8 k)) (p x) *
        ((b65q_uQ e i : ℚ) : ℂ) = if k = 0 then ((b65e_traceQ e : ℚ) : ℂ) else 0 := by
      rw [show (∑ i, b65e_coordinateEvalQ (b65e_leftCoordsQ e i (Fin.ofNat 8 k)) (p x) *
          ((b65q_uQ e i : ℚ) : ℂ)) = ∑ i, b65e_coordinateEvalQ
            (fun c ↦ b65e_leftCoordsQ e i (Fin.ofNat 8 k) c * b65q_uQ e i) (p x) by
        apply Finset.sum_congr rfl
        intro i _
        rw [show (fun c ↦ b65e_leftCoordsQ e i (Fin.ofNat 8 k) c * b65q_uQ e i) =
          fun c ↦ b65q_uQ e i * b65e_leftCoordsQ e i (Fin.ofNat 8 k) c from
            funext fun c ↦ mul_comm _ _, b65e_coordinateEvalQ_scale, mul_comm]]
      rw [hN]
      by_cases hk0 : k = 0 <;> simp [hk0, b65e_coordinateEvalQ, Fin.sum_univ_succ]
    rw [hN']

end HodgeLean.Foundations.Program

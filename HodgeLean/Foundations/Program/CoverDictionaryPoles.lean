import HodgeLean.Foundations.Program.CoverDictionaryGauge
import HodgeLean.Foundations.Program.CoverAnalyticThree

/-! # B6-5 stage 5d, stage four: the gauges of the 5c record at the poles

At a moving pole the non-resonant normal form (`b65f_local_normal_form`, with
`caf_moving_spectrum`) gives a gauge `G` with `G(t) = 1` and `G' = A G − (σ − t)⁻¹ G R`
(`b65g_moving_gauge`). At a fixed pole the analytic normal form of the record
(`b65p_Outputs.normal_form`), conjugated to the normalized eigenbasis `b65q_basis`, gives a gauge
`G = b65q_basis · H` with `H` the normal-form gauge of the hypothesis of `b65q_dictionary` and
`G' = A G − (σ − t)⁻¹ G Λ` (`b65g_fixed_gauge`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Matrix
open scoped Topology
namespace HodgeLean.Foundations.Program

local notation "𝔼" => (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)

/-- Operators are the operators of their matrices. -/
theorem caf_operator_mat (T : 𝔼) : b65r_operator (b65q_mat T) = T :=
  b65q_mat_injective (by rw [b65q_mat_operator])

/-- The matrix of a product. -/
theorem caf_mat_mul (S T : 𝔼) : b65q_mat (S * T) = b65q_mat S * b65q_mat T :=
  map_mul b65q_matAlg S T

/-- The matrix of the inverse of an operator. -/
theorem caf_mat_inverse (T : 𝔼) : b65q_mat (Ring.inverse T) = (b65q_mat T)⁻¹ := by
  by_cases hT : IsUnit T
  · obtain ⟨u, rfl⟩ := hT
    rw [Ring.inverse_unit]
    have h1 : b65q_mat ↑u * b65q_mat ↑u⁻¹ = 1 := by
      rw [← caf_mat_mul, Units.mul_inv]; exact map_one b65q_matAlg
    exact (Matrix.inv_eq_right_inv h1).symm
  · rw [Ring.inverse_non_unit _ hT]
    have hm : ¬ IsUnit (b65q_mat T) := fun h ↦ hT (by
      have := h.map (b65r_operatorEquiv 4).toAlgHom
      simpa [b65r_operatorEquiv_apply, caf_operator_mat] using this)
    rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ hm]
    exact map_zero b65q_matAlg

/-- **Splitting the coefficient at a pole.** -/
theorem caf_coefficient_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → ℂ) (A : ι → E →L[ℂ] E) (p : ι) (s : ℂ) :
    b65p_coefficient E t A s = (s - t p)⁻¹ • A p + b65p_regularPart E t A p s := by
  simp only [b65p_coefficient, b65p_regularPart]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _
    (Finset.mem_univ p)]
  simp only [ite_true, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun q hq ↦ by simp [Finset.ne_of_mem_erase hq]

/-- Off the other poles the regular part at a pole is analytic on a disc. -/
theorem caf_regularPart_ball {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → ℂ)
    (ht : Function.Injective t) (A : ι → 𝔼) (p : ι) :
    ∃ d > 0, AnalyticOnNhd ℂ (b65p_regularPart (Fin 4 → ℂ) t A p) (ball (t p) d) := by
  set S : Set ℂ := t '' {q | q ≠ p}
  have hS : IsClosed S := (Set.toFinite _).image t |>.isClosed
  have hp : t p ∉ S := by
    rintro ⟨q, hq, hqp⟩
    exact hq (ht hqp)
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hS.isOpen_compl (t p) hp
  refine ⟨d, hd, fun s hs ↦ b65p_regularPart_analyticAt _ t A p s fun q hq h ↦ ?_⟩
  exact hball hs ⟨q, hq, h.symm⟩

/-- **The gauge at a moving pole.** -/
theorem b65g_moving_gauge {p : Fin 12 → ℂ} (O : b65p_Outputs p) (θ : ℂ)
    (hθ : θ ∈ ball (0 : ℂ) O.radius) (j : Fin 12) :
    ∃ G : ℂ → 𝔼, AnalyticAt ℂ G (b65p_poles p θ (Sum.inr j)) ∧
      G (b65p_poles p θ (Sum.inr j)) = 1 ∧
      (∀ᶠ σ in 𝓝 (b65p_poles p θ (Sum.inr j)), IsUnit (G σ)) ∧
      ∀ᶠ σ in 𝓝[≠] (b65p_poles p θ (Sum.inr j)), HasDerivAt G
        (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ) σ * G σ -
          (σ - b65p_poles p θ (Sum.inr j))⁻¹ • (G σ * O.residue θ (Sum.inr j))) σ := by
  set t := b65p_poles p θ (Sum.inr j)
  set R := O.residue θ (Sum.inr j)
  set B := b65p_regularPart (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ) (Sum.inr j)
  obtain ⟨d, hd, hB⟩ := caf_regularPart_ball (b65p_poles p θ) (O.poles_injective θ hθ)
    (O.residue θ) (Sum.inr j)
  obtain ⟨q, -, hspec⟩ := caf_moving_spectrum O j
  have hnr := (hspec θ hθ).2.2
  obtain ⟨r, hr, -, H, hHa, hH1, hHu, hHd, -, -⟩ :=
    b65f_local_normal_form (Fin 4 → ℂ) R B t d hd hB hnr
  refine ⟨H, hHa t (mem_ball_self hr), hH1, ?_, ?_⟩
  · filter_upwards [ball_mem_nhds t hr] with σ hσ using hHu σ hσ
  · filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds t hr), self_mem_nhdsWithin] with σ hσ hσt
    have hne : σ - t ≠ 0 := sub_ne_zero.mpr hσt
    have hda := (hHa σ hσ).differentiableAt.hasDerivAt
    convert hda using 1
    have heq := hHd σ hσ
    have h2 : deriv H σ = (σ - t)⁻¹ • (R * H σ - H σ * R) + B σ * H σ := by
      rw [← smul_right_inj hne, smul_add, smul_smul, mul_inv_cancel₀ hne, one_smul, heq]
    rw [h2, caf_coefficient_split _ _ (Sum.inr j)]
    simp only [add_mul, smul_mul_assoc, smul_sub]
    abel


/-- The regular part at a fixed pole, in matrices. -/
theorem caf_mat_regularPart (t : Fin 4 ⊕ Fin 12 → ℂ) (R : Fin 4 ⊕ Fin 12 → 𝔼) (k : Fin 4)
    (s : ℂ) : b65q_mat (b65p_regularPart (Fin 4 → ℂ) t R (Sum.inl k) s) =
      b65q_regular t (fun q ↦ b65q_mat (R q)) k s := by
  simp only [b65p_regularPart, b65q_regular]
  rw [← b65q_matAlg_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  split_ifs
  · exact map_zero b65q_matAlg
  · rw [map_smul, b65q_matAlg_apply]

/-- Units of matrices give units of operators. -/
theorem caf_operator_isUnit {M : Matrix (Fin 4) (Fin 4) ℂ} (hM : IsUnit M) :
    IsUnit (b65r_operator M) := by
  have := hM.map (b65r_operatorEquiv 4).toAlgHom
  simpa [b65r_operatorEquiv_apply] using this

/-- Conjugating a gauge equation by an eigenbasis. -/
theorem caf_gauge_conj (R Λ Pv Pi Bv X X' Br : 𝔼) (c : ℂ) (hP : Pv * Pi = 1) (hP' : Pi * Pv = 1)
    (hRP : R * Pv = Pv * Λ) (hRB : R * Bv = Bv * Λ)
    (hX : c • X' = Λ * X - X * Λ + c • (Pi * Br * Pv * X)) :
    c • (Pv * X' * (Pi * Bv)) = R * (Pv * X * (Pi * Bv)) - Pv * X * (Pi * Bv) * Λ +
      c • (Br * (Pv * X * (Pi * Bv))) := by
  have hPiR : Pi * R = Λ * Pi := by
    calc Pi * R = Pi * R * (Pv * Pi) := by rw [hP, mul_one]
      _ = Pi * (R * Pv) * Pi := by simp only [mul_assoc]
      _ = Pi * (Pv * Λ) * Pi := by rw [hRP]
      _ = Λ * Pi := by rw [← mul_assoc Pi Pv, hP', one_mul]
  have hNΛ : Pi * Bv * Λ = Λ * (Pi * Bv) := by
    rw [mul_assoc, ← hRB, ← mul_assoc, hPiR, mul_assoc]
  calc c • (Pv * X' * (Pi * Bv)) = Pv * (c • X') * (Pi * Bv) := by
        rw [mul_smul_comm, smul_mul_assoc]
    _ = Pv * (Λ * X - X * Λ + c • (Pi * Br * Pv * X)) * (Pi * Bv) := by rw [hX]
    _ = (Pv * Λ) * X * (Pi * Bv) - Pv * X * (Λ * (Pi * Bv)) +
          c • ((Pv * Pi) * Br * Pv * X * (Pi * Bv)) := by
        simp only [mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = _ := by
        rw [← hRP, hP, ← hNΛ]
        simp only [one_mul, mul_assoc]

/-- Conjugating a gauge equation back to the eigenbasis. -/
theorem caf_gauge_conj_back (R Λ Bv Bi G G' Br : 𝔼) (c : ℂ) (hB : Bv * Bi = 1)
    (hB' : Bi * Bv = 1) (hRB : R * Bv = Bv * Λ)
    (hG : c • G' = R * G - G * Λ + c • (Br * G)) :
    c • (Bi * G') = Λ * (Bi * G) - Bi * G * Λ + c • (Bi * Br * Bv * (Bi * G)) := by
  have hBiR : Bi * R = Λ * Bi := by
    calc Bi * R = Bi * R * (Bv * Bi) := by rw [hB, mul_one]
      _ = Bi * (R * Bv) * Bi := by simp only [mul_assoc]
      _ = Bi * (Bv * Λ) * Bi := by rw [hRB]
      _ = Λ * Bi := by rw [← mul_assoc Bi Bv, hB', one_mul]
  calc c • (Bi * G') = Bi * (c • G') := by rw [mul_smul_comm]
    _ = (Bi * R) * G - Bi * G * Λ + c • (Bi * Br * G) := by
        rw [hG]; simp only [mul_add, mul_sub, mul_smul_comm, mul_assoc]
    _ = _ := by
        rw [hBiR]
        simp only [mul_assoc]
        rw [← mul_assoc Bv Bi, hB, one_mul]

/-- **The gauge at a fixed pole**, adapted to the normalized eigenbasis `b65q_basis`. -/
theorem b65g_fixed_gauge {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε, ∀ k : Fin 4,
      ∃ H : ℂ → Matrix (Fin 4) (Fin 4) ℂ,
      (∃ δ : ℝ, 0 < δ ∧
        (∀ i j : Fin 4,
          AnalyticOnNhd ℂ (fun s ↦ H s i j) (ball (b65p_fixedPole k) δ)) ∧
        H (b65p_fixedPole k) = 1 ∧
        ∀ s ∈ ball (b65p_fixedPole k) δ, ∀ i j : Fin 4,
          (s - b65p_fixedPole k) * deriv (fun s ↦ H s i j) s =
            (diagonal (b65p_exponents k) * H s - H s * diagonal (b65p_exponents k) +
              (s - b65p_fixedPole k) • ((b65q_basis O.residue θ k)⁻¹ *
                b65q_regular (b65p_poles p θ) (b65q_res O.residue θ) k s *
                  b65q_basis O.residue θ k * H s)) i j) ∧
      ∃ G : ℂ → 𝔼, (∀ s, b65q_mat (G s) = b65q_basis O.residue θ k * H s) ∧
        (∀ᶠ σ in 𝓝 (b65p_fixedPole k), IsUnit (G σ)) ∧
        ∀ᶠ σ in 𝓝[≠] (b65p_fixedPole k), HasDerivAt G
          (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ) σ * G σ -
            (σ - b65p_fixedPole k)⁻¹ • (G σ * b65p_exponent k)) σ := by
  obtain ⟨ε₀, hε₀, hε₀O, -, -, hnorm⟩ := b65q_normalizations p O
  have hexp : ∀ k, b65p_exponent k = b65r_operator (diagonal (b65p_exponents k)) := fun k ↦ rfl
  have hP₀ : ∀ k : Fin 4, IsUnit (b65r_operator (b65q_basis O.residue 0 k)) ∧
      O.residue 0 (Sum.inl k) * b65r_operator (b65q_basis O.residue 0 k) =
        b65r_operator (b65q_basis O.residue 0 k) * b65p_exponent k := by
    intro k
    obtain ⟨hu, he, -⟩ := (hnorm 0 (mem_ball_self hε₀)).1 k
    refine ⟨caf_operator_isUnit hu, b65q_mat_injective ?_⟩
    rw [caf_mat_mul, caf_mat_mul, b65q_mat_operator, hexp, b65q_mat_operator]
    exact he
  have hnf := fun k ↦ O.normal_form k _ (hP₀ k).1 (hP₀ k).2
  choose εk hεk hεkO P H hPa hP0 hPθ hHa hH1 hHeq using hnf
  set ε := min ε₀ (Finset.univ.inf' ⟨0, Finset.mem_univ _⟩ εk)
  have hε : 0 < ε := lt_min hε₀ ((Finset.lt_inf'_iff _).mpr fun k _ ↦ hεk k)
  refine ⟨ε, hε, (min_le_left _ _).trans hε₀O, fun θ hθ k ↦ ?_⟩
  have hθ0 : θ ∈ ball (0 : ℂ) ε₀ := ball_subset_ball (min_le_left _ _) hθ
  have hθk : θ ∈ ball (0 : ℂ) (εk k) := ball_subset_ball ((min_le_right _ _).trans
    (Finset.inf'_le _ (Finset.mem_univ k))) hθ
  obtain ⟨hBu, hBe, -⟩ := (hnorm θ hθ0).1 k
  obtain ⟨hPu, hPe⟩ := hPθ k θ hθk
  set t := b65p_fixedPole k
  set Λ := b65p_exponent k
  set R := O.residue θ (Sum.inl k)
  set Breg := b65p_regularPart (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ) (Sum.inl k)
  obtain ⟨Bu, hBu'⟩ := caf_operator_isUnit hBu
  obtain ⟨Pu, hPu'⟩ := hPu
  have hBe' : R * ↑Bu = ↑Bu * Λ := by
    apply b65q_mat_injective
    rw [hBu', caf_mat_mul, caf_mat_mul, b65q_mat_operator,
      show b65q_mat Λ = diagonal (b65p_exponents k) from b65q_mat_operator _]
    exact hBe
  have hPe' : R * ↑Pu = ↑Pu * Λ := by rw [hPu']; exact hPe
  set Hk : ℂ → 𝔼 := fun s ↦ H k s θ
  set N : 𝔼 := ↑Pu⁻¹ * ↑Bu
  set Gop : ℂ → 𝔼 := fun s ↦ ↑Pu * Hk s * N
  set Hop : ℂ → 𝔼 := fun s ↦ ↑Bu⁻¹ * Gop s
  -- analyticity of the gauge in `s`
  have hHk : ∀ s ∈ ball t (εk k), AnalyticAt ℂ Hk s := by
    intro s hs
    have h := hHa k (s, θ) ⟨hs, hθk⟩
    have hpr : AnalyticAt ℂ (fun s : ℂ ↦ (s, θ)) s := analyticAt_id.prod analyticAt_const
    exact h.comp_of_eq hpr rfl
  have hGd : ∀ s ∈ ball t (εk k), HasDerivAt Gop (↑Pu * deriv Hk s * N) s := fun s hs ↦
    (((hHk s hs).differentiableAt.hasDerivAt).const_mul _).mul_const _
  have hHd : ∀ s ∈ ball t (εk k), HasDerivAt Hop (↑Bu⁻¹ * (↑Pu * deriv Hk s * N)) s :=
    fun s hs ↦ (hGd s hs).const_mul _
  -- the gauge equation of the record, and its conjugates
  have hHeq' : ∀ s ∈ ball t (εk k), (s - t) • deriv Hk s =
      Λ * Hk s - Hk s * Λ + (s - t) • (↑Pu⁻¹ * Breg s * ↑Pu * Hk s) := by
    intro s hs
    have := hHeq k θ hθk s hs
    rw [← hPu', Ring.inverse_unit] at this
    exact this
  have hGeq : ∀ s ∈ ball t (εk k), (s - t) • (↑Pu * deriv Hk s * N) =
      R * Gop s - Gop s * Λ + (s - t) • (Breg s * Gop s) := fun s hs ↦
    caf_gauge_conj R Λ ↑Pu ↑Pu⁻¹ ↑Bu (Hk s) (deriv Hk s) (Breg s) (s - t) (Units.mul_inv Pu)
      (Units.inv_mul Pu) hPe' hBe' (hHeq' s hs)
  have hHeq2 : ∀ s ∈ ball t (εk k), (s - t) • (↑Bu⁻¹ * (↑Pu * deriv Hk s * N)) =
      Λ * Hop s - Hop s * Λ + (s - t) • (↑Bu⁻¹ * Breg s * ↑Bu * Hop s) := fun s hs ↦
    caf_gauge_conj_back R Λ ↑Bu ↑Bu⁻¹ (Gop s) _ (Breg s) (s - t) (Units.mul_inv Bu)
      (Units.inv_mul Bu) hBe' (hGeq s hs)
  have hBi : b65q_mat (↑Bu⁻¹ : 𝔼) = (b65q_basis O.residue θ k)⁻¹ := by
    rw [← Ring.inverse_unit, caf_mat_inverse, hBu', b65q_mat_operator]
  have hBm : b65q_mat (↑Bu : 𝔼) = b65q_basis O.residue θ k := by
    rw [hBu', b65q_mat_operator]
  have hΛm : b65q_mat Λ = diagonal (b65p_exponents k) := b65q_mat_operator _
  refine ⟨fun s ↦ b65q_mat (Hop s), ⟨εk k, hεk k, ?_, ?_, ?_⟩, Gop, ?_, ?_, ?_⟩
  · intro i j s hs
    have hc : AnalyticAt ℂ Hop s :=
      analyticAt_const.mul ((analyticAt_const.mul (hHk s hs)).mul analyticAt_const)
    have := ((b65q_entryCLM i j).analyticAt (Hop s)).comp hc
    refine this.congr (Eventually.of_forall fun s ↦ ?_)
    simp [b65q_entryCLM_apply]
  · simp only [Hop, Gop, Hk, N]
    rw [hH1 k θ hθk, mul_one, Units.mul_inv_cancel_left, Units.inv_mul]
    exact map_one b65q_matAlg
  · intro s hs i j
    have h2 : HasDerivAt (fun s ↦ b65q_entryCLM i j (Hop s))
        (b65q_entryCLM i j (↑Bu⁻¹ * (↑Pu * deriv Hk s * N))) s :=
      (b65q_entryCLM i j).hasFDerivAt.comp_hasDerivAt s (hHd s hs)
    simp only [b65q_entryCLM_apply] at h2
    rw [h2.deriv]
    have hmat : b65q_mat (Λ * Hop s - Hop s * Λ + (s - t) • (↑Bu⁻¹ * Breg s * ↑Bu * Hop s)) =
        diagonal (b65p_exponents k) * b65q_mat (Hop s) -
          b65q_mat (Hop s) * diagonal (b65p_exponents k) + (s - t) •
          ((b65q_basis O.residue θ k)⁻¹ * b65q_regular (b65p_poles p θ) (b65q_res O.residue θ) k s *
            b65q_basis O.residue θ k * b65q_mat (Hop s)) := by
      simp only [← b65q_matAlg_apply, map_add, map_sub, map_mul, map_smul]
      simp only [b65q_matAlg_apply]
      rw [hBi, hBm, caf_mat_regularPart, hΛm]
      rfl
    have hsm : (s - t) * b65q_mat (↑Bu⁻¹ * (↑Pu * deriv Hk s * N)) i j =
        b65q_mat ((s - t) • (↑Bu⁻¹ * (↑Pu * deriv Hk s * N))) i j := by
      have h3 : b65q_mat ((s - t) • (↑Bu⁻¹ * (↑Pu * deriv Hk s * N))) =
          (s - t) • b65q_mat (↑Bu⁻¹ * (↑Pu * deriv Hk s * N)) := map_smul b65q_matAlg _ _
      rw [h3, Matrix.smul_apply, smul_eq_mul]
    rw [hsm, hHeq2 s hs, hmat]
  · intro s
    have : Gop s = ↑Bu * Hop s := (Units.mul_inv_cancel_left Bu (Gop s)).symm
    rw [this, caf_mat_mul, hBm]
  · have hc : ContinuousAt Hk t := (hHk t (mem_ball_self (hεk k))).continuousAt
    have h1 : Hk t = 1 := hH1 k θ hθk
    have hU : {x : 𝔼 | IsUnit x} ∈ 𝓝 (Hk t) := by
      rw [h1]; exact Units.isOpen.mem_nhds isUnit_one
    filter_upwards [hc.preimage_mem_nhds hU] with σ hσ
    exact ((Units.isUnit Pu).mul hσ).mul ((Units.isUnit _).mul (Units.isUnit _))
  · filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds t (hεk k)), self_mem_nhdsWithin]
      with σ hσ hσt
    have hne : σ - t ≠ 0 := sub_ne_zero.mpr hσt
    convert hGd σ hσ using 1
    have h2 : ↑Pu * deriv Hk σ * N =
        (σ - t)⁻¹ • (R * Gop σ - Gop σ * Λ) + Breg σ * Gop σ := by
      rw [← smul_right_inj hne, smul_add, smul_smul, mul_inv_cancel₀ hne, one_smul,
        hGeq σ hσ]
    rw [h2, caf_coefficient_split _ _ (Sum.inl k),
      show b65p_poles p θ (Sum.inl k) = t from rfl]
    simp only [add_mul, smul_mul_assoc, smul_sub]
    abel

end HodgeLean.Foundations.Program

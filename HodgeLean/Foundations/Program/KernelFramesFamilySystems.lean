import HodgeLean.Foundations.Program.KernelFramesFamilyNormal
import HodgeLean.Foundations.Program.KernelFrames

/-! # B6-5 stage 5d, family part: analytic Laurent systems and invertible blocks

Entrywise analyticity of the Taylor coefficients, the normal-form gauge, the inverse series and
the Laurent entries along the path, on a disc where the normalized eigenbases are invertible;
the selected blocks are invertible at `θ = 0` (`b65k_r_block`, `b65k_q_block`) and hence near
`0` by continuity of the determinant.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

section
variable {s : Set ℂ} {t : ℂ → Fin 4 ⊕ Fin 12 → ℂ} {A : ℂ → Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ}
  {P : ℂ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}

theorem b65q_taylor_an (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) s)
    (hne : ∀ θ ∈ s, ∀ q k, q ≠ Sum.inl k → t θ q - t θ (Sum.inl k) ≠ 0)
    (hA : ∀ q, b65q_MatAn s fun θ ↦ A θ q) (k : Fin 4) (l : ℕ) :
    b65q_MatAn s fun θ ↦ b65q_taylor (t θ) (A θ) k l := by
  unfold b65q_taylor
  refine b65q_MatAn.sum _ fun q _ ↦ ?_
  by_cases hq : q = Sum.inl k
  · simpa [hq] using b65q_MatAn.const (s := s) (0 : Matrix (Fin 4) (Fin 4) ℂ)
  · simp only [hq, if_false]
    refine b65q_MatAn.smul ?_ (hA q)
    exact (((ht q).sub (ht _)).pow _).inv (fun θ hθ ↦ pow_ne_zero _ (hne θ hθ q k hq)) |>.neg

theorem b65q_gauge_an (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) s)
    (hne : ∀ θ ∈ s, ∀ q k, q ≠ Sum.inl k → t θ q - t θ (Sum.inl k) ≠ 0)
    (hA : ∀ q, b65q_MatAn s fun θ ↦ A θ q) (hP : ∀ k, b65q_MatAn s fun θ ↦ P θ k)
    (hPi : ∀ k, b65q_MatAn s fun θ ↦ (P θ k)⁻¹) (k : Fin 4) :
    ∀ N n, b65q_MatAn s fun θ ↦ b65q_gaugeUpTo (t θ) (A θ) (P θ k) k N n := by
  intro N
  induction N with
  | zero =>
    intro n
    simp only [b65q_gaugeUpTo]
    split_ifs
    · exact b65q_MatAn.one
    · exact b65q_MatAn.const 0
  | succ N ih =>
    intro n
    by_cases hn : n = N + 1
    · subst hn
      simp only [b65q_gaugeUpTo, Function.update_self]
      intro i j
      simp only [Matrix.of_apply]
      split_ifs with h
      · exact analyticOnNhd_const
      · refine AnalyticOnNhd.div ?_ analyticOnNhd_const fun _ _ ↦ h
        exact (b65q_MatAn.sum _ fun l _ ↦ (((hPi k).mul (b65q_taylor_an ht hne hA k l)).mul
          (hP k)).mul (ih (N - l))) i j
    · simp only [b65q_gaugeUpTo, Function.update_of_ne hn]
      exact ih n

theorem b65q_seriesInv_an {H : ℂ → ℕ → Matrix (Fin 4) (Fin 4) ℂ}
    (hH : ∀ m, b65q_MatAn s fun θ ↦ H θ m) :
    ∀ N n, b65q_MatAn s fun θ ↦ b65q_seriesInvUpTo (H θ) N n := by
  intro N
  induction N with
  | zero =>
    intro n
    simp only [b65q_seriesInvUpTo]
    split_ifs
    · exact b65q_MatAn.one
    · exact b65q_MatAn.const 0
  | succ N ih =>
    intro n
    by_cases hn : n = N + 1
    · subst hn
      simp only [b65q_seriesInvUpTo, Function.update_self]
      exact (b65q_MatAn.sum _ fun m _ ↦ (hH (m + 1)).mul (ih (N - m))).neg
    · simp only [b65q_seriesInvUpTo, Function.update_of_ne hn]
      exact ih n

variable (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) s)
    (hne : ∀ θ ∈ s, ∀ q k, q ≠ Sum.inl k → t θ q - t θ (Sum.inl k) ≠ 0)
    (hA : ∀ q, b65q_MatAn s fun θ ↦ A θ q) (hP : ∀ k, b65q_MatAn s fun θ ↦ P θ k)
    (hPi : ∀ k, b65q_MatAn s fun θ ↦ (P θ k)⁻¹)
include ht hne hA hP hPi

theorem b65q_rCoeff_an (k : Fin 4) (n : ℕ) :
    b65q_MatAn s fun θ ↦ b65q_rCoeff (t θ) (A θ) (P θ) k n :=
  (b65q_seriesInv_an (H := fun θ m ↦ b65q_gauge (t θ) (A θ) (P θ k) k m)
    (fun m ↦ b65q_gauge_an ht hne hA hP hPi k m m) n n).mul (hPi k)

theorem b65q_qCoeff_an (k : Fin 4) (n : ℕ) :
    b65q_MatAn s fun θ ↦ b65q_qCoeff (t θ) (A θ) (P θ) k n :=
  ((hP k).mul (b65q_gauge_an ht hne hA hP hPi k n n)).transpose

end

section
variable {s : Set ℂ} {t : ℂ → Fin 4 ⊕ Fin 12 → ℂ}

theorem b65q_principalEntry_an {K : ℂ → Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℂ}
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) s)
    (hne : ∀ θ ∈ s, ∀ q k, q ≠ Sum.inl k → t θ q - t θ (Sum.inl k) ≠ 0)
    (hK : ∀ k m, b65q_MatAn s fun θ ↦ K θ k m) (k j : Fin 4) (n : ℤ) (c : Fin 36) :
    AnalyticOnNhd ℂ (fun θ ↦ b65q_principalEntry (t θ) (K θ) k j n c) s := by
  unfold b65q_principalEntry
  split_ifs with h1 h2 h3
  · exact hK _ _ _ _
  · exact analyticOnNhd_const
  · refine b65q_an_sum _ fun l _ ↦ (hK _ _ _ _).mul (analyticOnNhd_const.mul ?_)
    refine (((ht _).sub (ht _)).pow _).inv fun θ hθ ↦ pow_ne_zero _ ?_
    exact hne θ hθ _ _ (fun h ↦ h1 (Sum.inl_injective h).symm)
  · exact analyticOnNhd_const

theorem b65q_betaEntry_an {K : ℂ → Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℂ} {node : Fin 12 → ℂ}
    {w : ℂ → Fin 12 → Fin 4 → ℂ}
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) s)
    (hne : ∀ θ ∈ s, ∀ q k, q ≠ Sum.inl k → t θ q - t θ (Sum.inl k) ≠ 0)
    (hK : ∀ k m, b65q_MatAn s fun θ ↦ K θ k m) (hw : ∀ x i, AnalyticOnNhd ℂ (fun θ ↦ w θ x i) s)
    (k j : Fin 4) (n : ℤ) (e : Fin 2) (v : Fin 6) :
    AnalyticOnNhd ℂ (fun θ ↦ b65q_betaEntry (t θ) (K θ) node (w θ) k j n e v) s := by
  unfold b65q_betaEntry
  split_ifs
  · refine b65q_an_sum _ fun x _ ↦ ?_
    split_ifs
    · refine analyticOnNhd_const.mul (b65q_an_sum _ fun l _ ↦ ?_)
      refine AnalyticOnNhd.mul ?_ ?_
      · simp only [Matrix.mulVec, dotProduct]
        exact b65q_an_sum _ fun i _ ↦ (hK _ _ _ _).mul (hw x i)
      · exact ((((ht _).sub (ht _)).pow _).inv fun θ hθ ↦
          pow_ne_zero _ (hne θ hθ _ _ Sum.inr_ne_inl)).neg
    · exact analyticOnNhd_const
  · exact analyticOnNhd_const

theorem b65q_betaInfinity_an {node : Fin 12 → ℂ} {w : ℂ → Fin 12 → Fin 4 → ℂ}
    (hw : ∀ x i, AnalyticOnNhd ℂ (fun θ ↦ w θ x i) s) (i : Fin 4) (e : Fin 2) (v : Fin 6) :
    AnalyticOnNhd ℂ (fun θ ↦ b65q_betaInfinity node (w θ) i e v) s := by
  unfold b65q_betaInfinity
  refine b65q_an_sum _ fun x _ ↦ ?_
  split_ifs
  · exact analyticOnNhd_const.mul (hw x i)
  · exact analyticOnNhd_const

end

theorem b65q_poles_an (p : Fin 12 → ℂ) (s : Set ℂ) (q : Fin 4 ⊕ Fin 12) :
    AnalyticOnNhd ℂ (fun θ ↦ b65p_poles p θ q) s := by
  rcases q with k | x
  · simpa [b65p_poles] using analyticOnNhd_const
  · simp only [b65p_poles, Sum.elim_inr]
    exact analyticOnNhd_const.add (analyticOnNhd_id.mul analyticOnNhd_const)

/-- **Analytic family systems** on a good disc. -/
theorem b65q_family_an {p : Fin 12 → ℂ} (O : b65p_Outputs p) {ε : ℝ} (hε : ε ≤ O.radius)
    (hgood : ∀ θ ∈ ball (0 : ℂ) ε,
      (∀ k i, (b65q_cmp O.residue θ k i).det ≠ 0) ∧ ∀ x, b65q_nrm O.residue θ x ≠ 0) :
    b65q_MatAn (ball 0 ε) (fun θ ↦ b65q_rFamily p O.residue θ) ∧
      b65q_MatAn (ball 0 ε) (fun θ ↦ b65q_qFamily p O.residue θ) := by
  obtain ⟨hPa, hwa, hpt⟩ := b65q_normalizations_on O hε hgood
  have hsub : ball (0 : ℂ) ε ⊆ ball 0 O.radius := ball_subset_ball hε
  have ht := b65q_poles_an p (ball 0 ε)
  have hne : ∀ θ ∈ ball (0 : ℂ) ε, ∀ q k, q ≠ Sum.inl k →
      b65p_poles p θ q - b65p_poles p θ (Sum.inl k) ≠ 0 := fun θ hθ q k hq ↦
    sub_ne_zero.mpr fun h ↦ hq (O.poles_injective θ (hsub hθ) h)
  have hA : ∀ q, b65q_MatAn (ball 0 ε) fun θ ↦ b65q_res O.residue θ q := fun q ↦
    (b65q_MatAn.res O q).mono hsub
  have hP : ∀ k, b65q_MatAn (ball 0 ε) fun θ ↦ b65q_basis O.residue θ k := fun k i j ↦ hPa k i j
  have hPi : ∀ k, b65q_MatAn (ball 0 ε) fun θ ↦ (b65q_basis O.residue θ k)⁻¹ := fun k ↦
    (hP k).inv fun θ hθ ↦ ((isUnit_iff_isUnit_det _).mp ((hpt θ hθ).1 k).1).ne_zero
  constructor
  · intro r c
    simp only [b65q_rFamily, b65q_rSystem]
    split_ifs
    · exact b65q_principalEntry_an ht hne (fun k m ↦ b65q_rCoeff_an ht hne hA hP hPi k m) _ _ _ _
    · exact analyticOnNhd_const
  · intro r c
    simp only [b65q_qFamily, b65q_qSystem]
    split_ifs
    · exact b65q_principalEntry_an ht hne (fun k m ↦ b65q_qCoeff_an ht hne hA hP hPi k m) _ _ _ _
    · exact b65q_betaEntry_an ht hne (fun k m ↦ b65q_qCoeff_an ht hne hA hP hPi k m)
        (fun x i ↦ hwa x i) _ _ _ _ _
    · exact analyticOnNhd_const
    · exact b65q_betaInfinity_an (fun x i ↦ hwa x i) _ _ _

/-- A good disc on which both selected blocks are invertible. -/
theorem b65q_block_disc {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ θ ∈ ball (0 : ℂ) ε,
        (∀ k i, (b65q_cmp O.residue θ k i).det ≠ 0) ∧ ∀ x, b65q_nrm O.residue θ x ≠ 0) ∧
      ∀ θ ∈ ball (0 : ℂ) ε,
        ((b65q_rFamily p O.residue θ).submatrix b65k_rRows b65k_rPivot).det ≠ 0 ∧
        ((b65q_qFamily p O.residue θ).submatrix b65k_qRows b65k_qPivot).det ≠ 0 := by
  obtain ⟨ε₀, hε₀, hε₀r, hgood⟩ := b65q_good_disc O
  obtain ⟨hr, hq⟩ := b65q_family_an O hε₀r hgood
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε₀ := mem_ball_self hε₀
  have hr0 : ((b65q_rFamily p O.residue 0).submatrix b65k_rRows b65k_rPivot).det ≠ 0 := by
    rw [b65q_rFamily_zero, Matrix.submatrix_map]
    intro h
    apply b65k_r_block
    have := RingHom.map_det (Rat.castHom ℂ) b65k_rBlock
    rw [RingHom.mapMatrix_apply] at this
    exact (map_eq_zero (Rat.castHom ℂ)).mp (this.trans h)
  have hq0 : ((b65q_qFamily p O.residue 0).submatrix b65k_qRows b65k_qPivot).det ≠ 0 := by
    rw [b65q_qFamily_zero, Matrix.submatrix_map]
    intro h
    apply b65k_q_block
    have := RingHom.map_det (Rat.castHom ℂ) b65k_qBlock
    rw [RingHom.mapMatrix_apply] at this
    exact (map_eq_zero (Rat.castHom ℂ)).mp (this.trans h)
  have hev : ∀ᶠ θ in 𝓝 (0 : ℂ),
      ((b65q_rFamily p O.residue θ).submatrix b65k_rRows b65k_rPivot).det ≠ 0 ∧
      ((b65q_qFamily p O.residue θ).submatrix b65k_qRows b65k_qPivot).det ≠ 0 :=
    ((((hr.submatrix _ _).det) 0 h0).continuousAt.eventually_ne hr0).and
      ((((hq.submatrix _ _).det) 0 h0).continuousAt.eventually_ne hq0)
  obtain ⟨ε₁, hε₁, h⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, (min_le_left _ _).trans hε₀r,
    fun θ hθ ↦ hgood θ (ball_subset_ball (min_le_left _ _) hθ),
    fun θ hθ ↦ h θ (ball_subset_ball (min_le_right _ _) hθ)⟩

end HodgeLean.Foundations.Program

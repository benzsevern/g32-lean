import HodgeLean.Foundations.Program.BraidBridgesThreeIsotopy

/-! # Finite-point motion over a square

A uniform separation bound and one time grid give a jointly continuous family of
plane bijections, with identity maps along the time-zero edge. Uniform support
control extends the family to the sphere.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

theorem rtc_pushList_continuous {n : ℕ} (R : ℝ) (l : List (Fin n)) :
    Continuous fun q : ((Fin n → ℂ) × (Fin n → ℂ)) × ℂ ↦
      b65x_pushList q.1.1 q.1.2 R l q.2 := by
  induction l with
  | nil => exact continuous_snd
  | cons j l ih =>
    exact ih.comp (continuous_fst.prodMk
      ((b65x_tent_continuous R).comp
        (((continuous_apply j).comp (continuous_fst.comp continuous_fst)).prodMk
          (((continuous_apply j).comp (continuous_snd.comp continuous_fst)).prodMk
            continuous_snd))))

theorem rtc_flow_continuous {n : ℕ} (P : unitInterval → ℝ → Fin n → ℂ)
    (hP : Continuous fun q : unitInterval × ℝ ↦ P q.1 q.2)
    (N : ℕ) (R : ℝ) (k : ℕ) :
    Continuous fun q : (unitInterval × ℝ) × ℂ ↦
      b65x_flow (P q.1.1) N R k q.1.2 q.2 := by
  induction k with
  | zero => exact continuous_snd
  | succ k ih =>
    have hc : Continuous fun q : (unitInterval × ℝ) × ℂ ↦
        P q.1.1 ((k : ℝ) / N) :=
      hP.comp ((continuous_fst.comp continuous_fst).prodMk continuous_const)
    have hd : Continuous fun q : (unitInterval × ℝ) × ℂ ↦
        P q.1.1 (b65x_clamp N k q.1.2) - P q.1.1 ((k : ℝ) / N) :=
      (hP.comp ((continuous_fst.comp continuous_fst).prodMk
        ((b65x_clamp_continuous N k).comp (continuous_snd.comp continuous_fst)))).sub hc
    exact (rtc_pushList_continuous R (List.finRange n)).comp
      ((hc.prodMk hd).prodMk ih)

theorem rtc_square_plane {n : ℕ} (Q : unitInterval × unitInterval → Fin n → ℂ)
    (hQ : Continuous Q) (hinj : ∀ q, Function.Injective (Q q)) :
    ∃ Φ : unitInterval → ℝ → ℂ → ℂ,
      Continuous (fun q : (unitInterval × ℝ) × ℂ ↦ Φ q.1.1 q.1.2 q.2) ∧
      (∀ s t, Function.Bijective (Φ s t)) ∧
      (∀ s z, Φ s 0 z = z) ∧
      (∀ s (t : unitInterval) j, Φ s t (Q (s, 0) j) = Q (s, t) j) ∧
      ∃ ρ : ℝ, ∀ s t z, ρ ≤ ‖z‖ → Φ s t z = z := by
  let P : unitInterval → ℝ → Fin n → ℂ :=
    fun s t ↦ Q (s, Set.projIcc 0 1 zero_le_one t)
  have hP : Continuous fun q : unitInterval × ℝ ↦ P q.1 q.2 :=
    hQ.comp (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd))
  -- separation along the motion
  have hpair : ∀ p : {p : Fin n × Fin n // p.1 ≠ p.2}, ∃ m > 0,
      ∀ t ∈ (Set.univ : Set (unitInterval × unitInterval)), m ≤ dist (Q t p.1.1) (Q t p.1.2) := by
    rintro ⟨⟨i, j⟩, hij⟩
    have hc : ContinuousOn (fun t ↦ dist (Q t i) (Q t j)) ((Set.univ : Set (unitInterval × unitInterval))) :=
      (((continuous_apply i).comp hQ).dist ((continuous_apply j).comp hQ)).continuousOn
    obtain ⟨t0, ht0, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc
    refine ⟨dist (Q t0 i) (Q t0 j), dist_pos.mpr fun h ↦ hij (hinj t0 h), fun t ht ↦ ?_⟩
    exact hmin ht
  choose m hm hmle using hpair
  obtain ⟨δ0, hδ0, hδ0le⟩ : ∃ δ0 > 0, ∀ p, δ0 ≤ m p := by
    by_cases he : IsEmpty {p : Fin n × Fin n // p.1 ≠ p.2}
    · exact ⟨1, one_pos, fun p ↦ he.elim p⟩
    · rw [not_isEmpty_iff] at he
      obtain ⟨p0, hp0⟩ := Finite.exists_min m
      exact ⟨m p0, hm p0, hp0⟩
  have hsep0 : ∀ t ∈ (Set.univ : Set (unitInterval × unitInterval)), ∀ i j, i ≠ j → δ0 ≤ dist (Q t i) (Q t j) :=
    fun t ht i j hij ↦ (hδ0le ⟨(i, j), hij⟩).trans (hmle ⟨(i, j), hij⟩ t ht)
  set R := δ0 / 3 with hRdef
  have hR : 0 < R := by positivity
  -- uniform continuity
  have huc := isCompact_univ.uniformContinuousOn_of_continuous (s := (Set.univ : Set (unitInterval × unitInterval))) hQ.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδP⟩ := huc R hR
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_trans (by positivity) hN
    exact_mod_cast this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hcell : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNr]
    rw [div_lt_iff₀ hδ] at hN
    linarith
  have hgrid : ∀ k ≤ N, (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNr]; exact_mod_cast hk
  have hclampI : ∀ k < N, ∀ t, b65x_clamp N k t ∈ Icc (0 : ℝ) 1 := by
    intro k hk t
    have h1 := hgrid k hk.le
    have h2 := hgrid (k + 1) hk
    push_cast at h2
    unfold b65x_clamp
    refine ⟨le_max_of_le_left h1.1, max_le h1.2 ((min_le_right _ _).trans h2.2)⟩
  have hv : ∀ s : unitInterval, ∀ k < N, ∀ t j, ‖P s (b65x_clamp N k t) j - P s ((k : ℝ) / N) j‖ < R := by
    intro s k hk t j
    have hd : dist (b65x_clamp N k t) ((k : ℝ) / N) < δ := by
      have hlo : (k : ℝ) / N ≤ b65x_clamp N k t := le_max_left _ _
      have hhi : b65x_clamp N k t ≤ ((k : ℝ) + 1) / N :=
        max_le (div_le_div_of_nonneg_right (by linarith) hNr.le) (min_le_right _ _)
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      calc b65x_clamp N k t - (k : ℝ) / N ≤ ((k : ℝ) + 1) / N - (k : ℝ) / N := by linarith
        _ = 1 / N := by ring
        _ < δ := hcell
    have hd' : dist (s, (⟨b65x_clamp N k t, hclampI k hk t⟩ : unitInterval))
        (s, (⟨(k : ℝ) / N, hgrid k hk.le⟩ : unitInterval)) < δ := by
      simpa only [Prod.dist_eq, dist_self, Subtype.dist_eq, max_eq_right dist_nonneg] using hd
    have := hδP _ (mem_univ _) _ (mem_univ _) hd'
    rw [← dist_eq_norm]
    simpa only [P, Set.projIcc_of_mem _ (hclampI k hk t),
      Set.projIcc_of_mem _ (hgrid k hk.le)] using
      lt_of_le_of_lt (dist_le_pi_dist _ _ j) this

  have hsep : ∀ s : unitInterval, ∀ k < N, ∀ i j, i ≠ j → 3 * R ≤ dist (P s ((k : ℝ) / N) i) (P s ((k : ℝ) / N) j) := by
    intro s k hk i j hij
    rw [hRdef, mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
    simpa only [P, Set.projIcc_of_mem _ (hgrid k hk.le)] using
      hsep0 (s, ⟨(k : ℝ) / N, hgrid k hk.le⟩) (mem_univ _) i j hij
  -- bound on the centres
  obtain ⟨M, hM⟩ : ∃ M, ∀ t ∈ (Set.univ : Set (unitInterval × unitInterval)), ∀ j, ‖Q t j‖ ≤ M := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hQ).isBounded.exists_norm_le
    exact ⟨C, fun t ht j ↦ (norm_le_pi_norm (Q t) j).trans (hC _ ⟨t, ht, rfl⟩)⟩
  refine ⟨fun s ↦ b65x_flow (P s) N R N, rtc_flow_continuous P hP N R N,
    fun s t ↦ b65x_flow_bijective (P s) N hR (hv s) t N le_rfl,
    fun s z ↦ ?_, fun s t j ↦ ?_, M + R, fun s t z hz ↦ ?_⟩
  · have key : ∀ k ≤ N, b65x_flow (P s) N R k 0 z = z := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        change b65x_round _ _ R (b65x_flow (P s) N R k 0 z) = z
        rw [ih (by omega), b65x_clamp_le (by positivity), sub_self, b65x_round,
          b65x_pushList_zero]
    exact key N le_rfl
  · have ht := b65x_flow_track (P s) N hNpos hR (hv s) (hsep s) t j N le_rfl
    rw [div_self hNr.ne', min_eq_left t.2.2, max_eq_right t.2.1] at ht
    have hp0 : P s 0 = Q (s, 0) := by
      dsimp [P]
      congr 2
      apply Subtype.ext
      norm_num [Set.projIcc]
    rw [hp0] at ht
    simpa only [P, Set.projIcc_val] using ht
  · apply b65x_flow_of_far (P s) N hR M _ t z hz N le_rfl
    intro k hk j
    simpa only [P, Set.projIcc_of_mem _ (hgrid k hk.le)] using
      hM (s, ⟨(k : ℝ) / N, hgrid k hk.le⟩) (mem_univ _) j

theorem rtc_square_sphere {n : ℕ} (Q : unitInterval × unitInterval → Fin n → ℂ)
    (hQ : Continuous Q) (hinj : ∀ q, Function.Injective (Q q)) :
    ∃ F : C((unitInterval × unitInterval) × OnePoint ℂ, OnePoint ℂ),
      (∀ s t, Function.Bijective (fun z ↦ F ((s, t), z))) ∧
      (∀ s z, F ((s, 0), z) = z) ∧
      (∀ s t j, F ((s, t), (Q (s, 0) j : OnePoint ℂ)) =
        (Q (s, t) j : OnePoint ℂ)) ∧
      (∀ s t, F ((s, t), OnePoint.infty) = OnePoint.infty) := by
  obtain ⟨Φ, hc, hbij, h0, htr, ρ, hfar⟩ := rtc_square_plane Q hQ hinj
  have hcp : Continuous fun q : (unitInterval × unitInterval) × ℂ ↦
      Φ q.1.1 q.1.2 q.2 :=
    hc.comp (((continuous_fst.comp continuous_fst).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).prodMk continuous_snd)
  let F : C((unitInterval × unitInterval) × OnePoint ℂ, OnePoint ℂ) :=
    ⟨fun q ↦ OnePoint.map (Φ q.1.1 q.1.2) q.2,
      b65x_lift_continuous (fun q : unitInterval × unitInterval ↦ Φ q.1 q.2)
        hcp ρ (fun q ↦ hfar q.1 q.2)⟩
  refine ⟨F, fun s t ↦ b65x_map_bijective (hbij s t), ?_,
    fun s t j ↦ ?_, fun _ _ ↦ rfl⟩
  · intro s z
    induction z using OnePoint.rec with
    | infty => rfl
    | coe z => exact congrArg ((↑) : ℂ → OnePoint ℂ) (h0 s z)
  · exact congrArg ((↑) : ℂ → OnePoint ℂ) (htr s t j)

end HodgeLean.Foundations.Program

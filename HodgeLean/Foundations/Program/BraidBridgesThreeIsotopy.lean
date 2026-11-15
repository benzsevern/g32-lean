import HodgeLean.Foundations.Program.MarkedRootCoverDefs

/-! # Isotopy extension for finitely many moving points in the plane

A continuous motion of finitely many distinct points of `ℂ` over `[0, 1]` extends to a continuous
family of bijections of the plane, the identity at time zero, carrying the initial points to the
moving ones and fixing the exterior of a large disc. Each step is a composition of radial tent
pushes, one per point, over a fine partition of the time interval.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric

namespace HodgeLean.Foundations.Program

/-- The radial tent push of radius `R` about `c` by the displacement `v`. -/
def b65x_tent (c v : ℂ) (R : ℝ) (z : ℂ) : ℂ := z + (max 0 (1 - dist z c / R)) • v

theorem b65x_tent_continuous (R : ℝ) :
    Continuous fun q : ℂ × ℂ × ℂ ↦ b65x_tent q.1 q.2.1 R q.2.2 := by
  unfold b65x_tent
  fun_prop

theorem b65x_tent_of_le {c v z : ℂ} {R : ℝ} (hR : 0 < R) (h : R ≤ dist z c) :
    b65x_tent c v R z = z := by
  have hs : 1 - dist z c / R ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hR]; linarith
  simp [b65x_tent, max_eq_left hs]

theorem b65x_tent_centre (c v : ℂ) (R : ℝ) : b65x_tent c v R c = c + v := by
  simp [b65x_tent]

theorem b65x_tent_zero (c z : ℂ) (R : ℝ) : b65x_tent c 0 R z = z := by
  simp [b65x_tent]

/-- A contracting perturbation of the identity of `ℂ` is bijective. -/
theorem b65x_add_contracting_bijective {g : ℂ → ℂ} {K : NNReal} (hg : ContractingWith K g) :
    Function.Bijective fun z ↦ z + g z := by
  constructor
  · intro x y hxy
    have hdist : dist x y = dist (g x) (g y) := by
      simp only [dist_eq_norm]
      rw [show x - y = -(g x - g y) by simp only at hxy; linear_combination hxy, norm_neg]
    have hle := hg.dist_le_mul x y
    rw [← hdist] at hle
    by_contra hne
    have hd : 0 < dist x y := dist_pos.mpr hne
    have hK : (K : ℝ) < 1 := hg.1
    nlinarith
  · intro y
    let q : ℂ → ℂ := fun z ↦ y - g z
    have hq : ContractingWith K q := by
      refine ⟨hg.1, LipschitzWith.of_dist_le_mul fun x z ↦ ?_⟩
      calc
        dist (q x) (q z) = dist (g x) (g z) := by
          simp only [dist_eq_norm]
          rw [show q x - q z = -(g x - g z) by simp [q], norm_neg]
        _ ≤ (K : ℝ) * dist x z := hg.dist_le_mul x z
    have hx : q (hq.fixedPoint q) = hq.fixedPoint q := hq.fixedPoint_isFixedPt
    refine ⟨hq.fixedPoint q, ?_⟩
    simp only [q] at hx
    exact eq_of_sub_eq_zero (by linear_combination -hx)

/-- The tent push is bijective when the displacement is shorter than the radius. -/
theorem b65x_tent_bijective {c v : ℂ} {R : ℝ} (hR : 0 < R) (hv : ‖v‖ < R) :
    Function.Bijective (b65x_tent c v R) := by
  let K : NNReal := ⟨‖v‖ / R, div_nonneg (norm_nonneg _) hR.le⟩
  have hK : ContractingWith K (fun z ↦ (max 0 (1 - dist z c / R)) • v) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
    · change ‖v‖ / R < 1
      rw [div_lt_one hR]; exact hv
    · let ax : ℝ := max 0 (1 - dist x c / R)
      let ay : ℝ := max 0 (1 - dist y c / R)
      have hmax : |ax - ay| ≤ |(1 - dist x c / R) - (1 - dist y c / R)| :=
        (abs_max_sub_max_le_max 0 _ 0 _).trans (by simp)
      have hdist : |dist y c - dist x c| ≤ dist x y := by
        simpa [dist_comm] using abs_dist_sub_le y x c
      have hscalar : |ax - ay| ≤ dist x y / R := by
        calc
          |ax - ay| ≤ |(1 - dist x c / R) - (1 - dist y c / R)| := hmax
          _ = |dist y c - dist x c| / R := by
            rw [show (1 - dist x c / R) - (1 - dist y c / R) = (dist y c - dist x c) / R by ring,
              abs_div, abs_of_pos hR]
          _ ≤ dist x y / R := (div_le_div_iff_of_pos_right hR).2 hdist
      change dist (ax • v) (ay • v) ≤ (‖v‖ / R) * dist x y
      rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
      calc
        |ax - ay| * ‖v‖ ≤ (dist x y / R) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hscalar (norm_nonneg _)
        _ = (‖v‖ / R) * dist x y := by ring
  exact b65x_add_contracting_bijective hK

/-- One push per index of a list, applied in list order. -/
def b65x_pushList {n : ℕ} (c v : Fin n → ℂ) (R : ℝ) : List (Fin n) → ℂ → ℂ
  | [] => id
  | j :: l => fun z ↦ b65x_pushList c v R l (b65x_tent (c j) (v j) R z)

theorem b65x_pushList_continuous {n : ℕ} (c : Fin n → ℂ) (R : ℝ) (l : List (Fin n)) :
    Continuous fun q : (Fin n → ℂ) × ℂ ↦ b65x_pushList c q.1 R l q.2 := by
  induction l with
  | nil => exact continuous_snd
  | cons j l ih =>
    change Continuous fun q : (Fin n → ℂ) × ℂ ↦
      b65x_pushList c q.1 R l (b65x_tent (c j) (q.1 j) R q.2)
    have h1 : Continuous fun q : (Fin n → ℂ) × ℂ ↦ b65x_tent (c j) (q.1 j) R q.2 := by
      unfold b65x_tent; fun_prop
    exact ih.comp (continuous_fst.prodMk h1)

theorem b65x_pushList_bijective {n : ℕ} (c v : Fin n → ℂ) {R : ℝ} (hR : 0 < R)
    (hv : ∀ j, ‖v j‖ < R) (l : List (Fin n)) :
    Function.Bijective (b65x_pushList c v R l) := by
  induction l with
  | nil => exact Function.bijective_id
  | cons j l ih => exact ih.comp (b65x_tent_bijective hR (hv j))

theorem b65x_pushList_of_far {n : ℕ} (c v : Fin n → ℂ) {R : ℝ} (hR : 0 < R)
    (l : List (Fin n)) {z : ℂ} (hz : ∀ j ∈ l, R ≤ dist z (c j)) :
    b65x_pushList c v R l z = z := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    change b65x_pushList c v R l (b65x_tent (c j) (v j) R z) = z
    rw [b65x_tent_of_le hR (hz j (by simp))]
    exact ih fun k hk ↦ hz k (by simp [hk])

theorem b65x_pushList_zero {n : ℕ} (c : Fin n → ℂ) (R : ℝ) (l : List (Fin n)) (z : ℂ) :
    b65x_pushList c 0 R l z = z := by
  induction l generalizing z with
  | nil => rfl
  | cons j l ih =>
    change b65x_pushList c 0 R l (b65x_tent (c j) 0 R z) = z
    rw [b65x_tent_zero, ih]

/-- Point tracking for one round of pushes with well separated centres. -/
theorem b65x_pushList_centre {n : ℕ} (c v : Fin n → ℂ) {R : ℝ} (hR : 0 < R)
    (hv : ∀ j, ‖v j‖ < R) (hsep : ∀ i j, i ≠ j → 3 * R ≤ dist (c i) (c j))
    (l : List (Fin n)) (hl : l.Nodup) (i : Fin n) :
    b65x_pushList c v R l (c i) = c i + if i ∈ l then v i else 0 := by
  induction l with
  | nil => simp [b65x_pushList]
  | cons j l ih =>
    change b65x_pushList c v R l (b65x_tent (c j) (v j) R (c i)) = _
    have hjl : j ∉ l := (List.nodup_cons.mp hl).1
    by_cases hij : i = j
    · subst hij
      rw [b65x_tent_centre, b65x_pushList_of_far c v hR l]
      · simp
      · intro k hk
        have hki : i ≠ k := fun h ↦ hjl (h ▸ hk)
        have h1 := hsep i k hki
        have h2 : dist (c i + v i) (c i) = ‖v i‖ := by simp [dist_eq_norm]
        have h3 := dist_triangle (c i) (c i + v i) (c k)
        rw [dist_comm (c i) (c i + v i), h2] at h3
        linarith [hv i]
    · rw [b65x_tent_of_le hR (by linarith [hsep i j hij, hR]), ih (List.nodup_cons.mp hl).2]
      simp [hij]

/-- One round of pushes, over all indices. -/
def b65x_round {n : ℕ} (c v : Fin n → ℂ) (R : ℝ) : ℂ → ℂ :=
  b65x_pushList c v R (List.finRange n)

theorem b65x_round_centre {n : ℕ} (c v : Fin n → ℂ) {R : ℝ} (hR : 0 < R)
    (hv : ∀ j, ‖v j‖ < R) (hsep : ∀ i j, i ≠ j → 3 * R ≤ dist (c i) (c j)) (i : Fin n) :
    b65x_round c v R (c i) = c i + v i := by
  rw [b65x_round, b65x_pushList_centre c v hR hv hsep _ (List.nodup_finRange n)]
  simp

/-- The clamp of `t` to the `k`-th cell `[k/N, (k+1)/N]`. -/
def b65x_clamp (N k : ℕ) (t : ℝ) : ℝ := max ((k : ℝ) / N) (min t (((k : ℝ) + 1) / N))

theorem b65x_clamp_continuous (N k : ℕ) : Continuous (b65x_clamp N k) := by
  unfold b65x_clamp; fun_prop

/-- The flow after `k` cells. -/
def b65x_flow {n : ℕ} (P : ℝ → Fin n → ℂ) (N : ℕ) (R : ℝ) : ℕ → ℝ → ℂ → ℂ
  | 0 => fun _ z ↦ z
  | k + 1 => fun t z ↦ b65x_round (P ((k : ℝ) / N))
      (P (b65x_clamp N k t) - P ((k : ℝ) / N)) R (b65x_flow P N R k t z)

theorem b65x_flow_continuous {n : ℕ} (P : ℝ → Fin n → ℂ) (hP : Continuous P) (N : ℕ)
    (R : ℝ) (k : ℕ) : Continuous fun q : ℝ × ℂ ↦ b65x_flow P N R k q.1 q.2 := by
  induction k with
  | zero => exact continuous_snd
  | succ k ih =>
    change Continuous fun q : ℝ × ℂ ↦ b65x_pushList (P ((k : ℝ) / N))
      (P (b65x_clamp N k q.1) - P ((k : ℝ) / N)) R (List.finRange n)
        (b65x_flow P N R k q.1 q.2)
    refine (b65x_pushList_continuous _ R _).comp (Continuous.prodMk ?_ ih)
    exact ((hP.comp ((b65x_clamp_continuous N k).comp continuous_fst)).sub continuous_const)

theorem b65x_flow_bijective {n : ℕ} (P : ℝ → Fin n → ℂ) (N : ℕ) {R : ℝ} (hR : 0 < R)
    (hv : ∀ k < N, ∀ t j, ‖P (b65x_clamp N k t) j - P ((k : ℝ) / N) j‖ < R) (t : ℝ) :
    ∀ k ≤ N, Function.Bijective (b65x_flow P N R k t) := by
  intro k
  induction k with
  | zero => intro _; exact Function.bijective_id
  | succ k ih =>
    intro hk
    exact (b65x_pushList_bijective _ _ hR (fun j ↦ hv k (by omega) t j) _).comp (ih (by omega))

theorem b65x_flow_of_far {n : ℕ} (P : ℝ → Fin n → ℂ) (N : ℕ) {R : ℝ} (hR : 0 < R)
    (M : ℝ) (hM : ∀ k < N, ∀ j, ‖P ((k : ℝ) / N) j‖ ≤ M) (t : ℝ) (z : ℂ) (hz : M + R ≤ ‖z‖) :
    ∀ k ≤ N, b65x_flow P N R k t z = z := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    change b65x_round _ _ R (b65x_flow P N R k t z) = z
    rw [ih (by omega)]
    apply b65x_pushList_of_far _ _ hR
    intro j _
    have h1 := hM k (by omega) j
    rw [dist_eq_norm]
    have h2 := norm_sub_norm_le z (P ((k : ℝ) / N) j)
    linarith

theorem b65x_clamp_le {N k : ℕ} {t : ℝ} (h : t ≤ (k : ℝ) / N) :
    b65x_clamp N k t = (k : ℝ) / N := by
  unfold b65x_clamp
  apply max_eq_left
  exact (min_le_left _ _).trans h

theorem b65x_flow_track {n : ℕ} (P : ℝ → Fin n → ℂ) (N : ℕ) (hN : 0 < N) {R : ℝ}
    (hR : 0 < R)
    (hv : ∀ k < N, ∀ t j, ‖P (b65x_clamp N k t) j - P ((k : ℝ) / N) j‖ < R)
    (hsep : ∀ k < N, ∀ i j, i ≠ j → 3 * R ≤ dist (P ((k : ℝ) / N) i) (P ((k : ℝ) / N) j))
    (t : ℝ) (i : Fin n) :
    ∀ k ≤ N, b65x_flow P N R k t (P 0 i) = P (max 0 (min t ((k : ℝ) / N))) i := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  intro k
  induction k with
  | zero =>
    intro _
    simp only [b65x_flow, CharP.cast_eq_zero, zero_div]
    congr 2
    rw [eq_comm, max_eq_left (min_le_right _ _)]
  | succ k ih =>
    intro hk
    change b65x_round _ _ R (b65x_flow P N R k t (P 0 i)) = _
    rw [ih (by omega)]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) / N := by positivity
    have hkk : (k : ℝ) / N ≤ ((k : ℝ) + 1) / N := by
      apply div_le_div_of_nonneg_right _ hNpos.le; linarith
    push_cast
    by_cases ht : t ≤ (k : ℝ) / N
    · rw [b65x_clamp_le ht, sub_self, b65x_round, b65x_pushList_zero,
        min_eq_left ht, min_eq_left (ht.trans hkk)]
    · push Not at ht
      rw [min_eq_right ht.le, max_eq_right hk0]
      rw [b65x_round_centre (P ((k : ℝ) / N)) (P (b65x_clamp N k t) - P ((k : ℝ) / N)) hR
        (fun j ↦ hv k (by omega) t j) (hsep k (by omega))]
      simp only [Pi.sub_apply, add_sub_cancel]
      congr 2
      unfold b65x_clamp
      rw [max_eq_right (le_min ht.le hkk), max_eq_right]
      exact le_min (hk0.trans ht.le) (hk0.trans hkk)

/-- Isotopy extension for finitely many points moving continuously without collision. -/
theorem b65x_isotopy {n : ℕ} (P : ℝ → Fin n → ℂ) (hP : Continuous P)
    (hinj : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective (P t)) :
    ∃ Φ : ℝ → ℂ → ℂ, Continuous (fun q : ℝ × ℂ ↦ Φ q.1 q.2) ∧
      (∀ t, Function.Bijective (Φ t)) ∧ (∀ z, Φ 0 z = z) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ j, Φ t (P 0 j) = P t j) ∧
      ∃ ρ : ℝ, ∀ t z, ρ ≤ ‖z‖ → Φ t z = z := by
  -- separation along the motion
  have hpair : ∀ p : {p : Fin n × Fin n // p.1 ≠ p.2}, ∃ m > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, m ≤ dist (P t p.1.1) (P t p.1.2) := by
    rintro ⟨⟨i, j⟩, hij⟩
    have hc : ContinuousOn (fun t ↦ dist (P t i) (P t j)) (Icc 0 1) :=
      (((continuous_apply i).comp hP).dist ((continuous_apply j).comp hP)).continuousOn
    obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hc
    refine ⟨dist (P t0 i) (P t0 j), dist_pos.mpr fun h ↦ hij (hinj t0 ht0 h), fun t ht ↦ ?_⟩
    exact hmin ht
  choose m hm hmle using hpair
  obtain ⟨δ0, hδ0, hδ0le⟩ : ∃ δ0 > 0, ∀ p, δ0 ≤ m p := by
    by_cases he : IsEmpty {p : Fin n × Fin n // p.1 ≠ p.2}
    · exact ⟨1, one_pos, fun p ↦ he.elim p⟩
    · rw [not_isEmpty_iff] at he
      obtain ⟨p0, hp0⟩ := Finite.exists_min m
      exact ⟨m p0, hm p0, hp0⟩
  have hsep0 : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j, i ≠ j → δ0 ≤ dist (P t i) (P t j) :=
    fun t ht i j hij ↦ (hδ0le ⟨(i, j), hij⟩).trans (hmle ⟨(i, j), hij⟩ t ht)
  set R := δ0 / 3 with hRdef
  have hR : 0 < R := by positivity
  -- uniform continuity
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous (s := Icc (0 : ℝ) 1) hP.continuousOn
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
  have hv : ∀ k < N, ∀ t j, ‖P (b65x_clamp N k t) j - P ((k : ℝ) / N) j‖ < R := by
    intro k hk t j
    have hd : dist (b65x_clamp N k t) ((k : ℝ) / N) < δ := by
      have hlo : (k : ℝ) / N ≤ b65x_clamp N k t := le_max_left _ _
      have hhi : b65x_clamp N k t ≤ ((k : ℝ) + 1) / N :=
        max_le (div_le_div_of_nonneg_right (by linarith) hNr.le) (min_le_right _ _)
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      calc b65x_clamp N k t - (k : ℝ) / N ≤ ((k : ℝ) + 1) / N - (k : ℝ) / N := by linarith
        _ = 1 / N := by ring
        _ < δ := hcell
    have := hδP _ (hclampI k hk t) _ (hgrid k hk.le) hd
    rw [← dist_eq_norm]
    exact lt_of_le_of_lt (dist_le_pi_dist _ _ j) this
  have hsep : ∀ k < N, ∀ i j, i ≠ j → 3 * R ≤ dist (P ((k : ℝ) / N) i) (P ((k : ℝ) / N) j) := by
    intro k hk i j hij
    rw [hRdef, mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
    exact hsep0 _ (hgrid k hk.le) i j hij
  -- bound on the centres
  obtain ⟨M, hM⟩ : ∃ M, ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, ‖P t j‖ ≤ M := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.image hP).isBounded.exists_norm_le
    exact ⟨C, fun t ht j ↦ (norm_le_pi_norm (P t) j).trans (hC _ ⟨t, ht, rfl⟩)⟩
  refine ⟨b65x_flow P N R N, b65x_flow_continuous P hP N R N,
    fun t ↦ b65x_flow_bijective P N hR hv t N le_rfl, fun z ↦ ?_, fun t ht j ↦ ?_,
    M + R, fun t z hz ↦ b65x_flow_of_far P N hR M (fun k hk j ↦ hM _ (hgrid k hk.le) j) t z hz
      N le_rfl⟩
  · -- time zero
    have key : ∀ k ≤ N, b65x_flow P N R k 0 z = z := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        change b65x_round _ _ R (b65x_flow P N R k 0 z) = z
        rw [ih (by omega), b65x_clamp_le (by positivity), sub_self, b65x_round,
          b65x_pushList_zero]
    exact key N le_rfl
  · rw [b65x_flow_track P N hNpos hR hv hsep t j N le_rfl, div_self hNr.ne',
      min_eq_left ht.2, max_eq_right ht.1]

/-- A continuous family of plane maps that is the identity far out extends continuously to
the sphere. -/
theorem b65x_lift_continuous {T : Type*} [TopologicalSpace T] (Φ : T → ℂ → ℂ)
    (hΦ : Continuous fun q : T × ℂ ↦ Φ q.1 q.2) (ρ : ℝ) (hfar : ∀ t z, ρ ≤ ‖z‖ → Φ t z = z) :
    Continuous fun q : T × OnePoint ℂ ↦ OnePoint.map (Φ q.1) q.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, w⟩
  induction w using OnePoint.rec with
  | infty =>
    have hV : IsOpen (((↑) : ℂ → OnePoint ℂ) '' closedBall 0 ρ)ᶜ :=
      OnePoint.isOpen_compl_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall 0 ρ⟩
    have hmem : (OnePoint.infty : OnePoint ℂ) ∈ (((↑) : ℂ → OnePoint ℂ) '' closedBall 0 ρ)ᶜ :=
      fun ⟨z, _, h⟩ ↦ OnePoint.coe_ne_infty z h
    apply continuousAt_snd.congr
    filter_upwards [(isOpen_univ.prod hV).mem_nhds ⟨mem_univ t, hmem⟩] with q hq
    obtain ⟨-, hq2⟩ := hq
    induction h : q.2 using OnePoint.rec with
    | infty => simp
    | coe z =>
      rw [h] at hq2
      have hz : ρ ≤ ‖z‖ := by
        by_contra hlt
        exact hq2 ⟨z, by simpa using (not_le.mp hlt).le, rfl⟩
      simp [hfar q.1 z hz]
  | coe z =>
    have he : Topology.IsOpenEmbedding (Prod.map id ((↑) : ℂ → OnePoint ℂ) : T × ℂ → _) :=
      Topology.IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe
    change ContinuousAt _ (Prod.map id ((↑) : ℂ → OnePoint ℂ) (t, z))
    rw [← he.continuousAt_iff]
    exact (OnePoint.continuous_coe.comp hΦ).continuousAt

theorem b65x_map_bijective {f : ℂ → ℂ} (hf : Function.Bijective f) :
    Function.Bijective (OnePoint.map f) := by
  constructor
  · intro a b h
    induction a using OnePoint.rec <;> induction b using OnePoint.rec
    · rfl
    · exact absurd h.symm (OnePoint.coe_ne_infty _)
    · exact absurd h (OnePoint.coe_ne_infty _)
    · simp only [OnePoint.map_some, OnePoint.coe_eq_coe] at h
      rw [hf.1 h]
  · intro b
    induction b using OnePoint.rec with
    | infty => exact ⟨OnePoint.infty, rfl⟩
    | coe z =>
      obtain ⟨y, rfl⟩ := hf.2 z
      exact ⟨y, rfl⟩

/-- The isotopy extension as a fibre-preserving homeomorphism of `[0, 1] × Ĉ`. -/
theorem b65x_isotopy_sphere {n : ℕ} (P : ℝ → Fin n → ℂ) (hP : Continuous P)
    (hinj : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective (P t)) :
    ∃ Φ : ℝ → ℂ → ℂ, ∃ E : unitInterval × OnePoint ℂ ≃ₜ unitInterval × OnePoint ℂ,
      (∀ t w, E (t, w) = (t, OnePoint.map (Φ t) w)) ∧
      (∀ t, Function.Bijective (Φ t)) ∧ (∀ z, Φ 0 z = z) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, Φ t (P 0 j) = P t j := by
  obtain ⟨Φ, hc, hbij, h0, htr, ρ, hfar⟩ := b65x_isotopy P hP hinj
  let F : unitInterval × OnePoint ℂ → unitInterval × OnePoint ℂ :=
    fun q ↦ (q.1, OnePoint.map (Φ q.1) q.2)
  have hFc : Continuous F := by
    refine continuous_fst.prodMk ?_
    have := b65x_lift_continuous (fun t : unitInterval ↦ Φ t)
      (hc.comp (continuous_subtype_val.prodMap continuous_id)) ρ (fun t z hz ↦ hfar t z hz)
    exact this
  have hFb : Function.Bijective F := by
    constructor
    · rintro ⟨t, a⟩ ⟨t', b⟩ h
      simp only [F, Prod.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      rw [(b65x_map_bijective (hbij t)).1 h2]
    · rintro ⟨t, b⟩
      obtain ⟨a, ha⟩ := (b65x_map_bijective (hbij t)).2 b
      exact ⟨(t, a), by simp [F, ha]⟩
  exact ⟨Φ, hFc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hFb), fun t w ↦ rfl,
    hbij, h0, htr⟩

/-- Transport along the isotopy: a based family of loops that avoids infinity and a subfamily of
the moving points ends, up to based homotopy in the complement of the final points, at the
image of its initial loop under the end map of the isotopy. -/
theorem b65x_family_end {n : ℕ} (P : ℝ → Fin n → ℂ) (Φ : ℝ → ℂ → ℂ)
    (E : unitInterval × OnePoint ℂ ≃ₜ unitInterval × OnePoint ℂ)
    (hE : ∀ t w, E (t, w) = (t, OnePoint.map (Φ t) w))
    (hbij : ∀ t, Function.Bijective (Φ t)) (h0 : ∀ z, Φ 0 z = z)
    (htr : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, Φ t (P 0 j) = P t j)
    (S : Set (Fin n)) (b : Fin n) (hb : ∀ t ∈ Icc (0 : ℝ) 1, P t b = P 0 b)
    (K : C(unitInterval × unitInterval, OnePoint ℂ))
    (hKb : ∀ t, K (t, 0) = (P 0 b : OnePoint ℂ) ∧ K (t, 1) = (P 0 b : OnePoint ℂ))
    (hKa : ∀ t s, K (t, s) ≠ OnePoint.infty ∧ ∀ j ∈ S, K (t, s) ≠ (P t j : OnePoint ℂ))
    (Y : Set (OnePoint ℂ))
    (hY : ∀ w, w ≠ OnePoint.infty → (∀ j ∈ S, w ≠ (P 1 j : OnePoint ℂ)) → w ∈ Y)
    {y : Y} (γ γ' : Path y y) (hγ : ∀ s, (γ s : OnePoint ℂ) = K (1, s))
    (hγ' : ∀ s, (γ' s : OnePoint ℂ) = OnePoint.map (Φ 1) (K (0, s))) :
    γ'.Homotopic γ := by
  have hE2 : ∀ t w, (E (t, w)).2 = OnePoint.map (Φ t) w := fun t w ↦ by rw [hE]
  have hEs : ∀ (t : unitInterval) w, (E.symm (t, w)).1 = t := by
    intro t w
    have h := congrArg Prod.fst (E.apply_symm_apply (t, w))
    rw [hE] at h
    exact h
  have hEs2 : ∀ (t : unitInterval) w, OnePoint.map (Φ t) (E.symm (t, w)).2 = w := by
    intro t w
    have h := E.apply_symm_apply (t, w)
    rw [show E.symm (t, w) = ((E.symm (t, w)).1, (E.symm (t, w)).2) from rfl, hEs, hE] at h
    exact congrArg Prod.snd h
  have hinv : ∀ (t : unitInterval) w w', OnePoint.map (Φ t) w' = w → (E.symm (t, w)).2 = w' := by
    intro t w w' h
    apply (b65x_map_bijective (hbij t)).1
    rw [hEs2, h]
  -- the pulled-back family
  let W : unitInterval × unitInterval → OnePoint ℂ := fun q ↦ (E.symm (q.1, K q)).2
  have hWc : Continuous W :=
    continuous_snd.comp (E.symm.continuous.comp (continuous_fst.prodMk K.continuous))
  let G : unitInterval × unitInterval → OnePoint ℂ := fun q ↦ OnePoint.map (Φ 1) (W q)
  have hGc : Continuous G := by
    have h : G = fun q ↦ (E (1, W q)).2 := funext fun q ↦ (hE2 1 (W q)).symm
    rw [h]
    exact continuous_snd.comp (E.continuous.comp (continuous_const.prodMk hWc))
  have hmap_inf : ∀ (t : unitInterval) w, OnePoint.map (Φ t) w = OnePoint.infty →
      w = OnePoint.infty := by
    intro t w h
    apply (b65x_map_bijective (hbij t)).1
    rw [h]; rfl
  have hmapP : ∀ (t : unitInterval) w j, OnePoint.map (Φ t) w = (P t j : OnePoint ℂ) →
      w = (P 0 j : OnePoint ℂ) := by
    intro t w j h
    apply (b65x_map_bijective (hbij t)).1
    rw [h, OnePoint.map_some, htr t t.2]
  have hGY : ∀ q, G q ∈ Y := by
    intro q
    have hWq : OnePoint.map (Φ q.1) (W q) = K q := hEs2 q.1 (K q)
    apply hY
    · intro h
      have h1 := hmap_inf 1 _ h
      apply (hKa q.1 q.2).1
      rw [← hWq, h1]; rfl
    · intro j hj h
      have h1 := hmapP 1 _ j h
      apply (hKa q.1 q.2).2 j hj
      rw [← hWq, h1, OnePoint.map_some, htr q.1 q.1.2]
  have hBfix : ∀ (t : unitInterval), OnePoint.map (Φ t) (P 0 b : OnePoint ℂ) = (P 0 b : OnePoint ℂ) := by
    intro t
    rw [OnePoint.map_some, htr t t.2, hb t t.2]
  have hB1 : OnePoint.map (Φ 1) (P 0 b : OnePoint ℂ) = (P 0 b : OnePoint ℂ) := hBfix 1
  have hy : (y : OnePoint ℂ) = (P 0 b : OnePoint ℂ) := by
    rw [← γ.source, hγ, (hKb 1).1]
  refine ⟨{ toFun := fun q ↦ ⟨G q, hGY q⟩
            continuous_toFun := hGc.subtype_mk _
            map_zero_left := fun s ↦ ?_
            map_one_left := fun s ↦ ?_
            prop' := fun t s hs ↦ ?_ }⟩
  · apply Subtype.ext
    change OnePoint.map (Φ 1) (W (0, s)) = ((γ' s : Y) : OnePoint ℂ)
    rw [hγ']
    congr 1
    apply hinv
    change OnePoint.map (Φ 0) (K (0, s)) = K (0, s)
    induction K (0, s) using OnePoint.rec with
    | infty => rfl
    | coe z => simp [h0]
  · apply Subtype.ext
    change OnePoint.map (Φ 1) (W (1, s)) = ((γ s : Y) : OnePoint ℂ)
    rw [hγ]
    exact hEs2 1 (K (1, s))
  · rcases hs with rfl | rfl
    · apply Subtype.ext
      change OnePoint.map (Φ 1) (W (t, 0)) = (γ' 0 : OnePoint ℂ)
      rw [γ'.source, hy]
      have : W (t, 0) = (P 0 b : OnePoint ℂ) := by
        apply hinv
        rw [(hKb t).1, hBfix]
      rw [this, hB1]
    · apply Subtype.ext
      change OnePoint.map (Φ 1) (W (t, 1)) = (γ' 1 : OnePoint ℂ)
      rw [γ'.target, hy]
      have : W (t, 1) = (P 0 b : OnePoint ℂ) := by
        apply hinv
        rw [(hKb t).2, hBfix]
      rw [this, hB1]

end HodgeLean.Foundations.Program

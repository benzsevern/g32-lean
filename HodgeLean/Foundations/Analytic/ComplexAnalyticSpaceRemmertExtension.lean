import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertMain
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertStein

/-! # A local Remmert–Stein extension theorem

Lane `an-rem`, prefix `anrem_`. The local form `anrem_LocalRSStmt` of the Remmert–Stein theorem: in
an open set `Ω ⊆ ℂⁿ`, a set `B` analytic in `Ω \ T` and of pure dimension `d + 1` has analytic
closure at the points of a set `T`, analytic in `Ω` of dimension at most `d` (Remmert–Stein,
Math. Ann. 126 (1953), Satz 13; Demailly, *Complex Analytic and Differential Geometry*, II,
Theorem 8.7). The proof is the box construction of `ComplexAnalyticSpaceRemmertStein` (generic
projection, proper box, bounded symmetric sheet coefficients continued across the projected
exceptional set), with closedness required only inside the ball around the point.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology Polynomial

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

open private adim9_frequently_ne_zero_finset adim9_fibre_card_of_sheets
  adim9_moment_observables_separate adim9_local_sheets_at
  from HodgeLean.Foundations.AnalyticGermRSAssemblyProofs

/-! ### Box lemmas needing closedness only inside the closed ball -/

theorem anrem_box_fibre_compact' {n p : ℕ} (K : Set (Fin n → ℂ)) {a : Fin n → ℂ} {R : ℝ}
    (hK : IsClosed (K ∩ Metric.closedBall a R)) (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)) (r : ℝ)
    (hsph : ∀ z ∈ K, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖) (w : Fin p → ℂ) (hw : ‖w - ξ a‖ < r) :
    IsCompact {z | z ∈ K ∧ ‖z - a‖ < R ∧ ξ z = w} := by
  have h := anr_box_fibre_compact (K ∩ Metric.closedBall a R) hK ξ a R r
    (fun z hz ↦ hsph z hz.1) w hw
  convert h using 1
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_eq_norm]
  constructor
  · rintro ⟨hz, hzR, hzw⟩; exact ⟨⟨hz, hzR.le⟩, hzR, hzw⟩
  · rintro ⟨⟨hz, -⟩, hzR, hzw⟩; exact ⟨hz, hzR, hzw⟩

theorem anrem_box_tube' {n p : ℕ} (K : Set (Fin n → ℂ)) {a : Fin n → ℂ} {R : ℝ}
    (hK : IsClosed (K ∩ Metric.closedBall a R)) (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)) (r : ℝ)
    (hsph : ∀ z ∈ K, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖) (w : Fin p → ℂ)
    (hw : ‖w - ξ a‖ < r) (O : Set (Fin n → ℂ)) (hO : IsOpen O)
    (hfib : ∀ z ∈ K, ‖z - a‖ < R → ξ z = w → z ∈ O) :
    ∀ᶠ v in 𝓝 w, ∀ z ∈ K, ‖z - a‖ < R → ξ z = v → z ∈ O := by
  have h := anr_box_tube (K ∩ Metric.closedBall a R) hK ξ a R r (fun z hz ↦ hsph z hz.1) w hw O hO
    (fun z hz hzR hzw ↦ hfib z hz.1 hzR hzw)
  filter_upwards [h] with v hv z hz hzR hzv
  exact hv z ⟨hz, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hzR.le⟩ hzR hzv

theorem anrem_fib_finite' {n p : ℕ} (B K : Set (Fin n → ℂ)) {a : Fin n → ℂ} {R : ℝ}
    (hKc : IsClosed (K ∩ Metric.closedBall a R)) (hBK : B ⊆ K)
    (hBloc : ∀ y ∈ B, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ B ↔ ∀ j, f j z = 0))
    (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)) (r : ℝ)
    (hsph : ∀ z ∈ K, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖) (w : Fin p → ℂ) (hw : ‖w - ξ a‖ < r)
    (hKB : ∀ z ∈ K, ‖z - a‖ < R → ξ z = w → z ∈ B) :
    {z | z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = w}.Finite := by
  have hFw : {z | z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = w} = {z | z ∈ K ∧ ‖z - a‖ < R ∧ ξ z = w} := by
    ext z
    constructor
    · rintro ⟨hz, hzR, hzw⟩
      exact ⟨hBK hz, hzR, hzw⟩
    · rintro ⟨hz, hzR, hzw⟩
      exact ⟨hKB z hz hzR hzw, hzR, hzw⟩
  have hc : IsCompact {z | z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = w} := by
    rw [hFw]; exact anrem_box_fibre_compact' K hKc ξ r hsph w hw
  exact adim9_compact_analytic_finite n _ hc fun z hz ↦
    anr_fibre_loc B z (hBloc z hz.1) ξ w a R hz.2.1

theorem anrem_good_base' (N d : ℕ) (B K : Set (Fin (N + 1) → ℂ)) {a : Fin (N + 1) → ℂ} {R : ℝ}
    (hKc : IsClosed (K ∩ Metric.closedBall a R)) (hBK : B ⊆ K)
    (hBloc : ∀ y ∈ B, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ B ↔ ∀ j, f j z = 0))
    (hpure : ∀ y ∈ B, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) B y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (ξ : (Fin (N + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) (r : ℝ)
    (hsph : ∀ z ∈ K, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖)
    (G : Set (Fin (d + 1) → ℂ)) (hGo : IsOpen G) (hGball : G ⊆ Metric.ball (ξ a) r)
    (hKB : ∀ z ∈ K, ‖z - a‖ < R → ξ z ∈ G → z ∈ B)
    (w : Fin (d + 1) → ℂ) (hw : w ∈ G) :
    ∃ (U : Set (Fin (d + 1) → ℂ)) (δ : (Fin (d + 1) → ℂ) → ℂ) (M : ℕ),
      IsOpen U ∧ w ∈ U ∧ U ⊆ G ∧ AnalyticOnNhd ℂ δ U ∧
      (∀ v ∈ U, ¬ (δ =ᶠ[𝓝 v] fun _ ↦ 0)) ∧
      ∀ v ∈ U, δ v ≠ 0 → ∃ k, k ≤ M ∧ ∃ (W : Set (Fin (d + 1) → ℂ))
        (r' : Fin k → (Fin (d + 1) → ℂ) → (Fin (N + 1) → ℂ)),
        IsOpen W ∧ v ∈ W ∧ W ⊆ U ∧ (∀ j, AnalyticOnNhd ℂ (r' j) W) ∧
        ∀ v' ∈ W, Function.Injective (fun j ↦ r' j v') ∧
          ∀ z, (z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = v') ↔ ∃ j, r' j v' = z := by
  set B' := B ∩ Metric.ball a R
  set K' := K ∩ Metric.closedBall a R
  have hballR : IsOpen (Metric.ball a R) := Metric.isOpen_ball
  have hB'loc : ∀ y ∈ B', ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ B' ↔ ∀ j, f j z = 0) := fun y hy ↦
    anrem_locEq_open (U := (hBloc y hy.1).choose) (hBloc y hy.1).choose_spec.1
      (hBloc y hy.1).choose_spec.2.2.choose_spec.choose_spec.1
      (hBloc y hy.1).choose_spec.2.2.choose_spec.choose_spec.2 hballR
      ⟨(hBloc y hy.1).choose_spec.2.1, hy.2⟩
  have hB'pure : ∀ y ∈ B', ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) B' y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    intro y hy Q hQ
    rw [anrem_germ_inter_nhds B _ y (hballR.mem_nhds hy.2)] at hQ
    exact hpure y hy.1 Q hQ
  have hmemB : ∀ z, ‖z - a‖ < R → (z ∈ B' ↔ z ∈ B) := fun z hz ↦
    ⟨fun h ↦ h.1, fun h ↦ ⟨h, by rw [Metric.mem_ball, dist_eq_norm]; exact hz⟩⟩
  obtain ⟨U, δ, M, hU, hwU, hUG, hδ, hnz, hsh⟩ := anr_good_base N d B' K' hKc
    (fun z hz ↦ ⟨hBK hz.1, Metric.ball_subset_closedBall hz.2⟩) hB'loc hB'pure ξ a R r
    (fun z hz ↦ hsph z hz.1) G hGo hGball
    (fun z hz hzR hzG ↦ (hmemB z hzR).2 (hKB z hz.1 hzR hzG)) w hw
  refine ⟨U, δ, M, hU, hwU, hUG, hδ, hnz, fun v hv hδv ↦ ?_⟩
  obtain ⟨k, hk, W, r', hW, hvW, hWU, hra, hr⟩ := hsh v hv hδv
  refine ⟨k, hk, W, r', hW, hvW, hWU, hra, fun v' hv' ↦ ⟨(hr v' hv').1, fun z ↦ ?_⟩⟩
  rw [← (hr v' hv').2 z]
  exact ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨(hmemB z h2).2 h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1.1, h2, h3⟩⟩

/-- The projection into the base ball of the part of a set of dimension at most `d` inside the
box lies locally in nowhere locally zero hypersurfaces, and is relatively closed. -/
theorem anrem_image_thin' (N d : ℕ) (T : Set (Fin (N + 1) → ℂ)) {a : Fin (N + 1) → ℂ} {R : ℝ}
    (hTc : IsClosed (T ∩ Metric.closedBall a R))
    (hTloc : ∀ y ∈ T, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ T ↔ ∀ j, f j z = 0))
    (hdimT : ∀ y ∈ T, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) T y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) ≤ (d : WithBot ℕ∞))
    (ξ : (Fin (N + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) (r : ℝ)
    (hsph : ∀ z ∈ T, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖) :
    (∀ x ∈ Metric.ball (ξ a) r, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧
      W ⊆ Metric.ball (ξ a) r ∧ ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧
        ξ '' {z | z ∈ T ∧ ‖z - a‖ < R ∧ ‖ξ z - ξ a‖ < r} ∩ W ⊆ {y | δ y = 0}) ∧
    IsOpen (Metric.ball (ξ a) r \ ξ '' {z | z ∈ T ∧ ‖z - a‖ < R ∧ ‖ξ z - ξ a‖ < r}) := by
  classical
  set A := ξ '' {z | z ∈ T ∧ ‖z - a‖ < R ∧ ‖ξ z - ξ a‖ < r}
  have hballR : IsOpen {z : Fin (N + 1) → ℂ | ‖z - a‖ < R} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · have hx' : ‖x - ξ a‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    set Fx := {z | z ∈ T ∧ ‖z - a‖ < R ∧ ξ z = x}
    have hFxc : IsCompact Fx := anrem_box_fibre_compact' T hTc ξ r hsph x hx'
    have hFxf : Fx.Finite := adim9_compact_analytic_finite (N + 1) Fx hFxc fun z hz ↦
      anr_fibre_loc T z (hTloc z hz.1) ξ x a R hz.2.1
    have hiso : ∀ y ∈ Fx, ∀ᶠ y' in 𝓝 y, y' ∈ T → ξ y' = ξ y → y' = y := by
      intro y hy
      have hcl : IsClosed (Fx \ {y}) := (hFxf.subset sdiff_subset).isClosed
      filter_upwards [hcl.isOpen_compl.mem_nhds (fun h ↦ h.2 rfl),
        hballR.mem_nhds hy.2.1] with y' hy' hy'R hy'T hξ
      by_contra hne
      exact hy' ⟨⟨hy'T, hy'R, hξ.trans hy.2.2⟩, hne⟩
    have hdata : ∀ y ∈ Fx, ∃ (O : Set (Fin (N + 1) → ℂ)) (ρ : ℝ)
        (δ : (Fin (d + 1) → ℂ) → ℂ), IsOpen O ∧ y ∈ O ∧
        0 < ρ ∧ AnalyticOnNhd ℂ δ (Metric.ball (ξ y) ρ) ∧
        (∀ w ∈ Metric.ball (ξ y) ρ, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
        ∀ z ∈ T ∩ O, δ (ξ z) = 0 := by
      intro y hy
      obtain ⟨U, hU, hyU, m, f, hf, hUT⟩ := hTloc y hy.1
      exact anr_image_thin_at N d T y hy.1 U hU hyU m f hf hUT ξ (hiso y hy) (hdimT y hy.1)
    choose! O ρ δ hOo hyO hρ hδ hnz hvan using hdata
    set Fs := hFxf.toFinset
    have hFs : ∀ y, y ∈ Fs ↔ y ∈ Fx := fun y ↦ Set.Finite.mem_toFinset _
    have hξy : ∀ y ∈ Fs, ξ y = x := fun y hy ↦ ((hFs y).mp hy).2.2
    have hOU : IsOpen (⋃ y ∈ Fs, O y) := isOpen_biUnion fun y hy ↦ hOo y ((hFs y).mp hy)
    have htube := anrem_box_tube' T hTc ξ r hsph x hx' _ hOU fun z hz hzR hzx ↦
      mem_biUnion ((hFs z).mpr ⟨hz, hzR, hzx⟩) (hyO z ⟨hz, hzR, hzx⟩)
    set W := Metric.ball (ξ a) r ∩ (⋂ y ∈ Fs, Metric.ball x (ρ y)) ∩
      interior {v | ∀ z ∈ T, ‖z - a‖ < R → ξ z = v → z ∈ ⋃ y ∈ Fs, O y}
    have hWo : IsOpen W := (Metric.isOpen_ball.inter (isOpen_biInter_finset fun y _ ↦
      Metric.isOpen_ball)).inter isOpen_interior
    have hWball : ∀ v ∈ W, ∀ y ∈ Fs, v ∈ Metric.ball (ξ y) (ρ y) := by
      intro v hv y hy
      rw [hξy y hy]
      exact mem_iInter₂.mp hv.1.2 y hy
    refine ⟨W, hWo, ⟨⟨hx, mem_iInter₂.mpr fun y hy ↦ Metric.mem_ball_self
      (hρ y ((hFs y).mp hy))⟩, mem_interior_iff_mem_nhds.mpr htube⟩,
      fun v hv ↦ hv.1.1, fun v ↦ ∏ y ∈ Fs, δ y v, ?_, ?_, ?_⟩
    · intro v hv
      exact Finset.analyticAt_fun_prod _ fun y hy ↦ hδ y ((hFs y).mp hy) v (hWball v hv y hy)
    · intro v hv hev
      have hfr := adim9_frequently_ne_zero_finset Fs (fun y ↦ Metric.ball (ξ y) (ρ y))
        (fun y _ ↦ Metric.isOpen_ball) δ
        (fun y hy ↦ (hδ y ((hFs y).mp hy)).continuousOn)
        (fun y hy ↦ hnz y ((hFs y).mp hy)) v (hWball v hv)
      obtain ⟨u, hu, hu0⟩ := (hfr.and_eventually hev).exists
      exact (Finset.prod_ne_zero_iff.mpr fun y hy ↦ (hu y hy).2) hu0
    · rintro v ⟨⟨z, ⟨hzT, hzR, -⟩, rfl⟩, hv⟩
      have hzO := interior_subset hv.2 z hzT hzR rfl
      obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp hzO
      exact Finset.prod_eq_zero hy (hvan y ((hFs y).mp hy) z ⟨hzT, hzy⟩)
  · rw [isOpen_iff_mem_nhds]
    rintro x ⟨hx, hxA⟩
    have hx' : ‖x - ξ a‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    have htube := anrem_box_tube' T hTc ξ r hsph x hx' ∅ isOpen_empty fun z hz hzR hzx ↦
      hxA ⟨z, ⟨hz, hzR, by rwa [hzx]⟩, hzx⟩
    filter_upwards [htube, Metric.isOpen_ball.mem_nhds hx] with v hv hvb
    refine ⟨hvb, ?_⟩
    rintro ⟨z, ⟨hzT, hzR, -⟩, rfl⟩
    exact hv z hzT hzR rfl

/-- On a box over which the projection is proper, and given a dense set of points of the pure
set isolated in their fibres, the closure of the pure set is cut out by finitely many analytic
equations: monic polynomials in moment observables whose coefficients are the bounded
symmetric functions of the sheets, continued across the projected exceptional set. -/
theorem anrem_box_equations' (N d : ℕ) (T B : Set (Fin (N + 1) → ℂ)) {a : Fin (N + 1) → ℂ}
    {R : ℝ} (hTc : IsClosed (T ∩ Metric.closedBall a R))
    (hKc : IsClosed ((closure B ∪ T) ∩ Metric.closedBall a R))
    (hTloc : ∀ y ∈ T, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ T ↔ ∀ j, f j z = 0))
    (hdimT : ∀ y ∈ T, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) T y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) ≤ (d : WithBot ℕ∞))
    (hBloc : ∀ y ∈ B, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ B ↔ ∀ j, f j z = 0))
    (hpure : ∀ y ∈ B, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) B y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hclB : ∀ z ∈ closure B, ‖z - a‖ < R → z ∈ B ∪ T)
    (ξ : (Fin (N + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) (r : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hsph : ∀ z ∈ closure B ∪ T, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖)
    (DB : Set (Fin (N + 1) → ℂ)) (hDB : DB ⊆ B) (hDBd : B ⊆ closure DB)
    (hDBiso : ∀ y ∈ DB, ∀ᶠ z in 𝓝 y, z ∈ B → ξ z = ξ y → z = y) :
    ∃ (m : ℕ) (f : Fin m → (Fin (N + 1) → ℂ) → ℂ),
      (∀ j, AnalyticOnNhd ℂ (f j) {z | ‖ξ z - ξ a‖ < r ∧ ‖z - a‖ < R}) ∧
      ∀ z ∈ {z | ‖ξ z - ξ a‖ < r ∧ ‖z - a‖ < R}, (z ∈ closure B ↔ ∀ j, f j z = 0) := by
  classical
  set K := closure B ∪ T
  have hBK : B ⊆ K := subset_closure.trans subset_union_left
  set V' := Metric.ball (ξ a) r
  set A' := ξ '' {z | z ∈ T ∧ ‖z - a‖ < R ∧ ‖ξ z - ξ a‖ < r}
  obtain ⟨hA'thin, hGo⟩ := anrem_image_thin' N d T hTc hTloc hdimT ξ r
    (fun z hz ↦ hsph z (Or.inr hz))
  set G := V' \ A'
  have hmemV : ∀ v, v ∈ V' ↔ ‖v - ξ a‖ < r := fun v ↦ by
    rw [Metric.mem_ball, dist_eq_norm]
  have hKB : ∀ z ∈ K, ‖z - a‖ < R → ξ z ∈ G → z ∈ B := by
    intro z hz hzR hzG
    have hzr : ‖ξ z - ξ a‖ < r := (hmemV _).mp hzG.1
    rcases hz with hz | hz
    · rcases hclB z hz hzR with h | h
      · exact h
      · exact absurd ⟨z, ⟨h, hzR, hzr⟩, rfl⟩ hzG.2
    · exact absurd ⟨z, ⟨hz, hzR, hzr⟩, rfl⟩ hzG.2
  set fib : (Fin (d + 1) → ℂ) → Set (Fin (N + 1) → ℂ) := fun v ↦
    {z | z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = v}
  have hfibfin : ∀ v ∈ G, (fib v).Finite := fun v hv ↦
    anrem_fib_finite' B K hKc hBK hBloc ξ r hsph v ((hmemV v).mp hv.1)
      fun z hz hzR hzv ↦ hKB z hz hzR (hzv ▸ hv)
  -- good parameters and the bad set
  let Good : (Fin (d + 1) → ℂ) → Prop := fun v ↦ ∃ (k : ℕ) (W : Set (Fin (d + 1) → ℂ))
    (r' : Fin k → (Fin (d + 1) → ℂ) → (Fin (N + 1) → ℂ)),
    IsOpen W ∧ v ∈ W ∧ W ⊆ G ∧ (∀ j, AnalyticOnNhd ℂ (r' j) W) ∧
    ∀ v' ∈ W, Function.Injective (fun j ↦ r' j v') ∧ ∀ z, z ∈ fib v' ↔ ∃ j, r' j v' = z
  set E := {v | v ∈ G ∧ ¬ Good v}
  have hEthin : ∀ x ∈ G, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧ W ⊆ G ∧
      ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ E ∩ W ⊆ {y | δ y = 0} := by
    intro x hx
    obtain ⟨U, δ, M, hUo, hxU, hUG, hδ, hnz, hsh⟩ := anrem_good_base' N d B K hKc hBK hBloc
      hpure ξ r hsph G hGo sdiff_subset hKB x hx
    refine ⟨U, hUo, hxU, hUG, δ, hδ, hnz, ?_⟩
    rintro v ⟨⟨-, hvgood⟩, hvU⟩
    by_contra hδv
    obtain ⟨k, -, W, r', hWo, hvW, hWU, hra, hr⟩ := hsh v hvU hδv
    exact hvgood ⟨k, W, r', hWo, hvW, hWU.trans hUG, hra, hr⟩
  set D := G \ E
  have hDG : ∀ v ∈ D, Good v := by
    rintro v ⟨hvG, hvE⟩
    by_contra h
    exact hvE ⟨hvG, h⟩
  have hGoodW : ∀ v, Good v → ∃ (k : ℕ) (W : Set (Fin (d + 1) → ℂ))
      (r' : Fin k → (Fin (d + 1) → ℂ) → (Fin (N + 1) → ℂ)),
      IsOpen W ∧ v ∈ W ∧ W ⊆ D ∧ (∀ j, AnalyticOnNhd ℂ (r' j) W) ∧
      ∀ v' ∈ W, Function.Injective (fun j ↦ r' j v') ∧ ∀ z, z ∈ fib v' ↔ ∃ j, r' j v' = z := by
    rintro v ⟨k, W, r', hWo, hvW, hWG, hra, hr⟩
    refine ⟨k, W, r', hWo, hvW, fun v' hv' ↦ ⟨hWG hv', fun hE ↦ hE.2 ?_⟩, hra, hr⟩
    exact ⟨k, W, r', hWo, hv', hWG, hra, hr⟩
  have hDo : IsOpen D := by
    rw [isOpen_iff_mem_nhds]
    intro v hv
    obtain ⟨k, W, r', hWo, hvW, hWD, -, -⟩ := hGoodW v (hDG v hv)
    exact Filter.mem_of_superset (hWo.mem_nhds hvW) hWD
  have hDconn : IsPreconnected D :=
    anr_thin2_preconnected V' A' E (convex_ball _ _).isPreconnected hA'thin hEthin hDo
  have hDdense : V' ⊆ closure D := anr_thin2_dense V' A' E hA'thin hEthin
  -- the sheet count is constant on the good set
  set sf : (Fin (d + 1) → ℂ) → Finset (Fin (N + 1) → ℂ) := fun v ↦
    if h : (fib v).Finite then h.toFinset else ∅
  have hsf : ∀ v, (fib v).Finite → ∀ z, z ∈ sf v ↔ z ∈ fib v := by
    intro v hv z
    simp only [sf, hv, ↓reduceDIte, Set.Finite.mem_toFinset]
  have hsheetfin : ∀ (k : ℕ) (r' : Fin k → (Fin (d + 1) → ℂ) → (Fin (N + 1) → ℂ)) v',
      (∀ z, z ∈ fib v' ↔ ∃ j, r' j v' = z) → (fib v').Finite := by
    intro k r' v' h
    refine (Set.finite_range fun j ↦ r' j v').subset fun z hz ↦ ?_
    obtain ⟨j, hj⟩ := (h z).mp hz
    exact ⟨j, hj⟩
  have hcardloc : ∀ v ∈ D, ∃ k : ℕ, ∀ᶠ v' in 𝓝 v, (sf v').card = k := by
    intro v hv
    obtain ⟨k, W, r', hWo, hvW, -, -, hr⟩ := hGoodW v (hDG v hv)
    refine ⟨k, Filter.mem_of_superset (hWo.mem_nhds hvW) fun v' hv' ↦ ?_⟩
    have hfin := hsheetfin k r' v' (hr v' hv').2
    exact adim9_fibre_card_of_sheets sf r' v'
      ⟨(hr v' hv').1, fun z ↦ (hsf v' hfin z).trans ((hr v' hv').2 z)⟩
  obtain ⟨v₀, hv₀⟩ : D.Nonempty := by
    have h := hDdense (Metric.mem_ball_self hr)
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, closure_empty] at h
    exact h
  set M := (sf v₀).card
  have hcardM : ∀ v ∈ D, (sf v).card = M := by
    intro v hv
    have hcont : ContinuousOn (fun v ↦ (sf v).card) D := by
      intro x hx
      obtain ⟨k, hk⟩ := hcardloc x hx
      exact (continuousAt_const.congr (hk.mono fun v hv ↦ hv.symm)).continuousWithinAt
    exact hDconn.constant_of_mapsTo (T := univ)
      (isDiscrete_iff_discreteTopology.mpr inferInstance) hcont (mapsTo_univ _ _) hv hv₀
  have hsheetsM : ∀ x ∈ D, ∃ (W : Set (Fin (d + 1) → ℂ))
      (r' : Fin M → (Fin (d + 1) → ℂ) → (Fin (N + 1) → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ D ∧ (∀ j, AnalyticOnNhd ℂ (r' j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r' j y) ∧
        ∀ z, z ∈ sf y ↔ ∃ j, r' j y = z := by
    intro x hx
    obtain ⟨k, W, r', hWo, hxW, hWD, hra, hr⟩ := hGoodW x (hDG x hx)
    have hr' : ∀ y ∈ W, Function.Injective (fun j ↦ r' j y) ∧
        ∀ z, z ∈ sf y ↔ ∃ j, r' j y = z := fun y hy ↦
      ⟨(hr y hy).1, fun z ↦ (hsf y (hsheetfin k r' y (hr y hy).2) z).trans ((hr y hy).2 z)⟩
    have hk : k = M := by
      rw [← hcardM x hx, adim9_fibre_card_of_sheets sf r' x (hr' x hxW)]
    subst hk
    exact ⟨W, r', hWo, hxW, hWD, hra, hr'⟩
  -- bounded symmetric coefficients, continued to the base ball
  have hbnd : ∀ x ∈ D, ∀ z ∈ sf x, ‖z‖ ≤ ‖a‖ + R := by
    intro x hx z hz
    have hz' := (hsf x (hfibfin x hx.1) z).mp hz
    calc ‖z‖ = ‖a + (z - a)‖ := by rw [add_sub_cancel]
      _ ≤ ‖a‖ + ‖z - a‖ := norm_add_le _ _
      _ ≤ ‖a‖ + R := by linarith [hz'.2.1]
  have hcoefs : ∀ obs : (Fin (N + 1) → ℂ) →L[ℂ] ℂ, ∃ b : Fin M → (Fin (d + 1) → ℂ) → ℂ,
      (∀ i, AnalyticOnNhd ℂ (b i) V') ∧ ∀ w ∈ D, ∀ t : ℂ,
        (adim9_fibrePolynomial (N + 1) (sf w) obs).eval t =
          t ^ M + ∑ i : Fin M, b i w * t ^ (i : ℕ) := by
    intro obs
    have hRb : 0 ≤ ‖obs‖ * (‖a‖ + R) := by positivity
    have hobs : ∀ x ∈ D, ∀ z ∈ sf x, ‖obs z‖ ≤ ‖obs‖ * (‖a‖ + R) := fun x hx z hz ↦
      (obs.le_opNorm z).trans (mul_le_mul_of_nonneg_left (hbnd x hx z hz) (norm_nonneg _))
    obtain ⟨hcoef, hmon⟩ := adim9_sheet_coefficients_aux (N + 1) (d + 1) M D sf hsheetsM obs
      _ hRb hobs
    have hext : ∀ i : Fin M, ∃ b : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ b V' ∧
        EqOn b (fun w ↦ (adim9_fibrePolynomial (N + 1) (sf w) obs).coeff i) D := by
      intro i
      obtain ⟨F, hF, hFf, -⟩ := anr_thin2_extension V' A' E hA'thin hEthin
        (fun w ↦ (adim9_fibrePolynomial (N + 1) (sf w) obs).coeff i) (hcoef i) _
        (fun x hx ↦ (hmon x hx).2.2.1 i)
      exact ⟨F, hF, hFf⟩
    choose b hb hbeq using hext
    refine ⟨b, hb, fun w hw t ↦ ?_⟩
    obtain ⟨hm, hdeg, -, -⟩ := hmon w hw
    conv_lhs => rw [hm.as_sum, hdeg]
    simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
    rw [Finset.sum_range (fun i ↦ (adim9_fibrePolynomial (N + 1) (sf w) obs).coeff i *
      t ^ i)]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hbeq i hw]
  -- moment observables and the equations
  let ℓ : Fin (N * M + 1) → (Fin (N + 1) → ℂ) →L[ℂ] ℂ := fun t ↦
    ∑ i : Fin (N + 1), (((t : ℕ) : ℂ) ^ (i : ℕ)) •
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (N + 1) ↦ ℂ) i
  have hℓ : ∀ t z, ℓ t z = ∑ i : Fin (N + 1), ((t : ℕ) : ℂ) ^ (i : ℕ) * z i := by
    intro t z
    simp [ℓ, sum_apply]
  choose b hb heq using fun t ↦ hcoefs (ℓ t)
  let f : Fin (N * M + 1) → (Fin (N + 1) → ℂ) → ℂ := fun t z ↦
    ℓ t z ^ M + ∑ i : Fin M, b t i (ξ z) * ℓ t z ^ (i : ℕ)
  set Box := {z : Fin (N + 1) → ℂ | ‖ξ z - ξ a‖ < r ∧ ‖z - a‖ < R}
  have hBoxo : IsOpen Box :=
    (isOpen_lt (ξ.continuous.sub continuous_const).norm continuous_const).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
  have hBoxV : ∀ z ∈ Box, ξ z ∈ V' := fun z hz ↦ (hmemV _).mpr hz.1
  have hfa : ∀ t, AnalyticOnNhd ℂ (f t) Box := by
    intro t z hz
    have hℓa : AnalyticAt ℂ (ℓ t) z := (ℓ t).analyticAt z
    refine (hℓa.pow M).add (Finset.analyticAt_fun_sum _ fun i _ ↦ ?_)
    exact ((hb t i (ξ z) (hBoxV z hz)).comp (ξ.analyticAt z)).mul (hℓa.pow _)
  set Gs := B ∩ Box ∩ ξ ⁻¹' D
  have hfG : ∀ t, ∀ y ∈ Gs, f t y = 0 := by
    intro t y hy
    have h := heq t (ξ y) hy.2 (ℓ t y)
    simp only [f, ← h, adim9_fibrePolynomial, eval_prod, eval_sub, eval_X, eval_C]
    refine Finset.prod_eq_zero (i := y) ?_ (sub_self _)
    exact (hsf (ξ y) (hfibfin (ξ y) hy.2.1) y).mpr ⟨hy.1.1, hy.1.2.2, rfl⟩
  -- density of the good part
  have hstepG : ∀ y ∈ B, y ∈ Box → ξ y ∈ G → y ∈ closure Gs := by
    intro y hyB hyBox hyG
    obtain ⟨W, hWo, hyW, hWG, δ, hδ, hnz, hEW⟩ := hEthin (ξ y) hyG
    have hiso := anr_fib_iso B ξ a R y hyBox.2 (hfibfin (ξ y) hyG)
    have h1 := anr_thin_at N d B y hyB (hBloc y hyB) (hpure y hyB) ξ hiso W hWo hyW δ
      (hδ _ hyW) (hnz _ hyW)
    refine closure_mono ?_ (anr_mem_closure_inter_open h1 hBoxo hyBox)
    rintro z ⟨⟨hzB, hzW, hδz⟩, hzBox⟩
    exact ⟨⟨hzB, hzBox⟩, hWG hzW, fun hzE ↦ hδz (hEW ⟨hzE, hzW⟩)⟩
  have hstepDB : ∀ y ∈ DB, y ∈ Box → y ∈ closure Gs := by
    intro y hyD hyBox
    have hyB := hDB hyD
    obtain ⟨W, hWo, hyW, hWV, δ, hδ, hnz, hAW⟩ := hA'thin (ξ y) (hBoxV y hyBox)
    have h1 := anr_thin_at N d B y hyB (hBloc y hyB) (hpure y hyB) ξ (hDBiso y hyD) W hWo
      hyW δ (hδ _ hyW) (hnz _ hyW)
    have h2 := anr_mem_closure_inter_open h1 hBoxo hyBox
    rw [← closure_closure (s := Gs)]
    refine closure_mono ?_ h2
    rintro z ⟨⟨hzB, hzW, hδz⟩, hzBox⟩
    exact hstepG z hzB hzBox ⟨hWV hzW, fun hzA ↦ hδz (hAW ⟨hzA, hzW⟩)⟩
  have hdense : ∀ z ∈ closure B, z ∈ Box → z ∈ closure Gs := by
    intro z hz hzBox
    have h1 : closure (B ∩ Box) ⊆ closure Gs := by
      rw [← closure_closure (s := Gs)]
      refine closure_mono fun y hy ↦ ?_
      have hy' := anr_mem_closure_inter_open (hDBd hy.1) hBoxo hy.2
      rw [← closure_closure (s := Gs)]
      exact closure_mono (fun x hx ↦ hstepDB x hx.1 hx.2) hy'
    exact h1 (anr_mem_closure_inter_open hz hBoxo hzBox)
  have hfwd : ∀ t, ∀ z ∈ Box, z ∈ closure Gs → f t z = 0 := by
    intro t z hz hzG
    exact ((hfa t z hz).continuousAt.continuousWithinAt).eq_const_of_mem_closure hzG (hfG t)
  -- the converse, by limits of whole fibres over good parameters
  have hbwd : ∀ z ∈ Box, (∀ t, f t z = 0) → z ∈ closure B := by
    intro z hz hf0
    obtain ⟨ws, hwsD, hws⟩ := mem_closure_iff_seq_limit.mp (hDdense (hBoxV z hz))
    let Ep : ℕ → Fin M → Fin (N + 1) → ℂ := fun m j ↦
      ((sf (ws m)).equivFin.symm (Fin.cast (hcardM _ (hwsD m)).symm j) : _)
    have hEmem : ∀ m j, Ep m j ∈ sf (ws m) := fun m j ↦ Finset.coe_mem _
    have hEimg : ∀ m, sf (ws m) = Finset.univ.image (Ep m) := by
      intro m
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hy
        refine ⟨Fin.cast (hcardM _ (hwsD m)) ((sf (ws m)).equivFin ⟨y, hy⟩), ?_⟩
        simp [Ep]
      · rintro ⟨j, rfl⟩
        exact hEmem m j
    have hEinj : ∀ m, Function.Injective (Ep m) := by
      intro m i j hij
      have := Subtype.ext hij
      simpa using (sf (ws m)).equivFin.symm.injective this
    have hEB : ∀ m j, Ep m j ∈ B ∧ ‖Ep m j‖ ≤ ‖a‖ + R := fun m j ↦
      ⟨((hsf _ (hfibfin _ (hwsD m).1) _).mp (hEmem m j)).1, hbnd _ (hwsD m) _ (hEmem m j)⟩
    have hEb : ∀ m, Ep m ∈ Metric.closedBall (0 : Fin M → Fin (N + 1) → ℂ) (‖a‖ + R) := by
      intro m
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j ↦ (hEB m j).2
    obtain ⟨Y, -, φ, hφ, hY⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hEb
    have hYj : ∀ j, Tendsto (fun m ↦ Ep (φ m) j) atTop (𝓝 (Y j)) :=
      fun j ↦ ((continuous_apply j).tendsto Y).comp hY
    have hYmem : ∀ j, Y j ∈ closure B := fun j ↦
      isClosed_closure.mem_of_tendsto (hYj j)
        (Eventually.of_forall fun m ↦ subset_closure (hEB (φ m) j).1)
    have hwφ : Tendsto (fun m ↦ ws (φ m)) atTop (𝓝 (ξ z)) := hws.comp hφ.tendsto_atTop
    have hroot : ∀ t, ∃ j, ℓ t z = ℓ t (Y j) := by
      intro t
      set x := ℓ t z
      have hlhs : Tendsto (fun m ↦ x ^ M + ∑ i : Fin M, b t i (ws (φ m)) * x ^ (i : ℕ))
          atTop (𝓝 (f t z)) := by
        refine tendsto_const_nhds.add (tendsto_finsetSum _ fun i _ ↦ ?_)
        exact (((hb t i (ξ z) (hBoxV z hz)).continuousAt.tendsto).comp hwφ).mul
          tendsto_const_nhds
      have hrhs : Tendsto (fun m ↦ ∏ j, (x - ℓ t (Ep (φ m) j))) atTop
          (𝓝 (∏ j, (x - ℓ t (Y j)))) :=
        tendsto_finsetProd _ fun j _ ↦
          tendsto_const_nhds.sub (((ℓ t).continuous.tendsto _).comp (hYj j))
      have hEq : ∀ m, x ^ M + ∑ i : Fin M, b t i (ws (φ m)) * x ^ (i : ℕ) =
          ∏ j, (x - ℓ t (Ep (φ m) j)) := by
        intro m
        rw [← heq t (ws (φ m)) (hwsD (φ m)) x, hEimg, adim9_fibrePolynomial,
          Finset.prod_image fun a _ b _ h ↦ hEinj (φ m) h]
        simp [eval_prod]
      have hlim := tendsto_nhds_unique (hlhs.congr hEq) hrhs
      rw [hf0 t] at hlim
      obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hlim.symm
      exact ⟨j, sub_eq_zero.mp hj⟩
    obtain ⟨j, hj⟩ := adim9_moment_observables_separate N M z Y fun t ↦ by
      obtain ⟨j, hj⟩ := hroot t
      exact ⟨j, by rw [← hℓ, ← hℓ, hj]⟩
    exact hj ▸ hYmem j
  exact ⟨N * M + 1, f, hfa, fun z hz ↦ ⟨fun h t ↦ hfwd t z hz (hdense z h hz),
    hbwd z hz⟩⟩

/-- Radii of a box around a point of the exceptional set, from closedness inside a ball. -/
theorem anrem_choose_radii' {n p : ℕ} (T B : Set (Fin n → ℂ)) {a : Fin n → ℂ} {R₀ : ℝ}
    (hR₀ : 0 < R₀)
    (hKc : ∀ ρ, ρ < R₀ → IsClosed ((closure B ∪ T) ∩ Metric.closedBall a ρ))
    (hclB : ∀ z ∈ closure B, ‖z - a‖ < R₀ → z ∈ B ∪ T) (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ))
    (hT : ∀ᶠ z in 𝓝 a, z ∈ T → ξ z = ξ a → z = a) (hB : (B ∩ {z | ξ z = ξ a}).Countable) :
    ∃ R : ℝ, 0 < R ∧ R < R₀ ∧ ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ closure B ∪ T, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖ := by
  obtain ⟨R₁, hR₁, hball⟩ := Metric.eventually_nhds_iff.mp hT
  set R₂ := min R₁ R₀
  have hR₂ : 0 < R₂ := lt_min hR₁ hR₀
  set Cn := (fun z ↦ ‖z - a‖) '' (B ∩ {z | ξ z = ξ a})
  have hCn : Cn.Countable := hB.image _
  obtain ⟨R, hR, hRC⟩ : ∃ R ∈ Ioo 0 R₂, R ∉ Cn := by
    by_contra h
    push Not at h
    have h0 := hCn.measure_zero MeasureTheory.volume
    have h1 : MeasureTheory.volume (Ioo 0 R₂) = 0 :=
      MeasureTheory.measure_mono_null (fun x hx ↦ h x hx) h0
    rw [Real.volume_Ioo] at h1
    have : (0 : ℝ) < R₂ - 0 := by linarith
    exact absurd h1 (by simpa using this)
  have hRR₀ : R < R₀ := lt_of_lt_of_le hR.2 (min_le_right _ _)
  have hsph : ∀ z ∈ closure B ∪ T, ξ z = ξ a → ‖z - a‖ ≠ R := by
    intro z hz hzξ hzR
    have hzT : z ∈ T → False := fun hzT ↦ by
      have hza := hball (show dist z a < R₁ by
        rw [dist_eq_norm, hzR]; exact lt_of_lt_of_le hR.2 (min_le_left _ _)) hzT hzξ
      rw [hza, sub_self, norm_zero] at hzR
      linarith [hR.1]
    rcases hz with hz | hz
    · rcases hclB z hz (by rw [hzR]; exact hRR₀) with h | h
      · exact hRC ⟨z, ⟨h, hzξ⟩, hzR⟩
      · exact hzT h
    · exact hzT hz
  obtain ⟨r, hr, hr'⟩ := anr_box_radius ((closure B ∪ T) ∩ Metric.closedBall a R) (hKc R hRR₀)
    ξ a R (fun z hz ↦ hsph z hz.1)
  exact ⟨R, hR.1, hRR₀, r, hr, fun z hz hzR ↦
    hr' z ⟨hz, by rw [Metric.mem_closedBall, dist_eq_norm, hzR]⟩ hzR⟩

/-- A set with local equations on an open set meets closed subsets of that open set in closed
sets. -/
theorem anrem_isClosed_inter_of_locEq {n : ℕ} {T Ω C : Set (Fin n → ℂ)}
    (h : ∀ z ∈ Ω, anrem_LocEq T z) (hC : IsClosed C) (hCΩ : C ⊆ Ω) : IsClosed (T ∩ C) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  by_cases hzC : z ∈ C
  · have hzT : z ∉ T := fun h' ↦ hz ⟨h', hzC⟩
    filter_upwards [anrem_eventually_not_mem (h z (hCΩ hzC)) hzT] with w hw hw'
    exact hw hw'.1
  · filter_upwards [hC.isOpen_compl.mem_nhds hzC] with w hw hw'
    exact hw hw'.2

/-- **The local Remmert–Stein theorem.** -/
theorem anrem_local_remmert_stein : anrem_LocalRSStmt := by
  intro n d T B Ω hΩ hTloc hTdim hBsub hBloc hpure a ⟨haT, haΩ⟩
  rcases n with _ | N
  · -- in `ℂ⁰` there is no pure set of positive dimension
    have hB : B = ∅ := by
      ext z
      simp only [mem_empty_iff_false, iff_false]
      intro hz
      obtain ⟨Q, hQ, hQd⟩ := anrem_exists_minimalPrime_ge (A := B) (y := z) (e := 0) (by
        have : Nontrivial (AnalyticGerm 0 ⧸ adim2_ideal 0 (adim2_germ 0 B z)) :=
          Ideal.Quotient.nontrivial_iff.2 (adim9b_germ_ideal_ne_top 0 B z hz)
        exact_mod_cast ringKrullDim_nonneg_of_nontrivial)
      have h1 := hpure z hz Q hQ
      have h2 := (anrem_dimension_le_iff B z 0).1 (anrem_dimension_le_zero_of_isolated
        (Eventually.of_forall fun x _ ↦ Subsingleton.elim x z)) Q hQ
      rw [h1] at h2
      have : d + 1 ≤ 0 := by exact_mod_cast h2
      omega
    rw [hB, closure_empty]
    exact anrem_locEq_of_eventually_not_mem (Eventually.of_forall fun _ h ↦ h)
  obtain ⟨R₁, hR₁, hball₁⟩ := Metric.isOpen_iff.1 hΩ a haΩ
  set R₀ := R₁ / 2
  have hR₀ : 0 < R₀ := by positivity
  have hcbΩ : ∀ ρ, ρ < R₁ → Metric.closedBall a ρ ⊆ Ω := fun ρ hρ ↦
    (Metric.closedBall_subset_ball hρ).trans hball₁
  have hbΩ : Metric.ball a R₀ ⊆ Ω :=
    (Metric.ball_subset_closedBall).trans (hcbΩ R₀ (by simp [R₀, hR₁]))
  set T₁ := T ∩ Metric.ball a R₀
  set B₁ := B ∩ Metric.ball a R₀
  have hballo : IsOpen (Metric.ball a R₀) := Metric.isOpen_ball
  have hlocInter : ∀ {S : Set (Fin (N + 1) → ℂ)} {y : Fin (N + 1) → ℂ}, anrem_LocEq S y →
      y ∈ Metric.ball a R₀ → anrem_LocEq (S ∩ Metric.ball a R₀) y := by
    intro S y hS hy
    obtain ⟨U, hU, hyU, m, f, hf, hUS⟩ := hS
    exact anrem_locEq_open hU hf hUS hballo ⟨hyU, hy⟩
  have hT₁loc : ∀ y ∈ T₁, anrem_LocEq T₁ y := fun y hy ↦ hlocInter (hTloc y (hbΩ hy.2)) hy.2
  have hB₁loc : ∀ y ∈ B₁, anrem_LocEq B₁ y := fun y hy ↦
    hlocInter (hBloc y (hBsub hy.1)) hy.2
  have hdimT₁ : ∀ y ∈ T₁, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) T₁ y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) ≤ (d : WithBot ℕ∞) := by
    intro y hy Q hQ
    rw [anrem_germ_inter_nhds T _ y (hballo.mem_nhds hy.2)] at hQ
    exact (anrem_dimension_le_iff T y _).1 (hTdim y ⟨hy.1, hbΩ hy.2⟩) Q hQ
  have hpure₁ : ∀ y ∈ B₁, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) B₁ y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    intro y hy Q hQ
    rw [anrem_germ_inter_nhds B _ y (hballo.mem_nhds hy.2)] at hQ
    exact hpure y hy.1 Q hQ
  have haT₁ : a ∈ T₁ := ⟨haT, Metric.mem_ball_self hR₀⟩
  -- a countable dense part of the pure set
  obtain ⟨s', hsc, hsd⟩ := TopologicalSpace.exists_countable_dense B₁
  set DB : Set (Fin (N + 1) → ℂ) := Subtype.val '' s'
  have hDB : DB ⊆ B₁ := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hDBd : B₁ ⊆ closure DB := by
    intro y hy
    have h1 : (⟨y, hy⟩ : B₁) ∈ closure s' := hsd.closure_eq ▸ mem_univ _
    exact mem_closure_image continuous_subtype_val.continuousAt h1
  obtain ⟨ξ, hξT, hξB, hξD⟩ := anr_choose_projection N d T₁ B₁ hT₁loc hdimT₁ hB₁loc
    (fun y hy Q hQ ↦ (hpure₁ y hy Q hQ).le) a haT₁ DB (hsc.image _) hDB
  -- closedness inside the ball
  have hclB₁ : ∀ z ∈ closure B₁, ‖z - a‖ < R₀ → z ∈ B₁ ∪ T₁ := by
    intro z hz hzR
    have hzb : z ∈ Metric.ball a R₀ := by rw [Metric.mem_ball, dist_eq_norm]; exact hzR
    by_cases hzT : z ∈ T
    · exact Or.inr ⟨hzT, hzb⟩
    · refine Or.inl ⟨?_, hzb⟩
      by_contra hzB
      have hev := anrem_eventually_not_mem (hBloc z ⟨hbΩ hzb, hzT⟩) hzB
      exact (mem_closure_iff_frequently.1 (closure_mono inter_subset_left hz) |>.and_eventually
        hev).exists.elim fun w hw ↦ hw.2 hw.1
  have hKc : ∀ ρ, ρ < R₀ → IsClosed ((closure B₁ ∪ T₁) ∩ Metric.closedBall a ρ) := by
    intro ρ hρ
    have hcb : Metric.closedBall a ρ ⊆ Metric.ball a R₀ := Metric.closedBall_subset_ball hρ
    have hT : T₁ ∩ Metric.closedBall a ρ = T ∩ Metric.closedBall a ρ := by
      ext z; exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hcb h.2⟩, h.2⟩⟩
    rw [union_inter_distrib_right, hT]
    exact (isClosed_closure.inter Metric.isClosed_closedBall).union
      (anrem_isClosed_inter_of_locEq hTloc Metric.isClosed_closedBall (hcb.trans hbΩ))
  obtain ⟨R, hR, hRR₀, r, hr, hsph⟩ := anrem_choose_radii' T₁ B₁ hR₀ hKc hclB₁ ξ hξT hξB
  have hTc : IsClosed (T₁ ∩ Metric.closedBall a R) := by
    have hcb : Metric.closedBall a R ⊆ Metric.ball a R₀ := Metric.closedBall_subset_ball hRR₀
    have hT : T₁ ∩ Metric.closedBall a R = T ∩ Metric.closedBall a R := by
      ext z; exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hcb h.2⟩, h.2⟩⟩
    rw [hT]
    exact anrem_isClosed_inter_of_locEq hTloc Metric.isClosed_closedBall (hcb.trans hbΩ)
  obtain ⟨m, f, hf, hfeq⟩ := anrem_box_equations' N d T₁ B₁ hTc (hKc R hRR₀) hT₁loc hdimT₁
    hB₁loc hpure₁ (fun z hz hzR ↦ hclB₁ z hz (hzR.trans hRR₀)) ξ r hR hr hsph DB hDB hDBd hξD
  set Box := {z : Fin (N + 1) → ℂ | ‖ξ z - ξ a‖ < r ∧ ‖z - a‖ < R}
  have hBoxo : IsOpen Box :=
    (isOpen_lt (ξ.continuous.sub continuous_const).norm continuous_const).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
  have haBox : a ∈ Box := ⟨by simp [hr], by simp [hR]⟩
  have hloc₁ : anrem_LocEq (closure B₁) a := ⟨Box, hBoxo, haBox, m, f, hf, hfeq⟩
  refine anrem_locEq_congr hballo (Metric.mem_ball_self hR₀) ?_ hloc₁
  ext z
  constructor
  · rintro ⟨hz, hzb⟩; exact ⟨closure_mono inter_subset_left hz, hzb⟩
  · rintro ⟨hz, hzb⟩
    exact ⟨anr_mem_closure_inter_open hz hballo hzb, hzb⟩

end HodgeLean.Foundations.Analytic

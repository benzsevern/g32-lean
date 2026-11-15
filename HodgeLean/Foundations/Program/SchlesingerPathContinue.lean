import HodgeLean.Foundations.Program.SchlesingerPathMixed
import HodgeLean.Foundations.Program.SchlesingerPathGauge

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65p_linear_unique_center (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (S : ℂ → E →L[ℂ] E) (c : ℂ) (σ : ℝ) (hσ : 0 < σ)
    (hS : AnalyticOnNhd ℂ S (ball c σ)) (y w : ℂ → E →L[ℂ] E) (h0 : y c = w c)
    (hy : ∀ z ∈ ball c σ, HasDerivAt y (S z * y z) z)
    (hw : ∀ z ∈ ball c σ, HasDerivAt w (S z * w z) z) :
    EqOn y w (ball c σ) := by
  let F : ℂ × (E →L[ℂ] E) → E →L[ℂ] E := fun q ↦ S (q.1 + c) * q.2
  have hF : AnalyticAt ℂ F (0, y c) :=
    ((hS c (mem_ball_self hσ)).comp_of_eq (analyticAt_fst.add analyticAt_const)
      (by simp)).mul analyticAt_snd
  have hmem (u : ℂ) (hu : u ∈ ball (0 : ℂ) σ) : u + c ∈ ball c σ := by
    simpa [mem_ball, dist_eq_norm] using hu
  have he := b65p_ode_unique (E →L[ℂ] E) F (y c) hF σ hσ
    (fun u ↦ y (u + c)) (fun u ↦ w (u + c)) (by simp) (by simp [h0])
    (fun u hu ↦ (hy (u + c) (hmem u hu)).comp_add_const u c)
    (fun u hu ↦ (hw (u + c) (hmem u hu)).comp_add_const u c)
  intro z hz
  have hz' : z - c ∈ ball (0 : ℂ) σ := by
    simpa [mem_ball, dist_eq_norm] using hz
  simpa using he hz'

theorem b65p_parameter_linear_system (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (S : ℂ × ℂ → E →L[ℂ] E) (V : Set ℂ) (hV : IsOpen V)
    (R : ℝ) (hR : 0 < R) (hS : AnalyticOnNhd ℂ S (V ×ˢ ball 0 R)) :
    ∃ Y : ℂ × ℂ → E →L[ℂ] E, AnalyticOnNhd ℂ Y (V ×ˢ ball 0 R) ∧
      (∀ p ∈ V, Y (p, 0) = 1) ∧
      (∀ p ∈ V, ∀ z ∈ ball (0 : ℂ) R,
        HasDerivAt (fun w ↦ Y (p, w)) (S (p, z) * Y (p, z)) z) ∧
      ∀ p ∈ V, ∀ z ∈ ball (0 : ℂ) R, IsUnit (Y (p, z)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hslice : ∀ p ∈ V, AnalyticOnNhd ℂ (fun z ↦ S (p, z)) (ball 0 R) := fun p hp z hz ↦
    (hS (p, z) ⟨hp, hz⟩).comp (analyticAt_const.prod analyticAt_id)
  have hsol : ∀ p, ∃ y : ℂ → E →L[ℂ] E, p ∈ V → (y 0 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) R, HasDerivAt y (S (p, z) * y z) z) ∧
      ∀ z ∈ ball (0 : ℂ) R, IsUnit (y z)) := by
    intro p
    by_cases hp : p ∈ V
    · obtain ⟨y, _, h0, hd, hb⟩ :=
        b65_linear_system E (fun z ↦ S (p, z)) 0 R hR (hslice p hp)
      exact ⟨y, fun _ ↦ ⟨h0, hd,
        fun z hz ↦ ContinuousLinearMap.isUnit_iff_bijective.mpr (hb z hz)⟩⟩
    · exact ⟨0, fun h ↦ (hp h).elim⟩
  choose y hy using hsol
  let Y : ℂ × ℂ → E →L[ℂ] E := fun q ↦ y q.1 q.2
  have hkey : ∀ p₀ ∈ V, ∀ z ∈ ball (0 : ℂ) R, AnalyticAt ℂ Y (p₀, z) := by
    intro p₀ hp₀
    obtain ⟨ρV, hρV, hV'⟩ := Metric.isOpen_iff.mp hV p₀ hp₀
    have hloc : ∀ z₁ ∈ ball (0 : ℂ) R, ∃ ρ σ : ℝ, 0 < ρ ∧ 0 < σ ∧
        ∃ Z : ℂ × ℂ → E →L[ℂ] E, AnalyticOnNhd ℂ Z (ball p₀ ρ ×ˢ ball z₁ σ) ∧
          ∀ p ∈ ball p₀ ρ, p ∈ V ∧ ∀ z ∈ ball z₁ σ,
            y p z = Z (p, z) * y p z₁ ∧ IsUnit (Z (p, z)) := by
      intro z₁ hz₁
      obtain ⟨ρ, σ, hρ, hσ, Z, hZa, hZ⟩ :=
        b65p_local_joint_gauge E ℂ S p₀ z₁ (hS _ ⟨hp₀, hz₁⟩)
      have hz₁' : ‖z₁‖ < R := by simpa using hz₁
      let ρ' := min ρ ρV
      let σ' := min σ (R - ‖z₁‖)
      have hρ' : 0 < ρ' := lt_min hρ hρV
      have hσ' : 0 < σ' := lt_min hσ (by linarith)
      have hsubσ : ball z₁ σ' ⊆ ball z₁ σ := ball_subset_ball (min_le_left _ _)
      have hsubR : ball z₁ σ' ⊆ ball 0 R := by
        intro z hz
        have h1 : dist z z₁ < R - ‖z₁‖ := lt_of_lt_of_le hz (min_le_right _ _)
        rw [mem_ball, dist_zero_right]
        calc ‖z‖ ≤ dist z z₁ + ‖z₁‖ := by
              simpa [dist_eq_norm] using norm_le_norm_sub_add z z₁
          _ < R := by linarith
      refine ⟨ρ', σ', hρ', hσ', Z, hZa.mono (prod_mono
        (ball_subset_ball (min_le_left _ _)) hsubσ), fun p hp ↦ ?_⟩
      have hpρ : p ∈ ball p₀ ρ := ball_subset_ball (min_le_left _ _) hp
      have hpV : p ∈ V := hV' (ball_subset_ball (min_le_right _ _) hp)
      obtain ⟨_, hyd, hyu⟩ := hy p hpV
      have hrel : EqOn (y p) (fun z ↦ Z (p, z) * y p z₁) (ball z₁ σ') :=
        b65p_linear_unique_center E (fun z ↦ S (p, z)) z₁ σ' hσ'
          ((hslice p hpV).mono hsubR) (y p) (fun z ↦ Z (p, z) * y p z₁)
          (by simp [(hZ p hpρ).1])
          (fun z hz ↦ hyd z (hsubR hz))
          (fun z hz ↦ by
            simpa only [mul_assoc] using
              ((hZ p hpρ).2 z (hsubσ hz)).mul_const (y p z₁))
      refine ⟨hpV, fun z hz ↦ ⟨hrel hz, ?_⟩⟩
      obtain ⟨u, hu⟩ := hyu z₁ hz₁
      have h := hyu z (hsubR hz)
      rw [hrel hz, ← hu] at h
      exact (Units.isUnit_mul_units _ u).mp h
    let Ω := {z : ℂ | AnalyticAt ℂ Y (p₀, z)}
    have hΩo : IsOpen Ω :=
      (isOpen_analyticAt ℂ Y).preimage (continuous_const.prodMk continuous_id)
    have h0 : (0 : ℂ) ∈ Ω := by
      obtain ⟨ρ, σ, hρ, hσ, Z, hZa, hZ⟩ := hloc 0 (mem_ball_self hR)
      apply (hZa (p₀, 0) ⟨mem_ball_self hρ, mem_ball_self hσ⟩).congr
      filter_upwards [prod_mem_nhds (ball_mem_nhds p₀ hρ) (ball_mem_nhds (0 : ℂ) hσ)]
        with q hq
      obtain ⟨hqV, hrel⟩ := hZ q.1 hq.1
      simp only [Y, (hrel q.2 hq.2).1, (hy q.1 hqV).1, mul_one]
    have hclosed : closure Ω ∩ ball (0 : ℂ) R ⊆ Ω := by
      rintro z₁ ⟨hcl, hz₁⟩
      obtain ⟨ρ, σ, hρ, hσ, Z, hZa, hZ⟩ := hloc z₁ hz₁
      obtain ⟨z₂, hz₂Ω, hd⟩ := Metric.mem_closure_iff.mp hcl σ hσ
      have hz₂ : z₂ ∈ ball z₁ σ := by rw [mem_ball, dist_comm]; exact hd
      obtain ⟨u, hu⟩ := ((hZ p₀ (mem_ball_self hρ)).2 z₂ hz₂).2
      have hinv : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ Ring.inverse (Z (q.1, z₂))) (p₀, z₁) :=
        (analyticAt_inverse (𝕜 := ℂ) u).comp_of_eq
          ((hZa (p₀, z₂) ⟨mem_ball_self hρ, hz₂⟩).comp_of_eq
            (analyticAt_fst.prod analyticAt_const) rfl) (by simp [hu])
      have hY₂ : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ Y (q.1, z₂)) (p₀, z₁) :=
        (show AnalyticAt ℂ Y (p₀, z₂) from hz₂Ω).comp_of_eq
          (analyticAt_fst.prod analyticAt_const) rfl
      apply (((hZa (p₀, z₁) ⟨mem_ball_self hρ, mem_ball_self hσ⟩).mul hinv).mul hY₂).congr
      filter_upwards [prod_mem_nhds (ball_mem_nhds p₀ hρ) (ball_mem_nhds z₁ hσ)]
        with q hq
      obtain ⟨_, hrel⟩ := hZ q.1 hq.1
      have h2 := hrel z₂ hz₂
      simp only [Y, Pi.mul_apply, (hrel q.2 hq.2).1, h2.1, mul_assoc,
        Ring.inverse_mul_cancel_left _ _ h2.2]
    intro z hz
    exact (convex_ball (0 : ℂ) R).isPreconnected.subset_of_closure_inter_subset hΩo
      ⟨0, mem_ball_self hR, h0⟩ hclosed hz
  refine ⟨Y, fun q hq ↦ hkey q.1 hq.1 q.2 hq.2, fun p hp ↦ (hy p hp).1,
    fun p hp ↦ (hy p hp).2.1, fun p hp ↦ (hy p hp).2.2⟩

theorem b65p_coefficient_analyticOn (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (t : ι → ℂ) (A : ι → E →L[ℂ] E) (U : Set ℂ)
    (hU : ∀ s ∈ U, ∀ q, s ≠ t q) :
    AnalyticOnNhd ℂ (b65p_coefficient E t A) U := by
  intro s hs
  unfold b65p_coefficient
  apply Finset.analyticAt_fun_sum
  intro q _
  exact ((analyticAt_id.sub analyticAt_const).inv
    (sub_ne_zero.mpr (hU s hs q))).smul analyticAt_const

theorem b65p_schlesinger_spatial_gauge (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 0 < r) (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E) (U : Set ℂ)
    (hUo : IsOpen U)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) (ball 0 r))
    (hinj : ∀ θ ∈ ball (0 : ℂ) r, Function.Injective (t θ))
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ p, HasDerivAt (fun θ ↦ A θ p)
      (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (A θ) p) θ)
    (hU : ∀ s ∈ U, ∀ z ∈ ball (0 : ℂ) r, ∀ q, s ≠ t z q)
    (Y : ℂ × ℂ → E →L[ℂ] E) (hYa : AnalyticOnNhd ℂ Y (U ×ˢ ball 0 r))
    (hY0 : ∀ s ∈ U, Y (s, 0) = 1)
    (hYd : ∀ s ∈ U, ∀ z ∈ ball (0 : ℂ) r, HasDerivAt (fun w ↦ Y (s, w))
      (b65p_verticalCoefficient E (t z) (fun q ↦ deriv (fun w ↦ t w q) z) (A z) s *
        Y (s, z)) z) :
    ∀ s ∈ U, ∀ θ ∈ ball (0 : ℂ) r, HasDerivAt (fun s ↦ Y (s, θ))
      (b65p_coefficient E (t θ) (A θ) s * Y (s, θ) -
        Y (s, θ) * b65p_coefficient E (t 0) (A 0) s) s := by
  have hAa (q : ι) : AnalyticOnNhd ℂ (fun z ↦ A z q) (ball (0 : ℂ) r) :=
    (show DifferentiableOn ℂ (fun z ↦ A z q) (ball (0 : ℂ) r) from
      fun z hz ↦ (hA z hz q).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  let S : ℂ × ℂ → E →L[ℂ] E := fun w ↦ b65p_verticalCoefficient E (t w.2)
    (fun q ↦ deriv (fun z ↦ t z q) w.2) (A w.2) w.1
  have hS : AnalyticOnNhd ℂ S (U ×ˢ ball 0 r) := by
    intro w hw
    exact b65p_verticalCoefficient_joint_analyticAt E t A w.1 w.2
      (fun q ↦ ht q w.2 hw.2) (fun q ↦ hAa q w.2 hw.2) (hU w.1 hw.1 w.2 hw.2)
  let H : ℂ × ℂ → E →L[ℂ] E := fun w ↦ b65p_coefficient E (t w.2) (A w.2) w.1
  let D : ℂ × ℂ → E →L[ℂ] E := fun w ↦ deriv (b65p_verticalCoefficient E (t w.2)
    (fun q ↦ deriv (fun z ↦ t z q) w.2) (A w.2)) w.1
  exact b65p_joint_flat_gauge E S H D Y U hUo r hr hYa hY0
    (fun p hp z hz ↦ (hS (p, z) ⟨hp, hz⟩).comp (analyticAt_const.prod analyticAt_id))
    hYd
    (by
      intro p hp z hz
      have htz : ∀ q, HasDerivAt (fun w ↦ t w q) (deriv (fun w ↦ t w q) z) z :=
        fun q ↦ (ht q z hz).differentiableAt.hasDerivAt
      have hd := (b65p_coefficient_parameter_hasDerivAt E t A
        (fun q ↦ deriv (fun w ↦ t w q) z)
        (b65p_schlesingerField E (fun q ↦ deriv (fun w ↦ t w q) z) (t z) (A z))
        z p htz (hA z hz) (hU p hp z hz))
      have hfl := b65p_schlesinger_flatness E t A (fun q ↦ deriv (fun w ↦ t w q) z) z p
        htz (hA z hz) (hinj z hz) (hU p hp z hz)
      apply hd.congr_deriv
      rw [← hd.deriv]
      dsimp only [D, S, H]
      rw [add_sub_assoc, ← hfl]
      abel)
    (by
      intro p hp z hz
      exact (b65p_verticalCoefficient_spatial_hasDerivAt E (t z)
        (fun q ↦ deriv (fun w ↦ t w q) z) (A z) p
        (hU p hp z hz)).differentiableAt.hasDerivAt)

theorem b65p_schlesinger_common_conjugator (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) (ball 0 r))
    (hinj : ∀ θ ∈ ball (0 : ℂ) r, Function.Injective (t θ))
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ p, HasDerivAt (fun θ ↦ A θ p)
      (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (A θ) p) θ) :
    ∀ x : ℂ, ∀ θ ∈ ball (0 : ℂ) r, ∃ G : (E →L[ℂ] E)ˣ, ∀ γ : Path x x,
      (∀ θ' ∈ ball (0 : ℂ) r, ∀ s q, γ s ≠ t θ' q) →
      b65f_transport E (b65p_coefficient E (t θ) (A θ)) (fun u ↦ γ.extend u) =
        G.val * b65f_transport E (b65p_coefficient E (t 0) (A 0)) (fun u ↦ γ.extend u) *
          (G⁻¹).val := by
  intro x θ hθ
  have hθr : ‖θ‖ < r := by simpa using hθ
  let r' := (‖θ‖ + r) / 2
  have hθr' : ‖θ‖ < r' := by dsimp [r']; linarith
  have hr'r : r' < r := by dsimp [r']; linarith
  have hr' : 0 < r' := lt_of_le_of_lt (norm_nonneg θ) hθr'
  have hθ' : θ ∈ ball (0 : ℂ) r' := by simpa using hθr'
  have hcb : closedBall (0 : ℂ) r' ⊆ ball 0 r := closedBall_subset_ball hr'r
  have hbb : ball (0 : ℂ) r' ⊆ ball 0 r := ball_subset_ball hr'r.le
  have hAa (q : ι) : AnalyticOnNhd ℂ (fun z ↦ A z q) (ball (0 : ℂ) r) :=
    (show DifferentiableOn ℂ (fun z ↦ A z q) (ball (0 : ℂ) r) from
      fun z hz ↦ (hA z hz q).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  let K : Set ℂ := ⋃ q, (fun z ↦ t z q) '' closedBall 0 r'
  have hK : IsCompact K := isCompact_iUnion (fun q ↦
    (isCompact_closedBall (0 : ℂ) r').image_of_continuousOn ((ht q).continuousOn.mono hcb))
  let U : Set ℂ := Kᶜ
  have hUo : IsOpen U := hK.isClosed.isOpen_compl
  have hU : ∀ s ∈ U, ∀ z ∈ closedBall (0 : ℂ) r', ∀ q, s ≠ t z q := by
    intro s hs z hz q heq
    exact hs (mem_iUnion.mpr ⟨q, z, hz, heq.symm⟩)
  have hγU : ∀ γ : Path x x, (∀ θ' ∈ ball (0 : ℂ) r, ∀ s q, γ s ≠ t θ' q) →
      ∀ s, γ s ∈ U := by
    intro γ hγ s hs
    obtain ⟨q, z, hz, heq⟩ := mem_iUnion.mp hs
    exact hγ z (hcb hz) s q heq.symm
  by_cases hx : x ∈ U
  swap
  · refine ⟨1, fun γ hγ ↦ ?_⟩
    exact (hx (by simpa using hγU γ hγ 0)).elim
  have hpole : ∀ p ∈ U, ∀ z ∈ ball (0 : ℂ) r', ∀ q, p ≠ t z q :=
    fun p hp z hz ↦ hU p hp z (ball_subset_closedBall hz)
  let S : ℂ × ℂ → E →L[ℂ] E := fun w ↦ b65p_verticalCoefficient E (t w.2)
    (fun q ↦ deriv (fun z ↦ t z q) w.2) (A w.2) w.1
  have hS : AnalyticOnNhd ℂ S (U ×ˢ ball 0 r') := by
    intro w hw
    exact b65p_verticalCoefficient_joint_analyticAt E t A w.1 w.2
      (fun q ↦ ht q w.2 (hbb hw.2)) (fun q ↦ hAa q w.2 (hbb hw.2))
      (hpole w.1 hw.1 w.2 hw.2)
  obtain ⟨Y, hYa, hY0, hYd, hYu⟩ := b65p_parameter_linear_system E S U hUo r' hr' hS
  have hflat := b65p_schlesinger_spatial_gauge E r' hr' t A U hUo
    (fun q ↦ (ht q).mono hbb) (fun z hz ↦ hinj z (hbb hz)) (fun z hz ↦ hA z (hbb hz))
    hpole Y hYa hY0 hYd
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) r' := mem_ball_self hr'
  obtain ⟨g, hg⟩ := b65p_loop_transport_gauge E (b65p_coefficient E (t 0) (A 0))
    (b65p_coefficient E (t θ) (A θ)) (fun s ↦ Y (s, θ)) U hUo
    (b65p_coefficient_analyticOn E (t 0) (A 0) U (fun s hs ↦ hpole s hs 0 hzero))
    (b65p_coefficient_analyticOn E (t θ) (A θ) U (fun s hs ↦ hpole s hs θ hθ'))
    (fun s hs ↦ hflat s hs θ hθ') x (hYu x hx θ hθ')
  exact ⟨g, fun γ hγ ↦ hg γ (hγU γ hγ)⟩

end HodgeLean.Foundations.Program

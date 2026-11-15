import HodgeLean.Foundations.Program.FuchsianSystemDefs
import HodgeLean.Foundations.Program.FuchsianSystemCircle
import HodgeLean.Foundations.Program.FuchsianSystemSmoothTransport
import HodgeLean.Foundations.Program.FuchsianSystemUnits
import HodgeLean.Foundations.Program.FuchsianSystemPolygon
import HodgeLean.Foundations.Program.FuchsianSystemConvergence
import HodgeLean.Foundations.Program.FuchsianSystemComposition
import HodgeLean.Foundations.Program.FuchsianSystemHomotopy

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65f_local_normal_form_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (R : E →L[ℂ] E) (B : ℂ → E →L[ℂ] E) (a : ℂ) (d : ℝ)
    (hd : 0 < d) (hB : AnalyticOnNhd ℂ B (ball a d))
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R * T - T * R))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ d ∧ ∃ H : ℂ → E →L[ℂ] E,
      AnalyticOnNhd ℂ H (ball a r) ∧ H a = 1 ∧
      (∀ z ∈ ball a r, IsUnit (H z)) ∧
      (∀ z ∈ ball a r, (z - a) • deriv H z =
        R * H z - H z * R + (z - a) • (B z * H z)) ∧
      (∀ z ∈ ball a r, z - a ∈ Complex.slitPlane →
        HasDerivAt (fun w ↦ H w * NormedSpace.exp (Complex.log (w - a) • R))
          (((z - a)⁻¹ • R + B z) *
            (H z * NormedSpace.exp (Complex.log (z - a) • R))) z) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < r →
        let Q := fun t : ℝ ↦ H (b65f_circle a ρ t) *
          NormedSpace.exp ((Complex.log (ρ : ℂ) +
            2 * Real.pi * Complex.I * (t : ℂ)) • R)
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt Q
          ((2 * Real.pi * Complex.I * (b65f_circle a ρ t - a)) •
            (((b65f_circle a ρ t - a)⁻¹ • R + B (b65f_circle a ρ t)) * Q t)) t) ∧
        Q 1 = Q 0 * NormedSpace.exp ((2 * Real.pi * Complex.I) • R) ∧
        b65f_transport E (fun z ↦ (z - a)⁻¹ • R + B z) (b65f_circle a ρ) * Q 0 = Q 1 := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨r, hr, hrd, H, hH, hH0, hu, hg⟩ := b65f_exists_analytic_gauge R B a d hd hB hnr
  refine ⟨r, hr, hrd, H, hH, hH0, hu, hg, ?_, ?_⟩
  · intro z hz hslit
    exact b65f_slit_solution_hasDerivAt R B H a z (hH z hz).differentiableAt hslit (hg z hz)
  · intro ρ hρ hρr
    let Q := fun t : ℝ ↦ H (b65f_circle a ρ t) *
      NormedSpace.exp ((Complex.log (ρ : ℂ) + 2 * Real.pi * Complex.I * (t : ℂ)) • R)
    have hcircle (t : ℝ) : b65f_circle a ρ t ∈ ball a r := by
      rw [mem_ball_iff_norm, b65f_circle_norm, abs_of_pos hρ]
      exact hρr
    have hQ (t : ℝ) : HasDerivAt Q
        ((2 * Real.pi * Complex.I * (b65f_circle a ρ t - a)) •
          (((b65f_circle a ρ t - a)⁻¹ • R + B (b65f_circle a ρ t)) * Q t)) t :=
      b65f_lifted_circle_hasDerivAt R B H a ρ t hρ
        (hH _ (hcircle t)).differentiableAt (hg _ (hcircle t))
    refine ⟨fun t _ ↦ hQ t, b65f_lifted_circle_endpoint R H a ρ, ?_⟩
    let U : Set ℂ := ball a r \ {a}
    let A : ℂ → E →L[ℂ] E := fun z ↦ (z - a)⁻¹ • R + B z
    have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
    have hA : AnalyticOnNhd ℂ A U := by
      intro z hz
      have hza : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hz.2)
      exact ((analyticAt_id.sub analyticAt_const).inv hza).smul analyticAt_const |>.add
        (hB z (ball_subset_ball hrd hz.1))
    have hc : Continuous (b65f_circle a ρ) := by
      unfold b65f_circle
      fun_prop
    have hm : MapsTo (b65f_circle a ρ) (Icc (0 : ℝ) 1) U := by
      intro t ht
      refine ⟨hcircle t, ?_⟩
      have hh : b65f_circle a ρ t - a ≠ 0 := by
        apply norm_pos_iff.mp
        rw [b65f_circle_norm, abs_of_pos hρ]
        exact hρ
      simpa only [mem_singleton_iff] using sub_ne_zero.mp hh
    exact b65f_smooth_transport_propagates hU hA (b65f_circle a ρ)
      (fun t ↦ 2 * Real.pi * Complex.I * (b65f_circle a ρ t - a)) Q hc.continuousOn
      (by fun_prop) hm (fun t _ ↦ b65f_circle_hasDerivAt a ρ t) (fun t _ ↦ hQ t)

theorem b65f_segment_solution_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (A : ℂ → E →L[ℂ] E) (a : ℂ) (r : ℝ)
    (hr : 0 < r) (hA : AnalyticOnNhd ℂ A (ball a r)) :
    AnalyticOnNhd ℂ (b65f_segment E A a) (ball a r) ∧
      b65f_segment E A a a = 1 ∧
      (∀ z ∈ ball a r, Summable (fun m ↦ b65f_iterated E A a z m 1)) ∧
      (∀ z ∈ ball a r, HasDerivAt (b65f_segment E A a)
        (A z * b65f_segment E A a z) z) ∧
      ∀ z ∈ ball a r, IsUnit (b65f_segment E A a z) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hd := fun z hz ↦ b65f_segment_hasDerivAt hA (x := z) hz
  refine ⟨?_, b65f_segment_initial E A a,
    fun z hz ↦ b65f_iterated_summable_on_disc E A a r hr hA z hz, hd, ?_⟩
  · exact (show DifferentiableOn ℂ (b65f_segment E A a) (ball a r) from
      fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  · intro z hz
    exact b65f_regular_solution_isUnit hr hA hd (b65f_segment_initial E A a) hz

theorem b65f_path_convergence_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U : Set ℂ) (hU : IsOpen U) (A : ℂ → E →L[ℂ] E)
    (hA : AnalyticOnNhd ℂ A U) (x y : U) (γ : Path x y) :
    Tendsto (b65f_polygon E A (fun t ↦ (γ.extend t).val)) atTop
      (𝓝 (b65f_transport E A (fun t ↦ (γ.extend t).val))) ∧
      IsUnit (b65f_transport E A (fun t ↦ (γ.extend t).val)) := by
  obtain ⟨N, hN, hs⟩ := b65f_polygon_stabilizes hU hA (fun t ↦ (γ.extend t).val)
    ((continuous_subtype_val.comp γ.continuous_extend).continuousOn)
    (fun t _ ↦ (γ.extend t).property)
  have he : (b65f_polygon E A (fun t ↦ (γ.extend t).val)) =ᶠ[atTop]
      (fun _ ↦ b65f_polygon E A (fun t ↦ (γ.extend t).val) N) :=
    eventually_atTop.mpr ⟨N, hs⟩
  have ht := tendsto_const_nhds.congr' he.symm
  have hl := ht.limUnder_eq
  unfold b65f_transport
  rw [hl]
  exact ⟨ht, hN⟩

theorem b65f_disc_transport_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (A : ℂ → E →L[ℂ] E) (a : ℂ) (r : ℝ)
    (hr : 0 < r) (hA : AnalyticOnNhd ℂ A (ball a r))
    (y : ball a r) (γ : Path (⟨a, mem_ball_self hr⟩ : ball a r) y) :
    b65f_transport E A (fun t ↦ (γ.extend t).val) = b65f_segment E A a y.val := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hp := b65f_polygon_eventually_propagates isOpen_ball hA
    (fun z hz ↦ b65f_segment_hasDerivAt hA hz)
    (fun t ↦ (γ.extend t).val)
    ((continuous_subtype_val.comp γ.continuous_extend).continuousOn)
    (fun t _ ↦ (γ.extend t).property)
  have he : ∀ᶠ N in atTop,
      b65f_polygon E A (fun t ↦ (γ.extend t).val) N = b65f_segment E A a y.val := by
    filter_upwards [hp] with N hN
    simpa only [Path.extend_zero, Path.extend_one, b65f_segment_initial, mul_one] using hN
  exact (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)).limUnder_eq

theorem b65f_path_composition_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U : Set ℂ) (hU : IsOpen U) (A : ℂ → E →L[ℂ] E)
    (hA : AnalyticOnNhd ℂ A U) (x y z : U) (γ : Path x y) (δ : Path y z) :
    b65f_transport E A (fun t ↦ ((γ.trans δ).extend t).val) =
      b65f_transport E A (fun t ↦ (δ.extend t).val) *
        b65f_transport E A (fun t ↦ (γ.extend t).val) := by
  have hγ := (b65f_path_convergence_aux E U hU A hA x y γ).1
  have hδ := (b65f_path_convergence_aux E U hU A hA y z δ).1
  have ht := (b65f_path_convergence_aux E U hU A hA x z (γ.trans δ)).1.comp
    (tendsto_add_atTop_nat 1)
  have he : (fun N ↦ b65f_polygon E A (fun t ↦ ((γ.trans δ).extend t).val) (N + 1)) =
      (fun N ↦ b65f_polygon E A (fun t ↦ (δ.extend t).val) N *
        b65f_polygon E A (fun t ↦ (γ.extend t).val) N) :=
    funext (b65f_polygon_trans A γ δ)
  change Tendsto (fun N ↦ b65f_polygon E A (fun t ↦ ((γ.trans δ).extend t).val) (N + 1))
    atTop _ at ht
  rw [he] at ht
  exact tendsto_nhds_unique ht (hδ.mul hγ)

theorem b65f_homotopy_invariance_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U : Set ℂ) (hU : IsOpen U) (A : ℂ → E →L[ℂ] E)
    (hA : AnalyticOnNhd ℂ A U) (x y : U) (γ δ : Path x y)
    (h : γ.Homotopic δ) :
    b65f_transport E A (fun t ↦ (γ.extend t).val) =
      b65f_transport E A (fun t ↦ (δ.extend t).val) := by
  obtain ⟨F⟩ := h
  exact b65f_homotopy_transport hU hA F

theorem b65f_monodromy_representation_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (s : Finset ℂ) (R : ℂ → E →L[ℂ] E) (x : {z : ℂ // z ∉ s}) :
    ∃ M : FundamentalGroup {z : ℂ // z ∉ s} x →* (E →L[ℂ] E)ˣ,
      ∀ γ : Path x x,
        (M (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) : E →L[ℂ] E) =
          b65f_transport E (b65f_coefficient E s R) (fun t ↦ (γ.extend t).val) := by
  classical
  let U : Set ℂ := {z | z ∉ s}
  let A := b65f_coefficient E s R
  have hU : IsOpen U := s.isClosed.isOpen_compl
  have hA : AnalyticOnNhd ℂ A U := by
    intro z hz
    apply s.analyticAt_fun_sum
    intro a ha
    exact ((analyticAt_id.sub analyticAt_const).inv
      (sub_ne_zero.mpr (by
        intro h
        have h' : z = a := h
        apply hz
        rw [h']
        exact ha))).smul analyticAt_const
  let t : Path x x → (E →L[ℂ] E)ˣ := fun γ ↦
    (b65f_path_convergence_aux E U hU A hA x x γ).2.unit
  have ht (γ : Path x x) : (t γ : E →L[ℂ] E) =
      b65f_transport E A (fun q ↦ (γ.extend q).val) := IsUnit.unit_spec _
  let q : Path.Homotopic.Quotient x x → (E →L[ℂ] E)ˣ := Quotient.lift t (by
    intro γ δ h
    apply Units.ext
    exact (ht γ).trans ((b65f_homotopy_invariance_aux E U hU A hA x x γ δ h).trans (ht δ).symm))
  have hq (γ : Path x x) : q (Path.Homotopic.Quotient.mk γ) = t γ := rfl
  have hconst : b65f_transport E A (fun _ ↦ x.val) = 1 := by
    have hp : b65f_polygon E A (fun _ ↦ x.val) = fun _ ↦ 1 := by
      funext N
      simp [b65f_polygon, b65f_segment_initial]
    unfold b65f_transport
    rw [hp]
    exact tendsto_const_nhds.limUnder_eq
  let M : FundamentalGroup U x →* (E →L[ℂ] E)ˣ := {
    toFun := fun p ↦ q p.toPath
    map_one' := by
      change q (Path.Homotopic.Quotient.mk (Path.refl x)) = 1
      rw [hq]
      apply Units.ext
      rw [ht]
      simpa only [Path.refl_extend, ContinuousMap.const_apply, Units.val_one] using hconst
    map_mul' := by
      intro p p'
      change q (p'.toPath.trans p.toPath) = q p.toPath * q p'.toPath
      induction p.toPath using Path.Homotopic.Quotient.ind with
      | mk γ =>
        induction p'.toPath using Path.Homotopic.Quotient.ind with
        | mk δ =>
          change t (δ.trans γ) = t γ * t δ
          apply Units.ext
          simp only [Units.val_mul, ht]
          exact b65f_path_composition_aux E U hU A hA x x x δ γ }
  refine ⟨M, ?_⟩
  intro γ
  exact ht γ

end HodgeLean.Foundations.Program

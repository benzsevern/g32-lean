import HodgeLean.Foundations.Program.CurveJacobianFormsPeriods

/-!
# Track B3 foundations (stage B3.4d): the period lattice is finitely generated

On a compact manifold, choose finitely many chart balls `b3Forms_cball E 1 x` covering it, with the
concentric balls of twice the radius inside the charts. For a family `A` of closed smooth
`1`-forms:
* on a chart ball, line integrals are differences of the primitive `b3Forms_ballPrim` at the
  centre (`b3Forms_lineIntegral_eq_ballPrim`);
* the transition values `b3Forms_transVal A x y q` (differences of the primitives of two balls at
  a common point) are locally constant on the overlap, hence take finitely many values on the
  overlap of the closed balls (`b3Forms_transVal_finite`);
* subdividing a loop by a Lebesgue number, its period is a sum of transition values
  (`b3Forms_periods_mem_closure`): **the periods along loops lie in a finitely generated group.**

Applied to the real and imaginary parts of holomorphic forms on a compact Riemann surface this is
statement 5 of `CurveJacobian.lean` (`b3Forms_periodLattice_finite`). -/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem b3Forms_exists_chartRadius (x : M) :
    ∃ R > 0, Metric.ball (chartAt E x x) (2 * R) ⊆ (chartAt E x).target := by
  obtain ⟨r, hr, h⟩ := Metric.isOpen_iff.1 (chartAt E x).open_target _
    ((chartAt E x).map_source (mem_chart_source E x))
  exact ⟨r / 2, by positivity, by rwa [mul_div_cancel₀ _ two_ne_zero]⟩

variable (E) in
/-- A radius `R` at `x` with the chart ball of radius `2 R` inside the chart image.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, GTM 82, §8 (Čech–de Rham with finite
covers); Forster, *Lectures on Riemann Surfaces*, GTM 81, §21. -/
def b3Forms_rad (x : M) : ℝ := (b3Forms_exists_chartRadius (E := E) x).choose

theorem b3Forms_rad_pos (x : M) : 0 < b3Forms_rad E x :=
  (b3Forms_exists_chartRadius (E := E) x).choose_spec.1

theorem b3Forms_ball_rad_subset (x : M) :
    Metric.ball (chartAt E x x) (2 * b3Forms_rad E x) ⊆ (chartAt E x).target :=
  (b3Forms_exists_chartRadius (E := E) x).choose_spec.2

variable (E) in
/-- The chart ball of radius `c R` at `x`, as a subset of `M`.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, GTM 82, §8 (Čech–de Rham with finite
covers); Forster, *Lectures on Riemann Surfaces*, GTM 81, §21. -/
def b3Forms_cball (c : ℝ) (x : M) : Set M :=
  (chartAt E x).source ∩ chartAt E x ⁻¹' Metric.ball (chartAt E x x) (c * b3Forms_rad E x)

theorem b3Forms_isOpen_cball (c : ℝ) (x : M) : IsOpen (b3Forms_cball E c x) :=
  (chartAt E x).isOpen_inter_preimage Metric.isOpen_ball

theorem b3Forms_cball_mono {c c' : ℝ} (h : c ≤ c') (x : M) :
    b3Forms_cball E c x ⊆ b3Forms_cball E c' x := fun _ hq ↦
  ⟨hq.1, Metric.ball_subset_ball (mul_le_mul_of_nonneg_right h (b3Forms_rad_pos x).le) hq.2⟩

theorem b3Forms_mem_cball_self {c : ℝ} (hc : 0 < c) (x : M) : x ∈ b3Forms_cball E c x :=
  ⟨mem_chart_source E x, Metric.mem_ball_self (mul_pos hc (b3Forms_rad_pos x))⟩

variable (E) in
/-- The closed chart ball of radius `R` at `x`.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, GTM 82, §8 (Čech–de Rham with finite
covers); Forster, *Lectures on Riemann Surfaces*, GTM 81, §21. -/
def b3Forms_kball (x : M) : Set M :=
  (chartAt E x).symm '' Metric.closedBall (chartAt E x x) (b3Forms_rad E x)

theorem b3Forms_closedBall_subset (x : M) :
    Metric.closedBall (chartAt E x x) (b3Forms_rad E x) ⊆ (chartAt E x).target :=
  (Metric.closedBall_subset_ball (by linarith [b3Forms_rad_pos (E := E) x])).trans
    (b3Forms_ball_rad_subset x)

theorem b3Forms_isCompact_kball [ProperSpace E] (x : M) : IsCompact (b3Forms_kball E x) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((chartAt E x).continuousOn_symm.mono (b3Forms_closedBall_subset x))

theorem b3Forms_cball_one_subset_kball (x : M) : b3Forms_cball E 1 x ⊆ b3Forms_kball E x := by
  rintro q ⟨hq, hb⟩
  refine ⟨chartAt E x q, Metric.ball_subset_closedBall (by simpa using hb),
    (chartAt E x).left_inv hq⟩

theorem b3Forms_kball_subset_cball_two (x : M) : b3Forms_kball E x ⊆ b3Forms_cball E 2 x := by
  rintro _ ⟨u, hu, rfl⟩
  have hut := b3Forms_closedBall_subset x hu
  refine ⟨(chartAt E x).map_target hut, ?_⟩
  rw [mem_preimage, (chartAt E x).right_inv hut]
  exact Metric.closedBall_subset_ball (by linarith [b3Forms_rad_pos (E := E) x]) hu

/-- **The primitive at the centre of a chart ball**: `q ↦ ∫` along the chart segment from `x`.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, GTM 82, §8 (Čech–de Rham with finite
covers); Forster, *Lectures on Riemann Surfaces*, GTM 81, §21. -/
def b3Forms_ballPrim (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) (x q : M) : ℝ :=
  b3Forms_lineIntegral α (b3Forms_segPath x (chartAt E x x) (chartAt E x q)) 0 1

/-- **Line integrals inside a chart ball** through the primitive at the centre. -/
theorem b3Forms_lineIntegral_eq_ballPrim {α : M → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : b3Forms_IsSmooth α) (hdα : b3Forms_d α = 0) (x : M) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) {s t : ℝ}
    (hγB : ∀ τ ∈ uIcc s t, γ τ ∈ b3Forms_cball E 2 x) :
    b3Forms_lineIntegral α γ s t = b3Forms_ballPrim α x (γ t) - b3Forms_ballPrim α x (γ s) := by
  set U := Metric.ball (chartAt E x x) (2 * b3Forms_rad E x)
  obtain ⟨h, hh⟩ := b3Forms_exists_local_primitive hα hdα x (convex_ball _ _) Metric.isOpen_ball
    (b3Forms_ball_rad_subset x)
  have hc : chartAt E x x ∈ U := Metric.mem_ball_self (by linarith [b3Forms_rad_pos (E := E) x])
  have hseg : ∀ q ∈ b3Forms_cball E 2 x, b3Forms_ballPrim α x q = h (chartAt E x q) -
      h (chartAt E x x) := fun q hq ↦
    b3Forms_lineIntegral_segPath hα x (convex_ball _ _) (b3Forms_ball_rad_subset x) hh hc hq.2
  rw [b3Forms_lineIntegral_eq_of_primitive hα hh hγ fun τ hτ ↦ hγB τ hτ,
    hseg _ (hγB t right_mem_uIcc), hseg _ (hγB s left_mem_uIcc)]
  ring

section Family

variable {Θ : Type*} (A : Θ → M → E [⋀^Fin 1]→L[ℝ] ℝ)

/-- **The transition values** `q ↦ (θ ↦ P_x^θ(q) - P_y^θ(q))` of a family of forms between the
primitives at the centres of two chart balls.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, GTM 82, §8 (Čech–de Rham with finite
covers); Forster, *Lectures on Riemann Surfaces*, GTM 81, §21. -/
def b3Forms_transVal (x y q : M) : Θ → ℝ :=
  fun θ ↦ b3Forms_ballPrim (A θ) x q - b3Forms_ballPrim (A θ) y q

variable {A} (hA : ∀ θ, b3Forms_IsSmooth (A θ)) (hdA : ∀ θ, b3Forms_d (A θ) = 0)
include hA hdA

/-- The transition values are locally constant on the overlap. -/
theorem b3Forms_transVal_eventually {x y q : M}
    (hq : q ∈ b3Forms_cball E 2 x ∩ b3Forms_cball E 2 y) :
    ∀ᶠ q' in 𝓝 q, b3Forms_transVal A x y q' = b3Forms_transVal A x y q := by
  set N := b3Forms_cball E 2 x ∩ b3Forms_cball E 2 y
  have hN : IsOpen N := (b3Forms_isOpen_cball 2 x).inter (b3Forms_isOpen_cball 2 y)
  have hO : IsOpen ((chartAt E q).target ∩ (chartAt E q).symm ⁻¹' N) :=
    (chartAt E q).isOpen_inter_preimage_symm hN
  have hmem : chartAt E q q ∈ (chartAt E q).target ∩ (chartAt E q).symm ⁻¹' N :=
    ⟨(chartAt E q).map_source (mem_chart_source E q), by
      rw [mem_preimage, (chartAt E q).left_inv (mem_chart_source E q)]; exact hq⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO _ hmem
  have hbt : Metric.ball (chartAt E q q) r ⊆ (chartAt E q).target := fun u hu ↦ (hball hu).1
  filter_upwards [b3Forms_nhds_of_ball (E := E) q hr] with q' hq'
  funext θ
  have hδ := b3Forms_segPath_isTame q (convex_ball _ _) hbt (Metric.mem_ball_self hr) hq'.2
  have hin : ∀ τ, b3Forms_segPath q (chartAt E q q) (chartAt E q q') τ ∈ N := fun τ ↦
    (hball (b3Forms_segPath_mem (convex_ball _ _) (Metric.mem_ball_self hr) hq'.2 τ)).2
  have h0 : b3Forms_segPath q (chartAt E q q) (chartAt E q q') 0 = q := by
    rw [b3Forms_segPath_zero, (chartAt E q).left_inv (mem_chart_source E q)]
  have h1 : b3Forms_segPath q (chartAt E q q) (chartAt E q q') 1 = q' := by
    rw [b3Forms_segPath_one, (chartAt E q).left_inv hq'.1]
  have ex := b3Forms_lineIntegral_eq_ballPrim (hA θ) (hdA θ) x hδ.1 (s := 0) (t := 1)
    fun τ _ ↦ (hin τ).1
  have ey := b3Forms_lineIntegral_eq_ballPrim (hA θ) (hdA θ) y hδ.1 (s := 0) (t := 1)
    fun τ _ ↦ (hin τ).2
  rw [h0, h1] at ex ey
  simp only [b3Forms_transVal]
  linarith

/-- **Finitely many transition values** on the overlap of two closed chart balls. -/
theorem b3Forms_transVal_finite [ProperSpace E] [T2Space M] (x y : M) :
    ∃ T : Finset (Θ → ℝ), (∀ q ∈ b3Forms_kball E x ∩ b3Forms_kball E y,
      b3Forms_transVal A x y q ∈ T) ∧ ∀ s ∈ T, ∃ q ∈ b3Forms_kball E x ∩ b3Forms_kball E y,
        s = b3Forms_transVal A x y q := by
  classical
  have hK : IsCompact (b3Forms_kball E x ∩ b3Forms_kball E y) :=
    (b3Forms_isCompact_kball x).inter_right (b3Forms_isCompact_kball y).isClosed
  obtain ⟨t, htK, ht⟩ := hK.elim_nhds_subcover
    (fun q ↦ {q' | b3Forms_transVal A x y q' = b3Forms_transVal A x y q}) fun q hq ↦
      b3Forms_transVal_eventually hA hdA
        ⟨b3Forms_kball_subset_cball_two x hq.1, b3Forms_kball_subset_cball_two y hq.2⟩
  refine ⟨t.image (b3Forms_transVal A x y), fun q hq ↦ ?_, fun s hs ↦ ?_⟩
  · obtain ⟨q₀, hq₀, hqq⟩ := mem_iUnion₂.1 (ht hq)
    exact Finset.mem_image.2 ⟨q₀, hq₀, hqq.symm⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hs
    exact ⟨q, htK q hq, rfl⟩

variable [ProperSpace E] [T2Space M] [CompactSpace M]

omit hA hdA in
theorem b3Forms_exists_finite_cover :
    ∃ F : Finset M, univ ⊆ ⋃ x ∈ F, b3Forms_cball E 1 x := by
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x : M ↦ b3Forms_cball E 1 x)
    fun x _ ↦ (b3Forms_isOpen_cball 1 x).mem_nhds (b3Forms_mem_cball_self one_pos x)
  exact ⟨t, ht⟩

/-- **The periods of a family of closed forms along loops lie in a finitely generated group.**
Subdividing a loop by a Lebesgue number of a finite cover by chart balls, its period is a sum of
transition values between the primitives of consecutive balls, which take finitely many values. -/
theorem b3Forms_periods_mem_closure :
    ∃ S : Set (Θ → ℝ), S.Finite ∧ (∀ s ∈ S, ∃ x y q : M,
      q ∈ b3Forms_kball E x ∩ b3Forms_kball E y ∧ s = b3Forms_transVal A x y q) ∧
      ∀ γ : ℝ → M, Function.Periodic γ 1 → ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ →
        (fun θ ↦ b3Forms_lineIntegral (A θ) γ 0 1) ∈ AddSubgroup.closure S := by
  classical
  obtain ⟨F, hF⟩ := b3Forms_exists_finite_cover (E := E) (M := M)
  choose T hT hT' using fun x y : M ↦ b3Forms_transVal_finite hA hdA x y
  refine ⟨⋃ x ∈ F, ⋃ y ∈ F, (T x y : Set (Θ → ℝ)), F.finite_toSet.biUnion fun x _ ↦
    F.finite_toSet.biUnion fun y _ ↦ (T x y).finite_toSet, fun s hs ↦ ?_, fun γ hper hγ ↦ ?_⟩
  · obtain ⟨x, -, hs⟩ := mem_iUnion₂.1 hs
    obtain ⟨y, -, hs⟩ := mem_iUnion₂.1 hs
    obtain ⟨q, hq, rfl⟩ := hT' x y s hs
    exact ⟨x, y, q, hq, rfl⟩
  have hcov : Icc (0 : ℝ) 1 ⊆ ⋃ i : F, γ ⁻¹' b3Forms_cball E 1 (i : M) := fun τ _ ↦ by
    obtain ⟨x, hx, hτ⟩ := mem_iUnion₂.1 (hF (mem_univ (γ τ)))
    exact mem_iUnion.2 ⟨⟨x, hx⟩, hτ⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun i : F ↦ (b3Forms_isOpen_cball 1 (i : M)).preimage hγ.continuous) hcov
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set m := n + 1
  have hm : (0 : ℝ) < m := by positivity
  have hm' : 1 / (m : ℝ) < δ := by simpa [m] using hn
  set a : ℕ → ℝ := fun k ↦ (k : ℝ) / m
  have ha : ∀ k : Fin m, a k ∈ Icc (0 : ℝ) 1 := fun k ↦
    ⟨by positivity, (div_le_one hm).2 (by exact_mod_cast k.2.le)⟩
  choose x hx using fun k : Fin m ↦ hleb (a k) (ha k)
  have hpiece : ∀ (k : Fin m), ∀ τ ∈ uIcc (a k) (a (k + 1)), γ τ ∈ b3Forms_cball E 1 (x k : M) :=
    fun k τ hτ ↦ by
      refine hx k (Metric.mem_ball.2 ?_)
      rw [uIcc_of_le (by simp only [a]; gcongr; simp)] at hτ
      rw [Real.dist_eq, abs_lt]
      have h1 : a (k + 1) - a k = 1 / m := by simp only [a]; push_cast; field_simp; ring
      constructor <;> linarith [hτ.1, hτ.2, hm']
  set q : ℕ → M := fun j ↦ γ (a j)
  have h2 : ∀ (k : Fin m), ∀ τ ∈ uIcc (a k) (a (k + 1)), γ τ ∈ b3Forms_cball E 2 (x k : M) :=
    fun k τ hτ ↦ b3Forms_cball_mono (by norm_num) (x k : M) (hpiece k τ hτ)
  have hsplit : ∀ θ, b3Forms_lineIntegral (A θ) γ 0 1 = ∑ k : Fin m,
      (b3Forms_ballPrim (A θ) (x k) (q (k + 1)) - b3Forms_ballPrim (A θ) (x k) (q k)) := by
    intro θ
    have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := a) (n := m)
      (f := fun t ↦ A θ (γ t) (fun _ ↦ b3Forms_velocity γ t))
      fun k _ ↦ b3Forms_intervalIntegrable_lineIntegrand (hA θ) hγ _ _
    have ha0 : a 0 = 0 := by simp [a]
    have ham : a m = 1 := by simp only [a]; field_simp
    rw [ha0, ham, Finset.sum_range] at hsum
    rw [b3Forms_lineIntegral, ← hsum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    exact b3Forms_lineIntegral_eq_ballPrim (hA θ) (hdA θ) (x k : M) hγ (h2 k)
  have hnext : ∀ k : Fin m, q (finRotate m k : ℕ) = q (k + 1) := fun k ↦ by
    by_cases hk : k = Fin.last n
    · rw [hk, finRotate_last]
      simp only [q, a, Fin.val_last, Fin.val_zero, Nat.cast_zero, zero_div]
      rw [show ((n : ℕ) + 1 : ℕ) = m from rfl, div_self hm.ne']
      simpa using (hper 0).symm
    · rw [coe_finRotate_of_ne_last hk]
  have hfun : (fun θ ↦ b3Forms_lineIntegral (A θ) γ 0 1) =
      ∑ k : Fin m, b3Forms_transVal A (x k) (x (finRotate m k)) (q (k + 1)) := by
    funext θ
    rw [hsplit θ, Finset.sum_apply]
    simp only [b3Forms_transVal]
    have hrot := (Equiv.sum_comp (finRotate m)
      (fun j : Fin m ↦ b3Forms_ballPrim (A θ) (x j) (q j))).symm
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hrot]
    simp only [hnext]
  rw [hfun]
  refine AddSubgroup.sum_mem _ fun k _ ↦ AddSubgroup.subset_closure ?_
  refine mem_iUnion₂.2 ⟨x k, (x k).2, mem_iUnion₂.2 ⟨x (finRotate m k), (x _).2, hT _ _ _ ⟨?_, ?_⟩⟩⟩
  · exact b3Forms_cball_one_subset_kball _ (hpiece k _ right_mem_uIcc)
  · rw [← hnext]
    exact b3Forms_cball_one_subset_kball _ (hpiece _ _ left_mem_uIcc)

end Family

end Real

section Finite

/-- A subgroup of a subgroup generated by a finite set is finitely generated. -/
theorem b3Forms_finite_of_le_closure {G : Type*} [AddCommGroup G] {Λ : AddSubgroup G}
    {T : Set G} (hT : T.Finite) (hΛ : Λ ≤ AddSubgroup.closure T) : Module.Finite ℤ Λ := by
  have h1 : AddSubgroup.FG (AddSubgroup.closure T) := (AddSubgroup.fg_iff _).2 ⟨T, rfl, hT⟩
  have h2 : (AddSubgroup.closure T).toIntSubmodule.FG :=
    (Submodule.fg_iff_addSubgroup_fg _).2 h1
  have h3 : Λ.toIntSubmodule.FG := h2.of_le (AddSubgroup.toIntSubmodule.monotone hΛ)
  have h4 : Λ.FG := (Submodule.fg_iff_addSubgroup_fg _).1 h3
  exact Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg Λ).2 h4)

end Finite

section Hol

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- **The period lattice of a compact Riemann surface is finitely generated** (statement 5 of
`CurveJacobian.lean`). -/
theorem b3Forms_periodLattice_finite [T2Space C] [CompactSpace C]
    (hE : Module.finrank ℂ E = 1) : Module.Finite ℤ (b3_periodLattice E C) := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_pos (by rw [hE]; exact one_pos)
  have : IsManifold 𝓘(ℝ, E) ∞ C := b3Forms_isManifold_real
  set A : b3_HolForm E C × Fin 2 → C → E [⋀^Fin 1]→L[ℝ] ℝ :=
    fun p ↦ if p.2 = 0 then b3Forms_reForm p.1 else b3Forms_imForm p.1
  have hA : ∀ p, b3Forms_IsSmooth (A p) := fun p ↦ by
    by_cases h : p.2 = 0
    · simp only [A, h, ite_true]; exact b3Forms_isSmooth_reForm _
    · simp only [A, h, ite_false]; exact b3Forms_isSmooth_imForm _
  have hdA : ∀ p, b3Forms_d (A p) = 0 := fun p ↦ by
    by_cases h : p.2 = 0
    · simp only [A, h, ite_true]; exact b3Forms_d_reForm hE _
    · simp only [A, h, ite_false]; exact b3Forms_d_imForm hE _
  obtain ⟨S, hS, -, hmem⟩ := b3Forms_periods_mem_closure hA hdA
  let Φ : (b3_HolForm E C × Fin 2 → ℝ) →+ (b3_HolForm E C → ℂ) :=
    { toFun := fun f θ ↦ (f (θ, 0) : ℂ) + Complex.I * (f (θ, 1) : ℂ)
      map_zero' := by funext θ; simp
      map_add' := fun f g ↦ by funext θ; simp; ring }
  refine b3Forms_finite_of_le_closure (hS.image Φ) ?_
  rw [b3_periodLattice, AddSubgroup.closure_le]
  rintro _ ⟨γ, rfl⟩
  have h := AddSubgroup.mem_map_of_mem Φ (hmem γ.1 γ.2.1 γ.2.2)
  rw [AddMonoidHom.map_closure] at h
  have e : b3_period E C γ = Φ (fun p ↦ b3Forms_lineIntegral (A p) γ.1 0 1) := by
    funext θ
    rw [b3Forms_period_eq]
    simp [Φ, A]
  rw [SetLike.mem_coe, e]
  exact h

end Hol

end HodgeLean.Foundations.Program

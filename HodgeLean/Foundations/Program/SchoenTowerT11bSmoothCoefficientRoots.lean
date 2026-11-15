import HodgeLean.Foundations.Program.SchoenTowerT11bRootSections

/-! Simple roots with a parameter in a real Banach space.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open Filter
open scoped Topology

/-- Smooth coefficient functions give a jointly smooth polynomial family over any real normed parameter space.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional local root step. -/
theorem s2v_t11b_smooth_coefficient_family_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Polynomial (E → ℝ)) (hP : ∀ i, ContDiff ℝ (⊤ : WithTop ℕ∞) (P.coeff i)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun z : E × ℝ => P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) z.1) z.2) := by
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply ContDiff.sum
  intro i hi
  exact ((hP i).comp contDiff_fst).mul (contDiff_snd.pow i)

/-- The vertical derivative of a smooth-coefficient family is the derivative of its actual specialized polynomial.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional local root step. -/
theorem s2v_t11b_smooth_coefficient_vertical_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Polynomial (E → ℝ)) (hP : ∀ i, ContDiff ℝ (⊤ : WithTop ℕ∞) (P.coeff i)) (a : E) (b : ℝ) :
    (fderiv ℝ (fun z : E × ℝ => P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) z.1) z.2) (a, b)) ∘L
        (ContinuousLinearMap.inr ℝ E ℝ) =
      ContinuousLinearMap.toSpanSingleton ℝ
        ((P.map (Pi.evalRingHom (fun _ : E => ℝ) a)).derivative.eval b) := by
  have hF := (s2v_t11b_smooth_coefficient_family_contDiff P hP).hasStrictFDerivAt
    (x := (a, b)) (by simp)
  have h := hF.hasFDerivAt.comp b (hasFDerivAt_prodMk_right a b)
  have hq := ((P.map (Pi.evalRingHom (fun _ : E => ℝ) a)).hasDerivAt b).hasFDerivAt
  apply h.unique
  simpa only [Function.comp_def, Polynomial.eval₂_eq_eval_map] using hq

/-- A simple real root has a smooth local section over an arbitrary real Banach parameter space.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional local root step. -/
theorem s2v_t11b_smooth_coefficient_simple_root_section {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Polynomial (E → ℝ)) (hP : ∀ i, ContDiff ℝ (⊤ : WithTop ℕ∞) (P.coeff i))
    (a : E) (b : ℝ) (hroot : P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) a) b = 0)
    (hsimple : (P.map (Pi.evalRingHom (fun _ : E => ℝ) a)).derivative.eval b ≠ 0) :
    ∃ ψ : E → ℝ, ψ a = b ∧ ContDiffAt ℝ 1 ψ a ∧
      (∀ᶠ z : E × ℝ in 𝓝 (a, b),
        P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) z.1) z.2 = 0 ↔ ψ z.1 = z.2) ∧
      (∀ᶠ t : E in 𝓝 a, P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) t) (ψ t) = 0) := by
  have cdf : ContDiffAt ℝ 1
      (fun z : E × ℝ => P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) z.1) z.2) (a, b) :=
    ((s2v_t11b_smooth_coefficient_family_contDiff P hP).of_le (by simp)).contDiffAt
  have hinv : ((fderiv ℝ
      (fun z : E × ℝ => P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) z.1) z.2) (a, b)) ∘L
      ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
    rw [s2v_t11b_smooth_coefficient_vertical_derivative P hP]
    exact ⟨ContinuousLinearEquiv.unitsEquivAut ℝ
      (Units.mk0 ((P.map (Pi.evalRingHom (fun _ : E => ℝ) a)).derivative.eval b) hsimple), rfl⟩
  let ψ := cdf.implicitFunction (by norm_num) hinv
  refine ⟨ψ, cdf.implicitFunction_apply_self (by norm_num) hinv,
    cdf.contDiffAt_implicitFunction (by norm_num) hinv, ?_, ?_⟩
  · simpa only [hroot] using cdf.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv
  · simpa only [hroot] using cdf.eventually_apply_implicitFunction (by norm_num) hinv

/-- A simple root has a smooth unique section on an actual open ball in the Banach parameter space.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional local root neighborhood step. -/
theorem s2v_t11b_smooth_coefficient_root_neighborhood {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Polynomial (E → ℝ)) (hP : ∀ i, ContDiff ℝ (⊤ : WithTop ℕ∞) (P.coeff i))
    (a : E) (b : ℝ) (hroot : P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) a) b = 0)
    (hsimple : (P.map (Pi.evalRingHom (fun _ : E => ℝ) a)).derivative.eval b ≠ 0) :
    ∃ ε δ : ℝ, ∃ ψ : E → ℝ, 0 < ε ∧ 0 < δ ∧ ψ a = b ∧
      ContDiffOn ℝ 1 ψ (Metric.ball a ε) ∧
      (∀ t ∈ Metric.ball a ε, ψ t ∈ Metric.ball b δ ∧
        P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) t) (ψ t) = 0) ∧
      ∀ t ∈ Metric.ball a ε, ∀ x ∈ Metric.ball b δ,
        P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) t) x = 0 ↔ ψ t = x := by
  obtain ⟨ψ, hψa, hψ, heq, hzero⟩ := s2v_t11b_smooth_coefficient_simple_root_section P hP a b hroot hsimple
  obtain ⟨r, hr, hrect⟩ := Metric.eventually_nhds_iff.mp heq
  have hmap : ∀ᶠ t in 𝓝 a, ψ t ∈ Metric.ball b r := by
    have ht : Tendsto ψ (𝓝 a) (𝓝 b) := by
      simpa only [hψa] using hψ.continuousAt.tendsto
    exact ht.eventually (Metric.ball_mem_nhds b hr)
  obtain ⟨s, hs, hsmall⟩ := Metric.eventually_nhds_iff.mp
    ((hψ.eventually (by norm_num)).and (hmap.and hzero))
  refine ⟨min r s, r, ψ, lt_min hr hs, hr, hψa, ?_, ?_, ?_⟩
  · intro t ht
    exact (hsmall ((Metric.mem_ball.mp ht).trans_le (min_le_right r s))).1.contDiffWithinAt
  · intro t ht
    exact (hsmall ((Metric.mem_ball.mp ht).trans_le (min_le_right r s))).2
  · intro t ht x hx
    apply hrect (y := (t, x))
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨(Metric.mem_ball.mp ht).trans_le (min_le_left r s), Metric.mem_ball.mp hx⟩

/-- Projection of a polynomial zero set is a local homeomorphism at a simple vertical root.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional local projection step. -/
theorem s2v_t11b_smooth_coefficient_root_projection_chart {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Polynomial (E → ℝ)) (hP : ∀ i, ContDiff ℝ (⊤ : WithTop ℕ∞) (P.coeff i))
    (a : E) (b : ℝ)
    (hroot : P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) a) b = 0)
    (hsimple : (P.map (Pi.evalRingHom (fun _ : E => ℝ) a)).derivative.eval b ≠ 0) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ e : Metric.ball a ε ≃ₜ
      {z : E × ℝ | z.1 ∈ Metric.ball a ε ∧ z.2 ∈ Metric.ball b δ ∧
        P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) z.1) z.2 = 0},
      ∀ t, (e t).val.1 = t.val := by
  obtain ⟨ε, δ, ψ, hε, hδ, _, hψ, hvalues, huniq⟩ :=
    s2v_t11b_smooth_coefficient_root_neighborhood P hP a b hroot hsimple
  let e : Metric.ball a ε ≃ₜ
      {z : E × ℝ | z.1 ∈ Metric.ball a ε ∧ z.2 ∈ Metric.ball b δ ∧
        P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) z.1) z.2 = 0} :=
    { toFun := fun t => ⟨(t.val, ψ t.val), t.property, hvalues t.val t.property⟩
      invFun := fun z => ⟨z.val.1, z.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun z => by
        apply Subtype.ext
        refine Prod.ext rfl ?_
        exact (huniq z.val.1 z.property.1 z.val.2 z.property.2.1).mp z.property.2.2
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.prodMk
          (continuousOn_iff_continuous_domRestrict.mp hψ.continuousOn)
      continuous_invFun :=
        (continuous_fst.comp continuous_subtype_val).subtype_mk _ }
  exact ⟨ε, δ, hε, hδ, e, fun _ => rfl⟩

end HodgeLean.Foundations.Program

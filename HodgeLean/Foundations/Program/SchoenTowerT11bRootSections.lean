import HodgeLean.Foundations.Program.SchoenTowerT11bDefs
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Local sections of polynomial families at simple roots.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open Filter
open scoped Topology

/-- Polynomial families in a parameter and a fiber coordinate are smooth jointly.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, local root-section step. -/
theorem s2v_t11b_polynomial_family_contDiff (P : Polynomial (Polynomial ℝ)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun z : ℝ × ℝ => P.eval₂ (Polynomial.evalRingHom z.1) z.2) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [Polynomial.eval₂_add] using hP.add hQ
  | monomial i q =>
    have hq : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun t : ℝ => q.eval t) := by
      induction q using Polynomial.induction_on' with
      | add q r hq hr => simpa only [Polynomial.eval_add] using hq.add hr
      | monomial j c =>
        simpa only [Polynomial.eval_monomial] using
          (contDiff_const.mul (contDiff_id.pow j) :
            ContDiff ℝ (⊤ : WithTop ℕ∞) (fun t : ℝ => c * t ^ j))
    simpa only [Polynomial.eval₂_monomial, Polynomial.coe_evalRingHom, Function.comp_def] using
      (hq.comp contDiff_fst).mul (contDiff_snd.pow i)

/-- The vertical analytic derivative is the derivative of the specialized polynomial.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, local root-section step. -/
theorem s2v_t11b_polynomial_family_vertical_derivative
    (P : Polynomial (Polynomial ℝ)) (a b : ℝ) :
    (fderiv ℝ (fun z : ℝ × ℝ => P.eval₂ (Polynomial.evalRingHom z.1) z.2) (a, b)) ∘L
        (ContinuousLinearMap.inr ℝ ℝ ℝ) =
      ContinuousLinearMap.toSpanSingleton ℝ
        ((P.map (Polynomial.evalRingHom a)).derivative.eval b) := by
  have hF := (s2v_t11b_polynomial_family_contDiff P).hasStrictFDerivAt
    (x := (a, b)) (by simp)
  have h := hF.hasFDerivAt.comp b (hasFDerivAt_prodMk_right a b)
  have hq := ((P.map (Polynomial.evalRingHom a)).hasDerivAt b).hasFDerivAt
  apply h.unique
  simpa only [Function.comp_def, Polynomial.eval₂_eq_eval_map] using hq

/-- A simple real root of a polynomial family has a locally unique differentiable section.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, local root-section step. -/
theorem s2v_t11b_simple_root_section (P : Polynomial (Polynomial ℝ)) (a b : ℝ)
    (hroot : P.eval₂ (Polynomial.evalRingHom a) b = 0)
    (hsimple : (P.map (Polynomial.evalRingHom a)).derivative.eval b ≠ 0) :
    ∃ ψ : ℝ → ℝ, ψ a = b ∧ DifferentiableAt ℝ ψ a ∧
      (∀ᶠ z : ℝ × ℝ in 𝓝 (a, b),
        P.eval₂ (Polynomial.evalRingHom z.1) z.2 = 0 ↔ ψ z.1 = z.2) ∧
      (∀ᶠ t : ℝ in 𝓝 a, P.eval₂ (Polynomial.evalRingHom t) (ψ t) = 0) := by
  have hF := (s2v_t11b_polynomial_family_contDiff P).hasStrictFDerivAt
    (x := (a, b)) (by simp)
  have hinv : ((fderiv ℝ
      (fun z : ℝ × ℝ => P.eval₂ (Polynomial.evalRingHom z.1) z.2) (a, b)) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [s2v_t11b_polynomial_family_vertical_derivative]
    exact ⟨ContinuousLinearEquiv.unitsEquivAut ℝ
      (Units.mk0 ((P.map (Polynomial.evalRingHom a)).derivative.eval b) hsimple), rfl⟩
  let ψ := hF.implicitFunctionOfProdDomain hinv
  have heq := hF.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  refine ⟨ψ, heq.self_of_nhds.mp rfl,
    (hF.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).differentiableAt, ?_, ?_⟩
  · simpa only [hroot] using heq
  · simpa only [hroot] using hF.eventually_apply_implicitFunctionOfProdDomain hinv

/-- The local section through a simple root is continuously differentiable.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, local root-section step. -/
theorem s2v_t11b_simple_root_section_contDiff (P : Polynomial (Polynomial ℝ)) (a b : ℝ)
    (hroot : P.eval₂ (Polynomial.evalRingHom a) b = 0)
    (hsimple : (P.map (Polynomial.evalRingHom a)).derivative.eval b ≠ 0) :
    ∃ ψ : ℝ → ℝ, ψ a = b ∧ ContDiffAt ℝ 1 ψ a ∧
      (∀ᶠ z : ℝ × ℝ in 𝓝 (a, b),
        P.eval₂ (Polynomial.evalRingHom z.1) z.2 = 0 ↔ ψ z.1 = z.2) ∧
      (∀ᶠ t : ℝ in 𝓝 a, P.eval₂ (Polynomial.evalRingHom t) (ψ t) = 0) := by
  have cdf : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ => P.eval₂ (Polynomial.evalRingHom z.1) z.2) (a, b) :=
    ((s2v_t11b_polynomial_family_contDiff P).of_le (by simp)).contDiffAt
  have hinv : ((fderiv ℝ
      (fun z : ℝ × ℝ => P.eval₂ (Polynomial.evalRingHom z.1) z.2) (a, b)) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [s2v_t11b_polynomial_family_vertical_derivative]
    exact ⟨ContinuousLinearEquiv.unitsEquivAut ℝ
      (Units.mk0 ((P.map (Polynomial.evalRingHom a)).derivative.eval b) hsimple), rfl⟩
  let ψ := cdf.implicitFunction (by norm_num) hinv
  refine ⟨ψ, cdf.implicitFunction_apply_self (by norm_num) hinv,
    cdf.contDiffAt_implicitFunction (by norm_num) hinv, ?_, ?_⟩
  · simpa only [hroot] using cdf.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv
  · simpa only [hroot] using cdf.eventually_apply_implicitFunction (by norm_num) hinv

/-- A simple root gives an actual open base interval with a smooth unique root section.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, local root-section step. -/
theorem s2v_t11b_simple_root_neighborhood (P : Polynomial (Polynomial ℝ)) (a b : ℝ)
    (hroot : P.eval₂ (Polynomial.evalRingHom a) b = 0)
    (hsimple : (P.map (Polynomial.evalRingHom a)).derivative.eval b ≠ 0) :
    ∃ ε δ : ℝ, ∃ ψ : ℝ → ℝ, 0 < ε ∧ 0 < δ ∧ ψ a = b ∧
      ContDiffOn ℝ 1 ψ (Metric.ball a ε) ∧
      (∀ t ∈ Metric.ball a ε, ψ t ∈ Metric.ball b δ ∧
        P.eval₂ (Polynomial.evalRingHom t) (ψ t) = 0) ∧
      ∀ t ∈ Metric.ball a ε, ∀ x ∈ Metric.ball b δ,
        P.eval₂ (Polynomial.evalRingHom t) x = 0 ↔ ψ t = x := by
  obtain ⟨ψ, hψa, hψ, heq, hzero⟩ := s2v_t11b_simple_root_section_contDiff P a b hroot hsimple
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
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, local root-section step. -/
theorem s2v_t11b_simple_root_projection_chart (P : Polynomial (Polynomial ℝ)) (a b : ℝ)
    (hroot : P.eval₂ (Polynomial.evalRingHom a) b = 0)
    (hsimple : (P.map (Polynomial.evalRingHom a)).derivative.eval b ≠ 0) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ e : Metric.ball a ε ≃ₜ
      {z : ℝ × ℝ | z.1 ∈ Metric.ball a ε ∧ z.2 ∈ Metric.ball b δ ∧
        P.eval₂ (Polynomial.evalRingHom z.1) z.2 = 0},
      ∀ t, (e t).val.1 = t.val := by
  obtain ⟨ε, δ, ψ, hε, hδ, _, hψ, hvalues, huniq⟩ :=
    s2v_t11b_simple_root_neighborhood P a b hroot hsimple
  let e : Metric.ball a ε ≃ₜ
      {z : ℝ × ℝ | z.1 ∈ Metric.ball a ε ∧ z.2 ∈ Metric.ball b δ ∧
        P.eval₂ (Polynomial.evalRingHom z.1) z.2 = 0} :=
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
          (continuousOn_iff_continuous_restrict.mp hψ.continuousOn)
      continuous_invFun :=
        (continuous_fst.comp continuous_subtype_val).subtype_mk _ }
  exact ⟨ε, δ, hε, hδ, e, fun _ => rfl⟩

/-- A compact region without roots stays without roots for nearby parameter values.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, local root-section step. -/
theorem s2v_t11b_polynomial_family_compact_root_exclusion
    (P : Polynomial (Polynomial ℝ)) (a : ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hno : ∀ x ∈ K, P.eval₂ (Polynomial.evalRingHom a) x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Metric.ball a ε, ∀ x ∈ K,
      P.eval₂ (Polynomial.evalRingHom t) x ≠ 0 := by
  let U : Set (ℝ × ℝ) :=
    {z | P.eval₂ (Polynomial.evalRingHom z.1) z.2 ≠ 0}
  have hU : IsOpen U := isOpen_compl_singleton.preimage
    (s2v_t11b_polynomial_family_contDiff P).continuous
  have hprod : ({a} : Set ℝ) ×ˢ K ⊆ U := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    obtain rfl := Set.mem_singleton_iff.mp ht
    exact hno x hx
  obtain ⟨V, W, hV, _, haV, hKW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton hK hU hprod
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV a (haV (Set.mem_singleton a))
  exact ⟨ε, hε, fun t ht x hx => (show (t, x) ∈ U from hVW ⟨hball ht, hKW hx⟩)⟩

end HodgeLean.Foundations.Program

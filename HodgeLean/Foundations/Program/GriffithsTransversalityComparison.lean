import HodgeLean.Foundations.Program.GriffithsTransversalityChains

/-! Liftable scalar cochains and their Čech–de Rham periods along retained polygons.
A lift of a scalar cochain `s` is a family of holomorphic one-form coefficients `β_a` on the
retained charts with `β_a − β_b = d s_ab`. The chain period of `(β, s)` along a polygon adds the
segment integrals of `β` and the values of `s` at the vertices.
HC no distance; AV milestone no distance. -/
noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

section B66gLift

/-- Holomorphic one-form coefficients on the retained charts whose chart differences are the
differentials of the scalar cochain `s`, written in the first chart of each overlap.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §§8–9, the Čech–de Rham complex. -/
def b66g_IsLift (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (s : b66k_Cochain R)
    (β : b66k_Index R → ℂ → ℂ) : Prop :=
  (∀ a, AnalyticOnNhd ℂ (β a) (b66k_domain R t a)) ∧
  ∀ a b w, w ∈ b66k_refinementDomain R t 1 a b →
    HasDerivAt (fun z => s a b ((R.atlas.A a).symm (t.val, z)).2)
      (β a w - β b (b66k_transition R a b (t.val, w)) *
        fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1)) w

theorem b66g_IsLift.add {R : rf8_SharedFamily} {t : b6t_polydisc mr_base} {s s' : b66k_Cochain R}
    {β β' : b66k_Index R → ℂ → ℂ} (h : b66g_IsLift R t s β) (h' : b66g_IsLift R t s' β') :
    b66g_IsLift R t (s + s') (β + β') := by
  refine ⟨fun a => (h.1 a).add (h'.1 a), fun a b w hw => ?_⟩
  have := (h.2 a b w hw).add (h'.2 a b w hw)
  convert this using 1
  simp only [Pi.add_apply]
  ring

theorem b66g_IsLift.smul {R : rf8_SharedFamily} {t : b6t_polydisc mr_base} {s : b66k_Cochain R}
    {β : b66k_Index R → ℂ → ℂ} (c : ℂ) (h : b66g_IsLift R t s β) :
    b66g_IsLift R t (c • s) (c • β) := by
  refine ⟨fun a => analyticOnNhd_const.mul (h.1 a), fun a b w hw => ?_⟩
  have := (h.2 a b w hw).const_mul c
  convert this using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem b66g_IsLift.zero (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66g_IsLift R t 0 0 := by
  refine ⟨fun a => analyticOnNhd_const, fun a b w _ => ?_⟩
  simp only [Pi.zero_apply, sub_zero, zero_mul]
  exact hasDerivAt_const w (0 : ℂ)

/-- Two lifts of the same cochain differ by the coefficients of a global holomorphic form. -/
theorem b66g_lift_sub (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {s : b66k_Cochain R}
    {β β' : b66k_Index R → ℂ → ℂ} (h : b66g_IsLift R t s β) (h' : b66g_IsLift R t s β') :
    ∃ q ∈ b66g_forms R t 1, ∀ a w, w ∈ b66k_domain R t a →
      β a w - β' a w = q a ((R.atlas.A a).symm (t.val, w)).2 := by
  let q : b66g_Coeff R := fun a x =>
    if (t, x) ∈ (R.atlas.A a).source then β a (R.atlas.A a (t, x)).2 - β' a (R.atlas.A a (t, x)).2
    else 0
  have hq : ∀ a w, w ∈ b66k_domain R t a →
      q a ((R.atlas.A a).symm (t.val, w)).2 = β a w - β' a w := by
    intro a w hw
    obtain ⟨h1, h2⟩ := b66g_inv_point R t a w hw
    simp only [q, h1, ↓reduceIte, h2]
  refine ⟨q, Submodule.subset_span ⟨fun a => ?_, fun a b x ha hb => ?_, fun a x hx => ?_⟩,
    fun a w hw => (hq a w hw).symm⟩
  · intro w hw
    refine ((h.1 a w hw).sub (h'.1 a w hw)).congr ?_
    filter_upwards [(b66g_domain_open R t a).mem_nhds hw] with z hz
    exact (hq a z hz).symm
  · have hc := b66g_chart_slice R t a x ha
    set w := (R.atlas.A a (t, x)).2
    have hw : w ∈ b66k_refinementDomain R t 1 a b := by
      refine ⟨?_, ?_⟩
      · rw [← hc.1]
        exact (R.atlas.A a).map_source ha
      · rw [one_smul, hc.2]
        exact hb
    have hu := (h.2 a b w hw).unique (h'.2 a b w hw)
    have hwd : w ∈ b66k_domain R t a := hw.1
    have htr := b66g_trans_point R t a b w hwd
    rw [hc.2] at htr
    have hvert := b66g_vertical_eq_D R t a b w hwd
    rw [hc.2] at hvert
    have hqa : q a x = β a w - β' a w := by
      have := hq a w hwd
      rwa [hc.2] at this
    have hqb : q b x = β b (b66k_transition R a b (t.val, w)) -
        β' b (b66k_transition R a b (t.val, w)) := by
      simp only [q, hb, ↓reduceIte, htr]
    rw [hqa, hqb, pow_one, hvert]
    linear_combination hu
  · simp only [q, hx, ↓reduceIte]

end B66gLift

section B66gChainPeriod

/-- The segment integral of a coefficient. -/
def b66g_segInt (f : ℂ → ℂ) (c e : ℂ) : ℂ := ∫ r in (0 : ℝ)..1, f (c + (r : ℂ) * (e - c)) * (e - c)

theorem b66g_segInt_add {f g : ℂ → ℂ} {c e : ℂ}
    (hf : ContinuousOn f (segment ℝ c e)) (hg : ContinuousOn g (segment ℝ c e)) :
    b66g_segInt (f + g) c e = b66g_segInt f c e + b66g_segInt g c e := by
  have hp : ∀ {h : ℂ → ℂ}, ContinuousOn h (segment ℝ c e) →
      IntervalIntegrable (fun r : ℝ => h (c + (r : ℂ) * (e - c)) * (e - c))
        MeasureTheory.volume 0 1 := by
    intro h hh
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    refine (hh.comp (continuous_const.add (Complex.continuous_ofReal.mul
      continuous_const)).continuousOn ?_).mul continuousOn_const
    intro r hr
    rw [segment_eq_image']
    exact ⟨r, hr, by simp [Complex.real_smul]⟩
  unfold b66g_segInt
  rw [← intervalIntegral.integral_add (hp hf) (hp hg)]
  congr 1
  funext r
  simp only [Pi.add_apply]
  ring

theorem b66g_segInt_smul (f : ℂ → ℂ) (c e k : ℂ) :
    b66g_segInt (k • f) c e = k * b66g_segInt f c e := by
  unfold b66g_segInt
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext r
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The fundamental theorem along a segment. -/
theorem b66g_segInt_deriv {v : ℂ → ℂ} {c e : ℂ} {U : Set ℂ}
    (hv : AnalyticOnNhd ℂ v U) (hseg : ∀ r ∈ Icc (0 : ℝ) 1, c + (r : ℂ) * (e - c) ∈ U) :
    b66g_segInt (deriv v) c e = v e - v c := by
  unfold b66g_segInt
  have hd : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => v (c + (r : ℂ) * (e - c)))
      (deriv v (c + (r : ℂ) * (e - c)) * (e - c)) r := by
    intro r hr
    rw [uIcc_of_le zero_le_one] at hr
    have hvd := (hv _ (hseg r hr)).differentiableAt.hasDerivAt
    have hl : HasDerivAt (fun r : ℝ => c + (r : ℂ) * (e - c)) (1 * (e - c)) r :=
      ((hasDerivAt_id r).ofReal_comp.mul_const (e - c)).const_add c
    rw [one_mul] at hl
    have := (hvd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r hl
    convert this using 1
    all_goals first
      | rfl
      | (simp only [ContinuousLinearMap.coe_restrictScalars',
          ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.mul ?_ continuousOn_const
    intro r hr
    exact ((hv _ (hseg r hr)).deriv.continuousAt.comp_of_eq
      (f := fun r : ℝ => c + (r : ℂ) * (e - c))
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
      rfl).continuousWithinAt

/-- Chain period of a pair `(β, s)` along a retained polygon over `t`.
Source: Bott–Tu, §9, Čech–de Rham periods; Forster, §20. -/
def b66g_cdr (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (D : b66g_Poly R)
    (β : b66k_Index R → ℂ → ℂ) (s : b66k_Cochain R) : ℂ :=
  ∑ k ∈ Finset.range D.N, (b66g_segInt (β (D.a k)) (D.c k) (D.E t.val k) +
    s (D.a (k + 1)) (D.a k) (D.V t (k + 1)).val.2)

theorem b66g_segIn_segment {R : rf8_SharedFamily} {t : b6t_polydisc mr_base}
    {a : b66k_Index R} {c e : ℂ} (h : b66g_SegIn R t a c e) :
    segment ℝ c e ⊆ b66k_domain R t a := by
  rw [segment_eq_image']
  rintro _ ⟨r, hr, rfl⟩
  show c + r • (e - c) ∈ _
  rw [Complex.real_smul]
  exact h r hr

theorem b66g_cdr_add (R : rf8_SharedFamily) {t : b6t_polydisc mr_base} (D : b66g_Poly R)
    (hv : D.Valid t) {β β' : b66k_Index R → ℂ → ℂ} (hβ : ∀ a, AnalyticOnNhd ℂ (β a) (b66k_domain R t a))
    (hβ' : ∀ a, AnalyticOnNhd ℂ (β' a) (b66k_domain R t a)) (s s' : b66k_Cochain R) :
    b66g_cdr R t D (β + β') (s + s') = b66g_cdr R t D β s + b66g_cdr R t D β' s' := by
  unfold b66g_cdr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs := b66g_segIn_segment (hv k).1
  rw [show (β + β') (D.a k) = β (D.a k) + β' (D.a k) from rfl,
    b66g_segInt_add ((hβ _).continuousOn.mono hs) ((hβ' _).continuousOn.mono hs)]
  simp only [Pi.add_apply]
  ring

theorem b66g_cdr_smul (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (D : b66g_Poly R)
    (k : ℂ) (β : b66k_Index R → ℂ → ℂ) (s : b66k_Cochain R) :
    b66g_cdr R t D (k • β) (k • s) = k * b66g_cdr R t D β s := by
  unfold b66g_cdr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (k • β) (D.a j) = k • β (D.a j) from rfl, b66g_segInt_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Holomorphic boundaries lift through the derivatives of their splittings. -/
theorem b66g_isLift_boundary (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {v : b66k_Index R → ℂ → ℂ} (hv : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a)) :
    b66g_IsLift R t (b66g_scalarBoundary R t v) (fun a => deriv (v a)) := by
  refine ⟨fun a => (hv a).deriv, fun a b w hw => ?_⟩
  obtain ⟨hm, hτd, -, -⟩ := b66g_transition_mem R t a b w hw
  have hτ := b66g_transition_hasDerivAt R t a b w hm
  have h1 := (hv a w hw.1).differentiableAt.hasDerivAt
  have h2 := (hv b _ hτd).differentiableAt.hasDerivAt.comp w hτ
  refine (h1.sub h2).congr_of_eventuallyEq ?_
  filter_upwards [b66g_overlap_eventually R t a b w hw] with z hz
  simp only [b66g_scalarBoundary, hz.1, ↓reduceIte, hz.2.1, hz.2.2]
  rfl

/-- Chain periods vanish on holomorphic boundaries. -/
theorem b66g_cdr_boundary (R : rf8_SharedFamily) {t : b6t_polydisc mr_base} (D : b66g_Poly R)
    (hD : D.Valid t) {v : b66k_Index R → ℂ → ℂ}
    (hv : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a)) :
    b66g_cdr R t D (fun a => deriv (v a)) (b66g_scalarBoundary R t v) = 0 := by
  have hterm : ∀ k : ℤ, b66g_segInt (deriv (v (D.a k))) (D.c k) (D.E t.val k) +
      b66g_scalarBoundary R t v (D.a (k + 1)) (D.a k) (D.V t (k + 1)).val.2 =
      v (D.a (k + 1)) (D.c (k + 1)) - v (D.a k) (D.c k) := by
    intro k
    rw [b66g_segInt_deriv (hv (D.a k)) (hD k).1]
    have hVv : (D.V t (k + 1)).val = (t, (D.V t (k + 1)).val.2) := b66g_fibre_val R t _
    have hm1 : (t, (D.V t (k + 1)).val.2) ∈ (R.atlas.A (D.a (k + 1))).source := by
      rw [← hVv]; exact b66g_inv_mem R t (D.a (k + 1)) (hD k).2.1
    have hm0 : (t, (D.V t (k + 1)).val.2) ∈ (R.atlas.A (D.a k)).source := by
      rw [← hVv]; exact (hD k).2.2
    have e1 : (R.atlas.A (D.a (k + 1)) (t, (D.V t (k + 1)).val.2)).2 = D.c (k + 1) := by
      rw [← hVv]; exact b66g_slice_inv R t (D.a (k + 1)) (hD k).2.1
    have e0 : (R.atlas.A (D.a k) (t, (D.V t (k + 1)).val.2)).2 = D.E t.val k := by
      rw [← hVv, D.E_eq_slice hD k]; rfl
    have hm : (t, (D.V t (k + 1)).val.2) ∈
        (R.atlas.A (D.a (k + 1))).source ∩ (R.atlas.A (D.a k)).source := ⟨hm1, hm0⟩
    simp only [b66g_scalarBoundary, hm, ↓reduceIte, e1, e0]
    ring
  unfold b66g_cdr
  refine (Finset.sum_congr rfl fun (k : ℕ) _ => hterm k).trans ?_
  have := Finset.sum_range_sub (fun k : ℕ => v (D.a k) (D.c k)) D.N
  push_cast at this
  rw [this]
  have h0 := D.a_add 0
  have h0' := D.c_add 0
  simp only [zero_add] at h0 h0'
  simp only [h0, h0', sub_self]

/-- Global forms lift the zero cochain through their chart coefficients. -/
theorem b66g_isLift_form (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {q : b66g_Coeff R}
    (hq : q ∈ b66g_forms R t 1) : b66g_IsLift R t 0 (b66g_coef R t q) := by
  obtain ⟨hqa, hql, -⟩ := b66g_forms_spec R t 1 hq
  refine ⟨hqa, fun a b w hw => ?_⟩
  have hb : (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A b).source := by
    have := hw.2; rwa [one_smul] at this
  obtain ⟨-, hx⟩ := b66g_trans_inv R t a b w hw.1 hb
  have hvert := b66g_vertical_eq_D R t a b w hw.1
  have hlaw := hql a b _ (b66g_inv_point R t a w hw.1).1 hb
  have : b66g_coef R t q a w - b66g_coef R t q b (b66k_transition R a b (t.val, w)) *
      fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1) = 0 := by
    simp only [b66g_coef, hx]
    rw [hlaw, pow_one, hvert]
    ring
  rw [this]
  exact hasDerivAt_const w (0 : ℂ)

/-- The chain period of a global form is its period along the polygon. -/
theorem b66g_cdr_form (R : rf8_SharedFamily) {t : b6t_polydisc mr_base} (D : b66g_Poly R)
    (hD : D.Valid t) (q : b66g_forms R t 1) :
    b66g_cdr R t D (b66g_coef R t q.val) 0 =
      b3_period ℂ (rf8_fibre R.C t) (D.smoothLoop hD) (b66g_formEquiv R t q) := by
  obtain ⟨hqa, -, -⟩ := b66g_forms_spec R t 1 q.property
  rw [D.period_eq hD (b66g_formEquiv R t q) (fun k => b66g_coef R t q.val (D.a k))
    (fun k y hy v => ?_) (fun k => (hqa _).continuousOn)]
  · unfold b66g_cdr
    simp only [Pi.zero_apply, add_zero]
    rfl
  · change b66g_toForm R t q.val ⟨y, v⟩ = _
    rw [b66g_toForm_apply R t q.property (D.a k) y hy v]
    simp only [b66g_coef, b66g_inv_slice R t (D.a k) y hy]

/-- Chain periods only see the lift on the chart domains. -/
theorem b66g_cdr_congr (R : rf8_SharedFamily) {t : b6t_polydisc mr_base} (D : b66g_Poly R)
    (hD : D.Valid t) {β β' : b66k_Index R → ℂ → ℂ}
    (h : ∀ a w, w ∈ b66k_domain R t a → β a w = β' a w) (s : b66k_Cochain R) :
    b66g_cdr R t D β s = b66g_cdr R t D β' s := by
  unfold b66g_cdr b66g_segInt
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le zero_le_one] at hr
  simp only [h _ _ ((hD k).1 r hr)]

end B66gChainPeriod

section B66gComparisonMap

theorem b66g_scalarBoundary_add (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (v w : b66k_Index R → ℂ → ℂ) :
    b66g_scalarBoundary R t (v + w) = b66g_scalarBoundary R t v + b66g_scalarBoundary R t w := by
  funext a b x
  simp only [b66g_scalarBoundary, Pi.add_apply]
  split_ifs <;> ring

theorem b66g_scalarBoundary_smul (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (c : ℂ)
    (v : b66k_Index R → ℂ → ℂ) :
    b66g_scalarBoundary R t (c • v) = c • b66g_scalarBoundary R t v := by
  funext a b x
  simp only [b66g_scalarBoundary, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- Every holomorphic scalar boundary is the boundary of one holomorphic splitting. -/
theorem b66g_scalarBoundaries_rep (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {u : b66k_Cochain R} (hu : u ∈ b66g_scalarBoundaries R t) :
    ∃ v : b66k_Index R → ℂ → ℂ, (∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a)) ∧
      u = b66g_scalarBoundary R t v := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨0, fun a => analyticOnNhd_const, ?_⟩
    funext a b x
    simp [b66g_scalarBoundary]
  | add x y _ _ hx hy =>
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨v + w, fun a => (hv a).add (hw a), (b66g_scalarBoundary_add R t v w).symm⟩
  | smul c x _ hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨c • v, fun a => analyticOnNhd_const.mul (hv a),
      (b66g_scalarBoundary_smul R t c v).symm⟩

/-- Retained polygons representing the transported basis on the fibre at `t`.
Source: Hatcher, *Algebraic Topology*, §2.A, loops generate `H₁`; `b66g_poly_span`. -/
structure b66g_Rep (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base) {n : ℕ}
    (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) where
  m : Fin n → ℕ
  f : ∀ i, Fin (m i) → ℤ
  D : ∀ i, Fin (m i) → b66g_Poly R
  hv : ∀ i j, (D i j).Valid t
  hrep : ∀ i, ∑ j, f i j • b6m_loopClass (rf8_fibre R.C t) ((D i j).smoothLoop (hv i j)) =
    b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i)

theorem b66g_rep_exists (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base) {n : ℕ}
    (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) : Nonempty (b66g_Rep R s t B) := by
  have h : ∀ i, ∃ (m : ℕ) (f : Fin m → ℤ) (D : Fin m → b66g_Poly R) (hv : ∀ j, (D j).Valid t),
      ∑ j, f j • b6m_loopClass (rf8_fibre R.C t) ((D j).smoothLoop (hv j)) =
        b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i) := by
    intro i
    have hmem : b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i) ∈ Submodule.span ℤ
        {x : b6m_H1 (rf8_fibre R.C t) | ∃ (D : b66g_Poly R) (hv : D.Valid t),
          x = b6m_loopClass (rf8_fibre R.C t) (D.smoothLoop hv)} := by
      rw [b66g_poly_span R t]; exact Submodule.mem_top
    obtain ⟨m, f, g, hg⟩ := Submodule.mem_span_set'.1 hmem
    choose D hv hD using fun j => (g j).property
    refine ⟨m, f, D, hv, ?_⟩
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hD j]
    exact (int_smul_eq_zsmul _ (f j) _).symm
  choose m f D hv hrep using h
  exact ⟨⟨m, f, D, hv, hrep⟩⟩

variable {R : rf8_SharedFamily} {s t : b6t_polydisc mr_base} {n : ℕ}
  {B : Module.Basis (Fin n) ℤ (b66g_Homology R s)}

/-- Chain periods along the representatives of the transported basis. -/
def b66g_cdrVec (P : b66g_Rep R s t B) (β : b66k_Index R → ℂ → ℂ) (u : b66k_Cochain R) :
    Fin n → ℂ :=
  fun i => ∑ j, (P.f i j : ℂ) * b66g_cdr R t (P.D i j) β u

theorem b66g_cdrVec_form (P : b66g_Rep R s t B) (q : b66g_forms R t 1) :
    b66g_cdrVec P (b66g_coef R t q.val) 0 = fun i =>
      (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i))).val (b66g_formEquiv R t q) := by
  funext i
  rw [← P.hrep i, map_sum]
  simp only [b66g_cdrVec, b66g_cdr_form R _ (P.hv i _) q, map_zsmul, AddSubgroup.val_finsetSum,
    AddSubgroup.coe_zsmul, Finset.sum_apply, R.hP t, zsmul_eq_mul]
  rfl

theorem b66g_cdrVec_form_mem (P : b66g_Rep R s t B) (q : b66g_forms R t 1) :
    b66g_cdrVec P (b66g_coef R t q.val) 0 ∈ b66g_periodSubspace R s t B :=
  Submodule.subset_span ⟨b66g_formEquiv R t q, b66g_cdrVec_form P q⟩

theorem b66g_cdrVec_add (P : b66g_Rep R s t B) {β β' : b66k_Index R → ℂ → ℂ}
    (hβ : ∀ a, AnalyticOnNhd ℂ (β a) (b66k_domain R t a))
    (hβ' : ∀ a, AnalyticOnNhd ℂ (β' a) (b66k_domain R t a)) (u u' : b66k_Cochain R) :
    b66g_cdrVec P (β + β') (u + u') = b66g_cdrVec P β u + b66g_cdrVec P β' u' := by
  funext i
  simp only [b66g_cdrVec, Pi.add_apply, b66g_cdr_add R _ (P.hv i _) hβ hβ', mul_add,
    Finset.sum_add_distrib]

theorem b66g_cdrVec_smul (P : b66g_Rep R s t B) (c : ℂ) (β : b66k_Index R → ℂ → ℂ)
    (u : b66k_Cochain R) : b66g_cdrVec P (c • β) (c • u) = c • b66g_cdrVec P β u := by
  funext i
  simp only [b66g_cdrVec, b66g_cdr_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

variable (R t) in
/-- Holomorphic scalar cocycles together with a lift. -/
def b66g_L : Submodule ℂ (b66k_Cochain R × (b66k_Index R → ℂ → ℂ)) where
  carrier := {p | p.1 ∈ b66g_scalarCycles R t ∧ b66g_IsLift R t p.1 p.2}
  add_mem' := fun hp hq => ⟨Submodule.add_mem _ hp.1 hq.1, hp.2.add hq.2⟩
  zero_mem' := ⟨Submodule.zero_mem _, b66g_IsLift.zero R t⟩
  smul_mem' := fun c _ hp => ⟨Submodule.smul_mem _ c hp.1, hp.2.smul c⟩

variable (R t) in
/-- The class of the cocycle of a lifted pair. -/
def b66g_psi : b66g_L R t →ₗ[ℂ] b66g_H1O R t where
  toFun p := ⟨(b66g_scalarBoundaries R t).mkQ p.1.1, Submodule.mem_map_of_mem p.2.1⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- Chain periods of a lifted pair, modulo holomorphic periods. -/
def b66g_phi (P : b66g_Rep R s t B) :
    b66g_L R t →ₗ[ℂ] ((Fin n → ℂ) ⧸ b66g_periodSubspace R s t B) where
  toFun p := (b66g_periodSubspace R s t B).mkQ (b66g_cdrVec P p.1.2 p.1.1)
  map_add' p q := by
    rw [← map_add]
    congr 1
    exact b66g_cdrVec_add P p.2.2.1 q.2.2.1 _ _
  map_smul' c p := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    exact b66g_cdrVec_smul P c _ _

theorem b66g_ker_psi_le (P : b66g_Rep R s t B) :
    LinearMap.ker (b66g_psi R t) ≤ LinearMap.ker (b66g_phi P) := by
  intro p hp
  have h0 : (b66g_scalarBoundaries R t).mkQ p.1.1 = 0 := congrArg Subtype.val hp
  obtain ⟨v, hv, hpv⟩ := b66g_scalarBoundaries_rep R t ((Submodule.Quotient.mk_eq_zero _).1 h0)
  have hlift : b66g_IsLift R t p.1.1 p.1.2 := p.2.2
  rw [hpv] at hlift
  obtain ⟨q, hq, hqβ⟩ := b66g_lift_sub R t hlift (b66g_isLift_boundary R t hv)
  have hsplit : b66g_cdrVec P p.1.2 p.1.1 =
      b66g_cdrVec P (fun a => deriv (v a)) (b66g_scalarBoundary R t v) +
        b66g_cdrVec P (b66g_coef R t q) 0 := by
    rw [← b66g_cdrVec_add P (β := fun a => deriv (v a)) (β' := b66g_coef R t q)
      (fun a => (hv a).deriv) (b66g_forms_spec R t 1 hq).1, add_zero, ← hpv]
    funext i
    simp only [b66g_cdrVec]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [b66g_cdr_congr R _ (P.hv i j) (β' := (fun a => deriv (v a)) + b66g_coef R t q)
      (fun a w hw => ?_)]
    simp only [Pi.add_apply, b66g_coef]
    rw [← hqβ a w hw]
    ring
  have hb : b66g_cdrVec P (fun a => deriv (v a)) (b66g_scalarBoundary R t v) = 0 := by
    funext i
    simp only [b66g_cdrVec, b66g_cdr_boundary R _ (P.hv i _) hv, mul_zero, Finset.sum_const_zero,
      Pi.zero_apply]
  change (b66g_periodSubspace R s t B).mkQ (b66g_cdrVec P p.1.2 p.1.1) = 0
  rw [hsplit, hb, zero_add, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact b66g_cdrVec_form_mem P ⟨q, hq⟩

/-- The comparison on liftable classes. -/
def b66g_E0 (P : b66g_Rep R s t B) :
    LinearMap.range (b66g_psi R t) →ₗ[ℂ] ((Fin n → ℂ) ⧸ b66g_periodSubspace R s t B) :=
  ((LinearMap.ker (b66g_psi R t)).liftQ (b66g_phi P) (b66g_ker_psi_le P)).comp
    (b66g_psi R t).quotKerEquivRange.symm.toLinearMap

theorem b66g_E0_apply (P : b66g_Rep R s t B) (p : b66g_L R t) :
    b66g_E0 P ⟨b66g_psi R t p, LinearMap.mem_range_self _ p⟩ = b66g_phi P p := by
  have : (b66g_psi R t).quotKerEquivRange.symm ⟨b66g_psi R t p, LinearMap.mem_range_self _ p⟩ =
      Submodule.Quotient.mk p := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [b66g_E0, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
    Submodule.liftQ_apply]

end B66gComparisonMap

section B66gTargetDim

variable (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base) {n : ℕ}
  (B : Module.Basis (Fin n) ℤ (b66g_Homology R s))

theorem b66g_lattice_le_dual :
    (b3_periodLattice ℂ (rf8_fibre R.C t) : Set (b3_HolForm ℂ (rf8_fibre R.C t) → ℂ)) ⊆
      b3_linearDual ℂ (rf8_fibre R.C t) := by
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨γ, rfl⟩ := hy
    exact b3_period_mem_linearDual γ
  | zero => exact (b3_linearDual ℂ _).zero_mem
  | add y z _ _ hy hz => exact (b3_linearDual ℂ _).add_mem hy hz
  | neg y _ hy => exact (b3_linearDual ℂ _).neg_mem hy

theorem b66g_lattice_linear (l : b3_periodLattice ℂ (rf8_fibre R.C t)) (a : ℂ)
    (κ κ' : b3_HolForm ℂ (rf8_fibre R.C t)) : l.val (a • κ + κ') = a * l.val κ + l.val κ' :=
  b66g_lattice_le_dual R t l.property a κ κ'

/-- Holomorphic periods on the transported basis. -/
def b66g_perMap : b3_HolForm ℂ (rf8_fibre R.C t) →ₗ[ℂ] (Fin n → ℂ) where
  toFun κ i := (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i))).val κ
  map_add' κ κ' := by
    funext i
    have := b66g_lattice_linear R t (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i)))
      1 κ κ'
    simpa only [one_smul, one_mul, Pi.add_apply] using this
  map_smul' c κ := by
    funext i
    have := b66g_lattice_linear R t (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i)))
      c κ 0
    simp only [add_zero, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at this ⊢
    have h0 := b66g_lattice_linear R t
      (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i))) 1 0 0
    simp only [add_zero, one_smul, one_mul, smul_zero] at h0
    have hz : (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i))).val 0 = 0 := by
      linear_combination -h0
    rw [this, hz, add_zero]

theorem b66g_periodSubspace_eq :
    b66g_periodSubspace R s t B = LinearMap.range (b66g_perMap R s t B) := by
  unfold b66g_periodSubspace
  rw [← Submodule.span_eq (LinearMap.range (b66g_perMap R s t B))]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_range]
  exact ⟨fun ⟨κ, hκ⟩ => ⟨κ, hκ.symm⟩, fun ⟨κ, hκ⟩ => ⟨κ, hκ.symm⟩⟩

theorem b66g_perMap_injective : Function.Injective (b66g_perMap R s t B) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro κ hκ
  have hi : ∀ i, (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i))).val κ = 0 :=
    fun i => congrFun hκ i
  let B' := B.map (b6m_H1Equiv (b6m_transport mr_base R.C s t))
  let ev : b3_periodLattice ℂ (rf8_fibre R.C t) →+ ℂ :=
    { toFun := fun l => l.val κ
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let F : b6m_H1 (rf8_fibre R.C t) →ₗ[ℤ] ℂ := ev.toIntLinearMap ∘ₗ R.P t
  have hx : ∀ x : b6m_H1 (rf8_fibre R.C t), F x = 0 := by
    intro x
    rw [← B'.sum_repr x, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smul]
    have : F (B' i) = 0 := by
      change (R.P t (B' i)).val κ = 0
      rw [show B' i = b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i) from
        Module.Basis.map_apply _ _ _, hi i]
    rw [this, smul_zero]
  refine b3Forms_hol_eq_zero_of_periods (by simp) κ fun γ => ?_
  have := hx (b6m_loopClass (rf8_fibre R.C t) γ)
  change (R.P t _).val κ = 0 at this
  rw [R.hP t] at this
  exact this

theorem b66g_n_eq {s : b6t_polydisc mr_base} (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) :
    n = 2 * Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) := by
  have h1 : Module.finrank ℤ (b66g_Homology R s) = n := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  have h2 := (b6m_H1Equiv (b6m_transport mr_base R.C s t)).finrank_eq
  obtain ⟨P', -⟩ := b6m_period_comparison (rf8_fibre R.C t)
  have h3 := P'.finrank_eq
  have h4 := b3_finrank_periodLattice (E := ℂ) (C := rf8_fibre R.C t) (by simp)
  rw [← h1]
  change Module.finrank ℤ (b6m_H1 (rf8_fibre R.C s)) = _
  rw [h2, h3, h4]

theorem b66g_target_finrank :
    Module.finrank ℂ ((Fin n → ℂ) ⧸ b66g_periodSubspace R s t B) =
      Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) := by
  have hq := Submodule.finrank_quotient_add_finrank (b66g_periodSubspace R s t B)
  have hr : Module.finrank ℂ (b66g_periodSubspace R s t B) =
      Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) := by
    rw [b66g_periodSubspace_eq, LinearMap.finrank_range_of_inj (b66g_perMap_injective R s t B)]
  have hn := b66g_n_eq R t B
  rw [hr, Module.finrank_fin_fun] at hq
  omega

end B66gTargetDim

section B66gH1ODim

variable (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)

theorem b66g_residueSum_qadd' (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z) {m : ℕ} {q r : b66g_Coeff R}
    (hq : q ∈ b66g_forms R t m) (hr : r ∈ b66g_forms R t m) :
    b66g_residueSum R t S v (q + r) = b66g_residueSum R t S v q + b66g_residueSum R t S v r := by
  obtain ⟨hqa, _, _⟩ := b66g_forms_spec R t m hq
  obtain ⟨hra, _, _⟩ := b66g_forms_spec R t m hr
  unfold b66g_residueSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hdom := b66g_own_domain R t x
  have h1 : MeromorphicAt (fun z => v (t, x) z * q (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
      (R.atlas.A (t, x) (t, x)).2 := (hmero _ _ hdom).mul (hqa (t, x) _ hdom).meromorphicAt
  have h2 : MeromorphicAt (fun z => v (t, x) z * r (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
      (R.atlas.A (t, x) (t, x)).2 := (hmero _ _ hdom).mul (hra (t, x) _ hdom).meromorphicAt
  rw [← TauCeti.Contour.residue_add h1 h2]
  congr 1
  funext z
  simp only [Pi.add_apply]
  ring

/-- A meromorphic splitting of a scalar cochain, regular off a finite set. -/
def b66g_IsSplit (s : b66k_Cochain R) (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ) : Prop :=
  (∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z) ∧
  (∀ a z, z ∈ b66k_domain R t a → ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z) ∧
  ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source → (t, x) ∈ (R.atlas.A b).source →
    s a b x = v a (R.atlas.A a (t, x)).2 - v b (R.atlas.A b (t, x)).2

variable {R t}

theorem b66g_split_exists {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) :
    ∃ S v, b66g_IsSplit R t s S v := by
  obtain ⟨x₀, h, hm, han, hsp⟩ := b66g_scalar_split R t hs
  refine ⟨{x₀}, h, hm, fun a z hz hx => han a z hz (by simpa using hx),
    fun a b x _ ha hb => hsp a b x ha hb⟩

theorem b66g_IsSplit.add {s s' : b66k_Cochain R} {S S' : Finset R.C}
    {v v' : b66k_Index R → ℂ → ℂ} (h : b66g_IsSplit R t s S v) (h' : b66g_IsSplit R t s' S' v') :
    b66g_IsSplit R t (s + s') (S ∪ S') (v + v') := by
  refine ⟨fun a z hz => (h.1 a z hz).add (h'.1 a z hz), fun a z hz hx => ?_,
    fun a b x hx ha hb => ?_⟩
  · simp only [Finset.mem_union, not_or] at hx
    exact (h.2.1 a z hz hx.1).add (h'.2.1 a z hz hx.2)
  · simp only [Finset.mem_union, not_or] at hx
    simp only [Pi.add_apply, h.2.2 a b x hx.1 ha hb, h'.2.2 a b x hx.2 ha hb]
    ring

theorem b66g_IsSplit.smul {s : b66k_Cochain R} {S : Finset R.C} {v : b66k_Index R → ℂ → ℂ}
    (c : ℂ) (h : b66g_IsSplit R t s S v) : b66g_IsSplit R t (c • s) S (c • v) := by
  refine ⟨fun a z hz => (h.1 a z hz).const_smul c, fun a z hz hx => ?_,
    fun a b x hx ha hb => ?_⟩
  · exact AnalyticAt.const_smul (c := c) (h.2.1 a z hz hx)
  · simp only [Pi.smul_apply, smul_eq_mul, h.2.2 a b x hx ha hb]
    ring

theorem b66g_split_res_eq {s : b66k_Cochain R} {S S' : Finset R.C}
    {v v' : b66k_Index R → ℂ → ℂ} (h : b66g_IsSplit R t s S v) (h' : b66g_IsSplit R t s S' v')
    {η : b66g_Coeff R} (hη : η ∈ b66g_forms R t 1) :
    b66g_residueSum R t S v η = b66g_residueSum R t S' v' η :=
  b66g_scalar_split_unique R t s S S' v v' h.1 h.2.1 h.2.2 h'.1 h'.2.1 h'.2.2 hη

variable (R t) in
/-- Residue pairing of a scalar cochain with a holomorphic form, through any splitting. -/
def b66g_res (s : b66k_Cochain R) (η : b66g_Coeff R) : ℂ :=
  if h : ∃ S v, b66g_IsSplit R t s S v then b66g_residueSum R t h.choose h.choose_spec.choose η
  else 0

theorem b66g_res_eq {s : b66k_Cochain R} {S : Finset R.C} {v : b66k_Index R → ℂ → ℂ}
    (h : b66g_IsSplit R t s S v) {η : b66g_Coeff R} (hη : η ∈ b66g_forms R t 1) :
    b66g_res R t s η = b66g_residueSum R t S v η := by
  have he : ∃ S v, b66g_IsSplit R t s S v := ⟨S, v, h⟩
  rw [b66g_res, dite_eq_left_of_eq_true (eq_true he)]
  exact b66g_split_res_eq he.choose_spec.choose_spec h hη

variable (R t) in
/-- The residue pairing on holomorphic scalar cocycles. -/
def b66g_rho : b66g_scalarCycles R t →ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 1) where
  toFun s :=
    { toFun := fun η => b66g_res R t s.1 η.1
      map_add' := fun η η' => by
        obtain ⟨S, v, h⟩ := b66g_split_exists s.2
        rw [b66g_res_eq h η.2, b66g_res_eq h η'.2, b66g_res_eq h (η + η').2]
        exact b66g_residueSum_qadd' R t S v h.1 η.2 η'.2
      map_smul' := fun c η => by
        obtain ⟨S, v, h⟩ := b66g_split_exists s.2
        rw [b66g_res_eq h η.2, b66g_res_eq h (c • η).2]
        exact b66g_residueSum_smul R t S v c η.1 }
  map_add' s s' := by
    ext η
    obtain ⟨S, v, h⟩ := b66g_split_exists s.2
    obtain ⟨S', v', h'⟩ := b66g_split_exists s'.2
    change b66g_res R t (s.1 + s'.1) η.1 = b66g_res R t s.1 η.1 + b66g_res R t s'.1 η.1
    rw [b66g_res_eq (h.add h') η.2, b66g_res_eq h η.2, b66g_res_eq h' η.2,
      b66g_residueSum_add R t _ v v' h.1 h'.1 η.2,
      b66g_residueSum_extend R t S _ v h.2.1 η.2 Finset.subset_union_left,
      b66g_residueSum_extend R t S' _ v' h'.2.1 η.2 Finset.subset_union_right]
  map_smul' c s := by
    ext η
    obtain ⟨S, v, h⟩ := b66g_split_exists s.2
    change b66g_res R t (c • s.1) η.1 = c * b66g_res R t s.1 η.1
    rw [b66g_res_eq (h.smul c) η.2, b66g_res_eq h η.2, b66g_residueSum_vsmul]

theorem b66g_rho_boundary {s : b66g_scalarCycles R t} (hs : s.1 ∈ b66g_scalarBoundaries R t) :
    b66g_rho R t s = 0 := by
  obtain ⟨v, hv, hsv⟩ := b66g_scalarBoundaries_rep R t hs
  have hsp : b66g_IsSplit R t s.1 ∅ v := by
    refine ⟨fun a z hz => (hv a z hz).meromorphicAt, fun a z hz _ => hv a z hz,
      fun a b x _ ha hb => ?_⟩
    rw [hsv]
    simp only [b66g_scalarBoundary, show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source
      from ⟨ha, hb⟩, ↓reduceIte]
  ext η
  change b66g_res R t s.1 η.1 = 0
  rw [b66g_res_eq hsp η.2]
  simp [b66g_residueSum]

theorem b66g_rho_ker {s : b66g_scalarCycles R t} (hs : b66g_rho R t s = 0) :
    s.1 ∈ b66g_scalarBoundaries R t := by
  obtain ⟨S, v, h⟩ := b66g_split_exists s.2
  obtain ⟨h', hh', hsp⟩ := b66g_scalar_dual R t s.2 S v h.1 h.2.1 h.2.2 fun η hη => by
    rw [← b66g_res_eq h hη]
    exact LinearMap.congr_fun hs ⟨η, hη⟩
  apply Submodule.subset_span
  refine ⟨h', hh', ?_⟩
  funext a b x
  simp only [b66g_scalarBoundary]
  split_ifs with hx
  · exact hsp a b x hx.1 hx.2
  · exact (b66g_scalarCycles_spec R t s.2).2.1 a b x hx

variable (R t) in
/-- Holomorphic scalar cocycles onto their classes. -/
def b66g_piO : b66g_scalarCycles R t →ₗ[ℂ] b66g_H1O R t where
  toFun s := ⟨(b66g_scalarBoundaries R t).mkQ s.1, Submodule.mem_map_of_mem s.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem b66g_piO_surjective : Function.Surjective (b66g_piO R t) := by
  rintro ⟨c, hc⟩
  obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.1 hc
  exact ⟨⟨s, hs⟩, rfl⟩

theorem b66g_ker_piO_le : LinearMap.ker (b66g_piO R t) ≤ LinearMap.ker (b66g_rho R t) := by
  intro s hs
  have h0 : (b66g_scalarBoundaries R t).mkQ s.1 = 0 := congrArg Subtype.val hs
  exact b66g_rho_boundary ((Submodule.Quotient.mk_eq_zero _).1 h0)

variable (R t) in
/-- The residue pairing on the scalar `H¹`. -/
def b66g_rhoBar : b66g_H1O R t →ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 1) :=
  ((LinearMap.ker (b66g_piO R t)).liftQ (b66g_rho R t) b66g_ker_piO_le).comp
    ((b66g_piO R t).quotKerEquivOfSurjective b66g_piO_surjective).symm.toLinearMap

theorem b66g_rhoBar_injective : Function.Injective (b66g_rhoBar R t) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  obtain ⟨s, rfl⟩ := b66g_piO_surjective (R := R) (t := t) c
  have he : ((b66g_piO R t).quotKerEquivOfSurjective b66g_piO_surjective).symm
      (b66g_piO R t s) = Submodule.Quotient.mk s := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  have hr : b66g_rho R t s = 0 := by
    have := hc
    simp only [b66g_rhoBar, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
      Submodule.liftQ_apply] at this
    exact this
  apply Subtype.ext
  change (b66g_scalarBoundaries R t).mkQ s.1 = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact b66g_rho_ker hr

theorem b66g_forms_one_finiteDimensional : FiniteDimensional ℂ (b66g_forms R t 1) := by
  have := b3A_holForm_finiteDimensional (E := ℂ) (C := rf8_fibre R.C t) (by simp)
  exact Module.Finite.equiv (b66g_formEquiv R t).symm

theorem b66g_H1O_finrank_le :
    FiniteDimensional ℂ (b66g_H1O R t) ∧
      Module.finrank ℂ (b66g_H1O R t) ≤ Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) := by
  have := b66g_forms_one_finiteDimensional (R := R) (t := t)
  have hfin : FiniteDimensional ℂ (b66g_H1O R t) :=
    Module.Finite.of_injective (b66g_rhoBar R t) b66g_rhoBar_injective
  refine ⟨hfin, ?_⟩
  have h1 := LinearMap.finrank_le_finrank_of_injective (b66g_rhoBar_injective (R := R) (t := t))
  rw [Subspace.dual_finrank_eq, (b66g_formEquiv R t).finrank_eq] at h1
  exact h1

end B66gH1ODim

end HodgeLean.Foundations.Program

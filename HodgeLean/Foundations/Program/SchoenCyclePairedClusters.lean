import HodgeLean.Foundations.Program.SchoenCyclePairedLocalPolynomial

/-! # Simultaneous adjusted divisor clusters -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable (hE : Module.finrank ℂ E = 1) {s k : ℕ}
  (forms : Fin s → b4c_MeroForm E C hE) (x : Fin s → C)
  (hres : ∀ i j, b4c_res (hE := hE) (forms i) (x j) = if i = j then 1 else 0)
  (y : Fin (2 * s) → C) (hy : Function.Injective y)
  (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (forms i) p) 0)
  (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (forms i) p) 0)
  (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * s)
include hres hy horder hout hgenus
theorem s2e_paired_divisor_local_tuple_le
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (θ : (b3_HolForm E C × (Fin s → ℂ))) (hθ : θ ≠ 0)
    (p : C) (r : ℝ)
    (ht : ∀ w ∈ Metric.ball (0 : ℂ) r,
      extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w ∈ (extChartAt 𝓘(ℂ, E) p).target)
    {d : ℕ} (z : Fin d → ℂ) (hz : ∀ i, z i ∈ Metric.ball (0 : ℂ) r)
    (hm : ∀ w ∈ Metric.ball (0 : ℂ) r,
      (Fintype.card {i : Fin d // z i = w} : ℤ) = s2e_adjustedDifferentialDivisor hE forms y θ
        ((extChartAt 𝓘(ℂ, E) p).symm (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w))) :
    (∑ i, Finsupp.single
      ((extChartAt 𝓘(ℂ, E) p).symm (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE (z i)))
      (1 : ℤ)) ≤ s2e_adjustedDifferentialDivisor hE forms y θ := by
  apply s2e_tuple_divisor_le_of_injective_coordinates _
    (s2e_adjustedDifferentialDivisor_effective hE forms x hres y hy horder hout θ hθ) (Metric.ball (0 : ℂ) r)
    (fun w => (extChartAt 𝓘(ℂ, E) p).symm
      (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w)) ?_ z hz
  · intro w hw
    exact le_of_eq (hm w hw)
  · intro u hu v hv huv
    have he := (extChartAt 𝓘(ℂ, E) p).symm.injOn (ht u hu) (ht v hv) huv
    exact (b4cov_lineEquiv hE).injective (add_left_cancel he)


theorem s2e_paired_divisor_eq_disjoint_local_tuples
    [T2Space C] [CompactSpace C] [ConnectedSpace C] {ι : Type} [Fintype ι]
    (θ : (b3_HolForm E C × (Fin s → ℂ))) (hθ : θ ≠ 0)
    (p : ι → C) (r : ι → ℝ) (d : ι → ℕ) (z : (i : ι) → Fin (d i) → ℂ)
    (ht : ∀ i w, w ∈ Metric.ball (0 : ℂ) (r i) →
      extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w ∈
        (extChartAt 𝓘(ℂ, E) (p i)).target)
    (hz : ∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i))
    (hm : ∀ i w, w ∈ Metric.ball (0 : ℂ) (r i) →
      (Fintype.card {j : Fin (d i) // z i j = w} : ℤ) = s2e_adjustedDifferentialDivisor hE forms y θ
        ((extChartAt 𝓘(ℂ, E) (p i)).symm
          (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)))
    (hd : b4c_deg (s2e_adjustedDifferentialDivisor hE forms y θ) = ((∑ i, d i : ℕ) : ℤ))
    (hdis : Pairwise (fun i j => Disjoint
      ((fun w => (extChartAt 𝓘(ℂ, E) (p i)).symm
        (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)) '' Metric.ball 0 (r i))
      ((fun w => (extChartAt 𝓘(ℂ, E) (p j)).symm
        (extChartAt 𝓘(ℂ, E) (p j) (p j) + b4cov_lineEquiv hE w)) '' Metric.ball 0 (r j)))) :
    s2e_adjustedDifferentialDivisor hE forms y θ = ∑ i, ∑ j, Finsupp.single
      ((extChartAt 𝓘(ℂ, E) (p i)).symm
        (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE (z i j))) (1 : ℤ) := by
  classical
  let g := fun i w => (extChartAt 𝓘(ℂ, E) (p i)).symm
    (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)
  have hsub (i : ι) : ↑(∑ j, Finsupp.single (g i (z i j)) (1 : ℤ)).support ⊆
      g i '' Metric.ball 0 (r i) := by
    intro x hx
    by_contra hn
    have hne : ∀ j, g i (z i j) ≠ x := fun j he => hn ⟨z i j, hz i j, he⟩
    have hzero : (∑ j, Finsupp.single (g i (z i j)) (1 : ℤ)) x = 0 := by
      simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
      exact Finset.sum_eq_zero (fun j _ => ite_eq_right (hne j))
    exact (Finsupp.mem_support_iff.mp hx) hzero
  apply s2e_effectiveDivisor_eq_cluster_sum _ (s2e_adjustedDifferentialDivisor_effective hE forms x hres y hy horder hout θ hθ)
    d hd (fun i j => g i (z i j))
  · intro i
    exact s2e_paired_divisor_local_tuple_le hE forms x hres y hy horder hout hgenus θ hθ (p i) (r i) (ht i) (z i) (hz i) (hm i)
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (hdis hij) (hsub i hx) (hsub j hy)


theorem s2e_pairedFamily_centred_local_polynomial
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    {n : ℕ} (b : Fin n → (b3_HolForm E C × (Fin s → ℂ)))
    (a : Fin n → ℂ) (hne : (∑ i, a i • b i : (b3_HolForm E C × (Fin s → ℂ))) ≠ 0)
    (p : C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (r δ : ℝ) (c : Fin d → (Fin n → ℂ) → ℂ),
      (d : ℤ) = s2e_adjustedDifferentialDivisor hE forms y (∑ i, a i • b i : (b3_HolForm E C × (Fin s → ℂ))) p ∧
      0 < r ∧ r < ε ∧ 0 < δ ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈
          (extChartAt 𝓘(ℂ, E) p).target) ∧
      (∀ j, AnalyticOnNhd ℂ (c j) (Metric.ball a δ)) ∧
      (∀ j, c j a = 0) ∧
      (∀ᶠ a' in 𝓝 a,
        (∑ i, a' i • b i : (b3_HolForm E C × (Fin s → ℂ))) ≠ 0 ∧
        (∀ z, HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a', z) = 0 →
          z ∈ Metric.ball (0 : ℂ) r) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) r, ∃ e : ℕ,
          analyticOrderAt
            (fun w => HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a', w)) z = e ∧
          (e : ℤ) = s2e_adjustedDifferentialDivisor hE forms y (∑ i, a' i • b i : (b3_HolForm E C × (Fin s → ℂ)))
            ((extChartAt 𝓘(ℂ, E) p).symm
              (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z))) := by
  obtain ⟨d, r, δ, c, hD, hr, hrε, hδ, ht, hc, hball⟩ :=
    s2e_paired_family_local_polynomial hE forms x hres y hy horder hout b a hne p hε
  have hnear : ∀ᶠ a' in 𝓝 a, a' ∈ Metric.ball a δ := Metric.ball_mem_nhds a hδ
  have hrest := (hnear.and
    (s2e_linear_family_eventually_ne_zero b a hne)).mono
      (fun a' ha' => And.intro ha'.2 (hball a' ha'.1 ha'.2))
  have hc0 : ∀ j, c j a = 0 := by
    apply s2e_monic_coefficients_zero_of_full_order c a
    obtain ⟨e, he, hdiv⟩ := hrest.self_of_nhds.2.2 0 (Metric.mem_ball_self hr)
    have heD : (e : ℤ) = (d : ℤ) := by
      simpa only [map_zero, add_zero, extChartAt_to_inv] using hdiv.trans
        (by simpa only [map_zero, add_zero, extChartAt_to_inv] using hD.symm)
    have hed : e = d := by exact_mod_cast heD
    have heval : (fun w => (monicPoly c a).eval w) =
        (fun w => HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a, w)) :=
      funext (spec_monicPoly_aux c a).2.2
    rw [heval, he, hed]
  exact ⟨d, r, δ, c, hD, hr, hrε, hδ, ht, hc, hc0, hrest⟩

/-- Centred local root tuples retain the actual nearby adjusted multiplicities. -/
theorem s2e_pairedFamily_centred_local_root_multiplicities
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    {n : ℕ} (b : Fin n → (b3_HolForm E C × (Fin s → ℂ)))
    (a : Fin n → ℂ) (hne : (∑ i, a i • b i : (b3_HolForm E C × (Fin s → ℂ))) ≠ 0)
    (p : C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (r δ : ℝ) (c : Fin d → (Fin n → ℂ) → ℂ),
      (d : ℤ) = s2e_adjustedDifferentialDivisor hE forms y (∑ i, a i • b i : (b3_HolForm E C × (Fin s → ℂ))) p ∧
      0 < r ∧ r < ε ∧ 0 < δ ∧
      (∀ w ∈ Metric.closedBall (0 : ℂ) r,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) p).target) ∧
      (∀ j, AnalyticOnNhd ℂ (c j) (Metric.ball a δ)) ∧
      (∀ j, c j a = 0) ∧
      ∀ᶠ a' in nhds a,
        (∑ i, a' i • b i : (b3_HolForm E C × (Fin s → ℂ))) ≠ 0 ∧
        ∀ z : Fin d → ℂ, monicPoly c a' = ∏ i, (Polynomial.X - Polynomial.C (z i)) →
          (∀ i, z i ∈ Metric.ball (0 : ℂ) r) ∧
          ∀ w ∈ Metric.ball (0 : ℂ) r,
            (Fintype.card {i : Fin d // z i = w} : ℤ) =
              s2e_adjustedDifferentialDivisor hE forms y (∑ i, a' i • b i : (b3_HolForm E C × (Fin s → ℂ)))
                ((extChartAt 𝓘(ℂ, E) p).symm
                  (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w)) := by
  obtain ⟨d, r, δ, c, hd, hr, hrε, hδ, ht, hc, hc0, he⟩ :=
    s2e_pairedFamily_centred_local_polynomial hE forms x hres y hy horder hout hgenus b a hne p hε
  refine ⟨d, r, δ, c, hd, hr, hrε, hδ, ht, hc, hc0, ?_⟩
  filter_upwards [he] with a' ha'
  refine ⟨ha'.1, fun z hz => ⟨?_, ?_⟩⟩
  · intro i
    apply ha'.2.1
    rw [← (spec_monicPoly_aux c a').2.2, hz]
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (z i))
  · intro w hw
    obtain ⟨m, hm, hdiv⟩ := ha'.2.2 w hw
    have hfun : (fun v => (monicPoly c a').eval v) =
        fun v => HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a', v) :=
      funext (spec_monicPoly_aux c a').2.2
    have hcount := s2e_rootTuple_analytic_order (monicPoly c a') z hz w
    rw [hfun, hm] at hcount
    have hnat : m = Fintype.card {i : Fin d // z i = w} := by exact_mod_cast hcount
    rw [← hnat]
    exact hdiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite adjusted clusters have simultaneous centred analytic polynomial presentations. -/
theorem s2e_pairedFamily_finite_centred_local_polynomials
    [T2Space C] [CompactSpace C] [ConnectedSpace C] {ι : Type} [Fintype ι]
    {n : ℕ} (b : Fin n → (b3_HolForm E C × (Fin s → ℂ)))
    (a : Fin n → ℂ) (hne : (∑ j, a j • b j : (b3_HolForm E C × (Fin s → ℂ))) ≠ 0)
    (p : ι → C) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ (d : ι → ℕ) (r δ : ι → ℝ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ),
      (∀ i, (d i : ℤ) = s2e_adjustedDifferentialDivisor hE forms y (∑ j, a j • b j : (b3_HolForm E C × (Fin s → ℂ))) (p i)) ∧
      (∀ i, 0 < r i ∧ r i < ε i ∧ 0 < δ i) ∧
      (∀ i w, w ∈ Metric.closedBall (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (p i)).target) ∧
      (∀ i j, AnalyticOnNhd ℂ (c i j) (Metric.ball a (δ i))) ∧
      (∀ i j, c i j a = 0) ∧
      ∀ᶠ a' in nhds a,
        (∑ j, a' j • b j : (b3_HolForm E C × (Fin s → ℂ))) ≠ 0 ∧
        ∀ i (z : Fin (d i) → ℂ),
          monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z j)) →
          (∀ j, z j ∈ Metric.ball (0 : ℂ) (r i)) ∧
          ∀ w ∈ Metric.ball (0 : ℂ) (r i),
            (Fintype.card {j : Fin (d i) // z j = w} : ℤ) =
              s2e_adjustedDifferentialDivisor hE forms y (∑ j, a' j • b j : (b3_HolForm E C × (Fin s → ℂ)))
                ((extChartAt 𝓘(ℂ, E) (p i)).symm
                  (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)) := by
  choose d r δ c hd hr hre hδ ht hc hc0 he using fun i =>
    s2e_pairedFamily_centred_local_root_multiplicities hE forms x hres y hy horder hout hgenus b a hne (p i) (hε i)
  refine ⟨d, r, δ, c, hd, fun i => ⟨hr i, hre i, hδ i⟩, ht, hc, hc0, ?_⟩
  filter_upwards [eventually_all.mpr he, s2e_linear_family_eventually_ne_zero b a hne]
    with a' ha' hn'
  exact ⟨hn', fun i => (ha' i).2⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Centred simultaneous polynomial clusters recover every nearby adjusted divisor. -/
theorem s2e_pairedFamily_centred_cluster_divisor_presentation
    [T2Space C] [CompactSpace C] [ConnectedSpace C] {ι : Type} [Fintype ι]
    {n : ℕ} (b : Fin n → (b3_HolForm E C × (Fin s → ℂ)))
    (a : Fin n → ℂ) (hne : (∑ j, a j • b j : (b3_HolForm E C × (Fin s → ℂ))) ≠ 0)
    (p : ι → C) (hp : Function.Injective p)
    (hsum : (∑ i, s2e_adjustedDifferentialDivisor hE forms y (∑ j, a j • b j : (b3_HolForm E C × (Fin s → ℂ))) (p i)) =
      b4c_deg (s2e_adjustedDifferentialDivisor hE forms y (∑ j, a j • b j : (b3_HolForm E C × (Fin s → ℂ))))) :
    ∃ (d : ι → ℕ) (r δ : ι → ℝ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ),
      (∀ i, (d i : ℤ) = s2e_adjustedDifferentialDivisor hE forms y (∑ j, a j • b j : (b3_HolForm E C × (Fin s → ℂ))) (p i)) ∧
      (∀ i, 0 < r i ∧ 0 < δ i) ∧
      (∀ i w, w ∈ Metric.closedBall (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (p i)).target) ∧
      (∀ i j, AnalyticOnNhd ℂ (c i j) (Metric.ball a (δ i))) ∧
      (∀ i j, c i j a = 0) ∧
      ∀ᶠ a' in nhds a,
        (∑ j, a' j • b j : (b3_HolForm E C × (Fin s → ℂ))) ≠ 0 ∧
        ∀ z : (i : ι) → Fin (d i) → ℂ,
          (∀ i, monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
          (∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i)) ∧
          s2e_adjustedDifferentialDivisor hE forms y (∑ j, a' j • b j : (b3_HolForm E C × (Fin s → ℂ))) =
            ∑ i, ∑ j, Finsupp.single
              ((extChartAt 𝓘(ℂ, E) (p i)).symm
                (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE (z i j))) (1 : ℤ) := by
  obtain ⟨ε, hε, _, hsep⟩ := s2e_curve_chart_discs_disjoint hE p hp
  obtain ⟨d, r, δ, c, hd, hr, ht, hc, hc0, he⟩ :=
    s2e_pairedFamily_finite_centred_local_polynomials hE forms x hres y hy horder hout hgenus b a hne p ε hε
  refine ⟨d, r, δ, c, hd, fun i => ⟨(hr i).1, (hr i).2.2⟩, ht, hc, hc0, ?_⟩
  filter_upwards [he] with a' ha'
  refine ⟨ha'.1, fun z hz => ?_⟩
  have hzi : ∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i) :=
    fun i => (ha'.2 i (z i) (hz i)).1
  refine ⟨hzi, ?_⟩
  have hdeg : b4c_deg (s2e_adjustedDifferentialDivisor hE forms y
      (∑ j, a' j • b j : (b3_HolForm E C × (Fin s → ℂ)))) = ((∑ i, d i : ℕ) : ℤ) := by
    rw [s2e_adjustedDifferentialDivisor_degree hE forms x hres y hgenus _ ha'.1,
      ← s2e_adjustedDifferentialDivisor_degree hE forms x hres y hgenus _ hne, ← hsum]
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => (hd i).symm)
  apply s2e_paired_divisor_eq_disjoint_local_tuples hE forms x hres y hy horder hout hgenus _ ha'.1 p r d z
    (fun i w hw => ht i w (Metric.ball_subset_closedBall hw)) hzi
    (fun i => (ha'.2 i (z i) (hz i)).2) hdeg
  intro i j hij
  exact (hsep hij).mono
    (Set.image_mono (Metric.ball_subset_ball (hr i).2.1.le))
    (Set.image_mono (Metric.ball_subset_ball (hr j).2.1.le))



theorem s2e_pairedFamily_centred_support_divisor_presentation
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    {n : ℕ} (b : Fin n → (b3_HolForm E C × (Fin s → ℂ)))
    (a : Fin n → ℂ) (hne : (∑ j, a j • b j : (b3_HolForm E C × (Fin s → ℂ))) ≠ 0) :
    let D := s2e_adjustedDifferentialDivisor hE forms y (∑ j, a j • b j : (b3_HolForm E C × (Fin s → ℂ)))
    ∃ (d : D.support → ℕ) (r δ : D.support → ℝ) (c : (i : D.support) → Fin (d i) → (Fin n → ℂ) → ℂ),
      (∀ i, (d i : ℤ) = s2e_adjustedDifferentialDivisor hE forms y (∑ j, a j • b j : (b3_HolForm E C × (Fin s → ℂ))) (i : C)) ∧
      (∀ i, 0 < r i ∧ 0 < δ i) ∧
      (∀ i w, w ∈ Metric.closedBall (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (i : C) (i : C) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (i : C)).target) ∧
      (∀ i j, AnalyticOnNhd ℂ (c i j) (Metric.ball a (δ i))) ∧
      (∀ i j, c i j a = 0) ∧
      ∀ᶠ a' in nhds a,
        (∑ j, a' j • b j : (b3_HolForm E C × (Fin s → ℂ))) ≠ 0 ∧
        ∀ z : (i : D.support) → Fin (d i) → ℂ,
          (∀ i, monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
          (∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i)) ∧
          s2e_adjustedDifferentialDivisor hE forms y (∑ j, a' j • b j : (b3_HolForm E C × (Fin s → ℂ))) =
            ∑ i : D.support, ∑ j : Fin (d i), Finsupp.single
              ((extChartAt 𝓘(ℂ, E) (i : C)).symm
                (extChartAt 𝓘(ℂ, E) (i : C) (i : C) + b4cov_lineEquiv hE (z i j))) (1 : ℤ) := by
  dsimp only
  let D := s2e_adjustedDifferentialDivisor hE forms y (∑ j, a j • b j : (b3_HolForm E C × (Fin s → ℂ)))
  apply s2e_pairedFamily_centred_cluster_divisor_presentation hE forms x hres y hy horder hout hgenus b a hne
    (fun i : D.support => (i : C)) Subtype.val_injective
  change (∑ i : D.support, D i) = b4c_deg D
  simp [b4c_deg, Finsupp.sum, Finset.sum_attach]


end HodgeLean.Foundations.Program

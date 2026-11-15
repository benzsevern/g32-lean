import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemPolynomial
import HodgeLean.Foundations.Program.G32Native.PairedResidualChartDivisors
import HodgeLean.Foundations.Program.G32Native.PairedResidualProjectiveSystem

/-! # Centred polynomial clusters of the full normalized differential system -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology
open HodgeLean.Adapters HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable (hE : Module.finrank ℂ E = 1) {r : ℕ}
  (y : Fin (2 * r) → C) (hy : Function.Injective y)
  (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
  (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
    (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q.val p) 0) ∧
    (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
    ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
include hy hW

/-- Centred full-system coefficients vanish to the exact adjusted multiplicity. -/
theorem residual_system_centred_local_polynomial
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    {n : ℕ} (b : Fin n → W)
    (a : Fin n → ℂ) (hne : (∑ i, a i • b i : W) ≠ 0)
    (p : C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (r δ : ℝ) (c : Fin d → (Fin n → ℂ) → ℂ),
      (d : ℤ) = (b4c_divForm (hE := hE) (∑ i, a i • b i : W).val + s2e_markedPoleDivisor y) p ∧
      0 < r ∧ r < ε ∧ 0 < δ ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈
          (extChartAt 𝓘(ℂ, E) p).target) ∧
      (∀ j, AnalyticOnNhd ℂ (c j) (Metric.ball a δ)) ∧
      (∀ j, c j a = 0) ∧
      (∀ᶠ a' in 𝓝 a,
        (∑ i, a' i • b i : W) ≠ 0 ∧
        (∀ z, HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a', z) = 0 →
          z ∈ Metric.ball (0 : ℂ) r) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) r, ∃ e : ℕ,
          analyticOrderAt
            (fun w => HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a', w)) z = e ∧
          (e : ℤ) = (b4c_divForm (hE := hE) (∑ i, a' i • b i : W).val + s2e_markedPoleDivisor y)
            ((extChartAt 𝓘(ℂ, E) p).symm
              (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z))) := by
  obtain ⟨d, r, δ, c, hD, hr, hrε, hδ, ht, hc, hball⟩ :=
    residual_system_local_polynomial hE y hy W hW b a hne p hε
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

#print axioms residual_system_centred_local_polynomial
/-- Local full-system root tuples retain their exact adjusted multiplicities. -/
theorem residual_system_centred_local_root_multiplicities
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    {n : ℕ} (b : Fin n → W)
    (a : Fin n → ℂ) (hne : (∑ i, a i • b i : W) ≠ 0)
    (p : C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (r δ : ℝ) (c : Fin d → (Fin n → ℂ) → ℂ),
      (d : ℤ) = (b4c_divForm (hE := hE) (∑ i, a i • b i : W).val + s2e_markedPoleDivisor y) p ∧
      0 < r ∧ r < ε ∧ 0 < δ ∧
      (∀ w ∈ Metric.closedBall (0 : ℂ) r,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) p).target) ∧
      (∀ j, AnalyticOnNhd ℂ (c j) (Metric.ball a δ)) ∧
      (∀ j, c j a = 0) ∧
      ∀ᶠ a' in nhds a,
        (∑ i, a' i • b i : W) ≠ 0 ∧
        ∀ z : Fin d → ℂ, monicPoly c a' = ∏ i, (Polynomial.X - Polynomial.C (z i)) →
          (∀ i, z i ∈ Metric.ball (0 : ℂ) r) ∧
          ∀ w ∈ Metric.ball (0 : ℂ) r,
            (Fintype.card {i : Fin d // z i = w} : ℤ) =
              (b4c_divForm (hE := hE) (∑ i, a' i • b i : W).val + s2e_markedPoleDivisor y)
                ((extChartAt 𝓘(ℂ, E) p).symm
                  (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w)) := by
  obtain ⟨d, r, δ, c, hd, hr, hrε, hδ, ht, hc, hc0, he⟩ :=
    residual_system_centred_local_polynomial hE y hy W hW b a hne p hε
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


#print axioms residual_system_centred_local_root_multiplicities
/-- Finite full-system clusters have simultaneous centred polynomial presentations. -/
theorem residual_system_finite_centred_local_polynomials
    [T2Space C] [CompactSpace C] [ConnectedSpace C] {ι : Type} [Fintype ι]
    {n : ℕ} (b : Fin n → W)
    (a : Fin n → ℂ) (hne : (∑ j, a j • b j : W) ≠ 0)
    (p : ι → C) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ (d : ι → ℕ) (r δ : ι → ℝ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ),
      (∀ i, (d i : ℤ) = (b4c_divForm (hE := hE) (∑ j, a j • b j : W).val + s2e_markedPoleDivisor y) (p i)) ∧
      (∀ i, 0 < r i ∧ r i < ε i ∧ 0 < δ i) ∧
      (∀ i w, w ∈ Metric.closedBall (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (p i)).target) ∧
      (∀ i j, AnalyticOnNhd ℂ (c i j) (Metric.ball a (δ i))) ∧
      (∀ i j, c i j a = 0) ∧
      ∀ᶠ a' in nhds a,
        (∑ j, a' j • b j : W) ≠ 0 ∧
        ∀ i (z : Fin (d i) → ℂ),
          monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z j)) →
          (∀ j, z j ∈ Metric.ball (0 : ℂ) (r i)) ∧
          ∀ w ∈ Metric.ball (0 : ℂ) (r i),
            (Fintype.card {j : Fin (d i) // z j = w} : ℤ) =
              (b4c_divForm (hE := hE) (∑ j, a' j • b j : W).val + s2e_markedPoleDivisor y)
                ((extChartAt 𝓘(ℂ, E) (p i)).symm
                  (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)) := by
  choose d r δ c hd hr hre hδ ht hc hc0 he using fun i =>
    residual_system_centred_local_root_multiplicities hE y hy W hW b a hne (p i) (hε i)
  refine ⟨d, r, δ, c, hd, fun i => ⟨hr i, hre i, hδ i⟩, ht, hc, hc0, ?_⟩
  filter_upwards [eventually_all.mpr he, s2e_linear_family_eventually_ne_zero b a hne]
    with a' ha' hn'
  exact ⟨hn', fun i => (ha' i).2⟩


#print axioms residual_system_finite_centred_local_polynomials
/-- Simultaneous full-system roots reconstruct nearby divisors with their multiplicities. -/
theorem residual_system_centred_cluster_divisor_presentation
    (k : ℕ)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    [T2Space C] [CompactSpace C] [ConnectedSpace C] {ι : Type} [Fintype ι]
    {n : ℕ} (b : Fin n → W)
    (a : Fin n → ℂ) (hne : (∑ j, a j • b j : W) ≠ 0)
    (p : ι → C) (hp : Function.Injective p)
    (hsum : (∑ i, (b4c_divForm (hE := hE) (∑ j, a j • b j : W).val + s2e_markedPoleDivisor y) (p i)) =
      b4c_deg ((b4c_divForm (hE := hE) (∑ j, a j • b j : W).val + s2e_markedPoleDivisor y))) :
    ∃ (d : ι → ℕ) (r δ : ι → ℝ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ),
      (∀ i, (d i : ℤ) = (b4c_divForm (hE := hE) (∑ j, a j • b j : W).val + s2e_markedPoleDivisor y) (p i)) ∧
      (∀ i, 0 < r i ∧ 0 < δ i) ∧
      (∀ i w, w ∈ Metric.closedBall (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (p i)).target) ∧
      (∀ i j, AnalyticOnNhd ℂ (c i j) (Metric.ball a (δ i))) ∧
      (∀ i j, c i j a = 0) ∧
      ∀ᶠ a' in nhds a,
        (∑ j, a' j • b j : W) ≠ 0 ∧
        ∀ z : (i : ι) → Fin (d i) → ℂ,
          (∀ i, monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
          (∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i)) ∧
          (b4c_divForm (hE := hE) (∑ j, a' j • b j : W).val + s2e_markedPoleDivisor y) =
            ∑ i, ∑ j, Finsupp.single
              ((extChartAt 𝓘(ℂ, E) (p i)).symm
                (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE (z i j))) (1 : ℤ) := by
  obtain ⟨ε, hε, _, hsep⟩ := s2e_curve_chart_discs_disjoint hE p hp
  obtain ⟨d, r, δ, c, hd, hr, ht, hc, hc0, he⟩ :=
    residual_system_finite_centred_local_polynomials hE y hy W hW b a hne p ε hε
  refine ⟨d, r, δ, c, hd, fun i => ⟨(hr i).1, (hr i).2.2⟩, ht, hc, hc0, ?_⟩
  filter_upwards [he] with a' ha'
  refine ⟨ha'.1, fun z hz => ?_⟩
  have hzi : ∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i) :=
    fun i => (ha'.2 i (z i) (hz i)).1
  refine ⟨hzi, ?_⟩
  have deg (v : W) (hv : v ≠ 0) :
      b4c_deg (b4c_divForm (hE := hE) v.val + s2e_markedPoleDivisor y) = (2 * k : ℕ) :=
    residualProjectiveDivisor_degree hE y W
      (fun q => ⟨(hW q).1, (hW q).2.2⟩) hgenus (Projectivization.mk ℂ v hv)
  have hdeg : b4c_deg (b4c_divForm (hE := hE) (∑ j, a' j • b j : W).val +
      s2e_markedPoleDivisor y) = ((∑ i, d i : ℕ) : ℤ) := by
    rw [deg _ ha'.1, ← deg _ hne, ← hsum]
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => (hd i).symm)
  apply residual_effective_divisor_eq_disjoint_chart_tuples hE _
    (residualProjectiveDivisor_effective hE y hy W hW
      (Projectivization.mk ℂ (∑ j, a' j • b j : W) ha'.1)) p r d z
    (fun i w hw => ht i w (Metric.ball_subset_closedBall hw)) hzi
    (fun i => (ha'.2 i (z i) (hz i)).2) hdeg
  intro i j hij
  exact (hsep hij).mono
    (Set.image_mono (Metric.ball_subset_ball (hr i).2.1.le))
    (Set.image_mono (Metric.ball_subset_ball (hr j).2.1.le))

#print axioms residual_system_centred_cluster_divisor_presentation
/-- Support-indexed full-system clusters recover every nearby adjusted divisor. -/
theorem residual_system_centred_support_divisor_presentation
    (k : ℕ)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    {n : ℕ} (b : Fin n → W)
    (a : Fin n → ℂ) (hne : (∑ j, a j • b j : W) ≠ 0) :
    let D := (b4c_divForm (hE := hE) (∑ j, a j • b j : W).val + s2e_markedPoleDivisor y)
    ∃ (d : D.support → ℕ) (r δ : D.support → ℝ) (c : (i : D.support) → Fin (d i) → (Fin n → ℂ) → ℂ),
      (∀ i, (d i : ℤ) = (b4c_divForm (hE := hE) (∑ j, a j • b j : W).val + s2e_markedPoleDivisor y) (i : C)) ∧
      (∀ i, 0 < r i ∧ 0 < δ i) ∧
      (∀ i w, w ∈ Metric.closedBall (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (i : C) (i : C) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (i : C)).target) ∧
      (∀ i j, AnalyticOnNhd ℂ (c i j) (Metric.ball a (δ i))) ∧
      (∀ i j, c i j a = 0) ∧
      ∀ᶠ a' in nhds a,
        (∑ j, a' j • b j : W) ≠ 0 ∧
        ∀ z : (i : D.support) → Fin (d i) → ℂ,
          (∀ i, monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
          (∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i)) ∧
          (b4c_divForm (hE := hE) (∑ j, a' j • b j : W).val + s2e_markedPoleDivisor y) =
            ∑ i : D.support, ∑ j : Fin (d i), Finsupp.single
              ((extChartAt 𝓘(ℂ, E) (i : C)).symm
                (extChartAt 𝓘(ℂ, E) (i : C) (i : C) + b4cov_lineEquiv hE (z i j))) (1 : ℤ) := by
  dsimp only
  let D := (b4c_divForm (hE := hE) (∑ j, a j • b j : W).val + s2e_markedPoleDivisor y)
  apply residual_system_centred_cluster_divisor_presentation hE y hy W hW k hgenus b a hne
    (fun i : D.support => (i : C)) Subtype.val_injective
  change (∑ i : D.support, D i) = b4c_deg D
  simp [b4c_deg, Finsupp.sum, Finset.sum_attach]

#print axioms residual_system_centred_support_divisor_presentation
end HodgeLean.Foundations.Program.G32Native

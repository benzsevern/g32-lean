import HodgeLean.Foundations.Curves.AbelTheorem.ComplexCutoffDerivative
import HodgeLean.Foundations.Curves.AbelTheorem.WeightedLocalResidue
import HodgeLean.Foundations.Curves.AbelTheorem.RadialChartStokes
import HodgeLean.Foundations.Curves.AbelTheorem.RadialCutoffNeighborhoods
import HodgeLean.Foundations.Curves.AbelTheorem.LocalizedStokesComparison

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory Metric
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem complex_weighted_residue_stokes (h : Module.finrank ℂ E = 1)
    (w : b4c_MeroForm E C h)
    (ho : ∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0)
    (G : C → ℂ) (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G)
    (hhol : ∀ x, meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0 < 0 →
      ∀ᶠ y in 𝓝 x, AnalyticAt ℂ (centeredScalar h G y) 0)
    (P : ℂ →L[ℝ] ℝ)
    (hβ : b3Forms_IsSmooth (complex_multiplier_wedge h G (b4c_residue_normalizedForm h w) P)) :
    b3Forms_integral (b4c_residue_basis h)
      (complex_multiplier_wedge h G (b4c_residue_normalizedForm h w) P) =
      -∑ x ∈ (b4c_residue_poles_finite h w).toFinset,
        P (2 * (Real.pi : ℂ) * Complex.I * (G x * b4c_res (hE := h) w x)) := by
  classical
  let s := (b4c_residue_poles_finite h w).toFinset
  let U : C → Set C := fun x => if x ∈ s then
    interior {y | AnalyticAt ℂ (centeredScalar h G y) 0} else Set.univ
  have hU : ∀ x, U x ∈ 𝓝 x := by
    intro x
    by_cases hx : x ∈ s
    · have he := hhol x ((b4c_residue_poles_finite h w).mem_toFinset.mp hx)
      simpa only [U, if_pos hx] using interior_mem_nhds.mpr he
    · simp only [U, if_neg hx, Filter.univ_mem]
  let f : C → ℂ → ℂ := fun x =>
    HurwitzPrymRR_loc h (b4c_residue_normalizedForm h w) x * centeredScalar h G x
  have hdata (x : C) : ∃ r > 0, x ∈ s →
      (∀ z : ℂ, ‖z‖ < r → z ≠ 0 → AnalyticAt ℂ (f x) z) ∧
      ∀ a b : ℝ, 0 < a → a < b → b < r →
        (∫ z : ℂ, (Complex.I * fderiv ℝ
          (fun y : ℂ => (b4c_residue_profile a b ‖y‖ : ℂ)) z 1 -
          fderiv ℝ (fun y : ℂ => (b4c_residue_profile a b ‖y‖ : ℂ)) z Complex.I) * f x z) =
          -(2 * (Real.pi : ℂ) * Complex.I * (G x * b4c_res (hE := h) w x)) := by
    by_cases hx : x ∈ s
    · obtain ⟨r, hr, hA, hL⟩ := weighted_meromorphic_local_data h w G x (ho x)
        ((hhol x ((b4c_residue_poles_finite h w).mem_toFinset.mp hx)).self_of_nhds)
      exact ⟨r, hr, fun _ => ⟨hA, hL⟩⟩
    · exact ⟨1, zero_lt_one, fun hs => False.elim (hx hs)⟩
  choose R hR hdata using hdata
  obtain ⟨a, b, hab, hχ, hχc, hχU, hχchart, hχone, hd, hball⟩ :=
    radial_cutoffs_in_neighborhoods h (s : Set C) s.finite_toSet U hU R hR
  let χ : C → C → ℝ := fun x ↦ b4c_residue_chartFunction h x
    (fun z ↦ b4c_residue_profile (a x) (b x) ‖z‖)
  let ψ : C → C → ℝ := fun x ↦ b4c_residue_chartFunction h x
    (fun z ↦ b4c_residue_profile (a x / 2) (a x) ‖z‖)
  let μ : C → ℝ := fun y ↦ 1 - ∑ i ∈ s, ψ i y
  have hψ : ∀ i ∈ s, ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ ℝ) ∞ (ψ i) := by
    intro i hi
    apply b4c_residue_chartFunction_smooth h i
    · exact b4c_residue_profile_radial_smooth (by positivity [ (hab i).1 ])
        (by linarith [(hab i).1])
    · exact b4c_residue_profile_radial_compact (by linarith [(hab i).1])
    · intro z hz
      apply hball i z
      have hzle : ‖z‖ ≤ a i := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          b4c_residue_profile_radial_support (by linarith [(hab i).1]) hz
      exact hzle.trans (hab i).2.1.le
  have hψone : ∀ i ∈ s, ψ i =ᶠ[nhds i] fun _ ↦ (1 : ℝ) := by
    intro i hi
    exact b4c_residue_chartFunction_one h i _
      (b4c_residue_profile_radial_one (by positivity [ (hab i).1 ])
        (by linarith [(hab i).1]))
  have hone : ∀ i ∈ s, ∀ y ∈ tsupport (ψ i), χ i y = 1 := by
    intro i hi
    exact b4c_residue_nested_cutoffs h i (hab i).1 (hab i).2.1 (hball i)
  have hsub : ∀ i ∈ s, tsupport (ψ i) ⊆ tsupport (χ i) := by
    intro i hi y hy
    exact subset_tsupport _ (by simp [hone i hi y hy])
  have hψd : (s : Set C).PairwiseDisjoint (fun i ↦ tsupport (ψ i)) := by
    intro i hi j hj hij
    exact (hd hi hj hij).mono (hsub i hi) (hsub j hj)
  have hμ : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ μ :=
    contMDiff_const.sub (ContMDiff.sum hψ)
  have hpoles : ∀ x, meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0 < 0 →
      μ =ᶠ[nhds x] 0 := by
    intro x hx
    apply b4c_residue_cutoff_vanishes s ψ hψone hψd
    exact (b4c_residue_poles_finite h w).mem_toFinset.mpr hx
  let θ : TangentBundle 𝓘(ℂ, E) C → ℂ :=
    fun v => G v.proj * ((μ v.proj : ℂ) * b4c_residue_normalizedForm h w v)
  have hθ : HurwitzPrymRR_IsLinear θ := by
    intro x c v v'
    change G x * ((μ x : ℂ) * _) = c * (G x * ((μ x : ℂ) * _)) + G x * ((μ x : ℂ) * _)
    rw [b4c_residue_normalizedForm_linear h w]
    ring
  have hs := complex_cutoff_coefficient_smooth h w μ hμ hpoles G hG
  let α := b4c_residue_realForm h θ P
  let β := complex_multiplier_wedge h G (b4c_residue_normalizedForm h w) P
  have hα : b3Forms_IsSmooth α := b4c_residue_realForm_smooth h θ hθ P hs
  have hz : ∀ i ∈ s, ∀ y ∈ tsupport (χ i), β y = 0 := by
    intro i hi y hy
    have hu := hχU i hy
    change y ∈ U i at hu
    simp only [U, if_pos hi] at hu
    have hyhol : y ∈ {y | AnalyticAt ℂ (centeredScalar h G y) 0} := interior_subset hu
    exact complex_multiplier_wedge_zero_of_analytic h G hG _
      (b4c_residue_normalizedForm_linear h w) P y hyhol
  have hpart : ∀ x, (b3Forms_d α - β) x ≠ 0 → ∑ i ∈ s, χ i x = 1 := by
    intro x hx
    apply b4c_residue_cutoff_partition s χ ψ hd hone
    by_contra hn
    have he : ∀ i ∈ s, ψ i =ᶠ[𝓝 x] 0 := by
      intro i hi
      apply notMem_tsupport_iff_eventuallyEq.mp
      exact fun hxi => hn (mem_iUnion₂.mpr ⟨i, hi, hxi⟩)
    have hμone : μ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      have hz : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, ψ i y = 0 := by
        simpa only [Filter.eventually_all_finset, Filter.EventuallyEq, Pi.zero_apply] using he
      filter_upwards [hz] with y hy
      simp only [μ, Finset.sum_eq_zero hy, sub_zero]
    have heq := complex_cutoff_derivative_of_constant_germ h w G hG μ hμ hpoles P x 1 hμone
    exact hx (by
      change b3Forms_d α x - β x = 0
      rw [heq, one_smul, sub_self])
  rw [integral_eq_neg_local_derivatives h α hα β hβ s χ (fun i _ => hχ i)
    (fun i _ => hχchart i) hpart hz]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hcoef : ∀ z : ℂ, chartAt E i i + b4cov_lineEquiv h z ∈ (chartAt E i).target →
      χ i ((chartAt E i).symm (chartAt E i i + b4cov_lineEquiv h z)) ≠ 0 →
      HurwitzPrymRR_loc h θ i =ᶠ[𝓝 z]
        fun u => (1 - (b4c_residue_profile (a i / 2) (a i) ‖u‖ : ℂ)) * f i u := by
    intro z ht hne
    have he := b4c_residue_coefficient_germ h w μ i (a i / 2) (a i) ht
      (b4c_residue_multiplier_germ s χ ψ hd hone hi (subset_tsupport _ hne))
    filter_upwards [he] with u hu
    change centeredScalar h G i u * HurwitzPrymRR_loc h
      (fun v => (μ v.proj : ℂ) * b4c_residue_normalizedForm h w v) i u = _
    rw [hu]
    dsimp only [f, Pi.mul_apply]
    ring
  have ha2 : 0 < a i / 2 := div_pos (hab i).1 (by norm_num)
  have haa : a i / 2 < a i := by linarith [(hab i).1]
  have haR : a i < R i := (hab i).2.1.trans (hab i).2.2
  have hLi := (hdata i hi).2 (a i / 2) (a i) ha2 haa haR
  simp_rw [b4c_residue_profile_density ha2 haa] at hLi
  exact radial_chart_integral_of_local_density h θ hθ hs i (hab i).1 (hab i).2.1
    (hball i) (f i) (fun z hz => (hdata i hi).1 z (hz.trans (hab i).2.2)) hcoef
    (G i * b4c_res (hE := h) w i) hLi P

end HodgeLean.Foundations.Curves.AbelTheorem

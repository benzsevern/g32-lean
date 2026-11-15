import HodgeLean.Foundations.Program.SchoenCycleSliceDivisors
import HodgeLean.Foundations.Program.SchoenCycleAnalyticFamily
import HodgeLean.Foundations.Program.SchoenCycleCanonicalFamily

/-! # Pole correction in linear differential families -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology Manifold
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable

/-- A finite family with a common simple-pole bound has a jointly analytic
corrected coefficient, even when some parameter coefficients vanish.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, divisors and linear systems. -/
theorem s2e_linear_simple_pole_family {n : ℕ} (f : Fin n → ℂ → ℂ)
    (hf : ∀ i, MeromorphicAt (f i) 0)
    (ho : ∀ i, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (f i) 0) :
    ∃ g : (Fin n → ℂ) × ℂ → ℂ,
      (∀ a, AnalyticAt ℂ g (a, 0)) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a, z * ∑ i, a i * f i z = g (a, z)) := by
  classical
  choose h hh he using fun i => s2e_simple_pole_analytic_extension (f i) (hf i) (ho i)
  refine ⟨fun az => ∑ i, az.1 i * h i az.2, ?_, ?_⟩
  · intro a
    apply Finset.analyticAt_fun_sum
    intro i hi
    have ha : AnalyticAt ℂ (fun az : (Fin n → ℂ) × ℂ => az.1 i) (a, 0) :=
      ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).comp
        (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)).analyticAt _
    exact ha.mul ((hh i).comp (f := fun az : (Fin n → ℂ) × ℂ => az.2) analyticAt_snd)
  · have he' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ i, z * f i z = h i z :=
      Filter.eventually_all.mpr he
    filter_upwards [he'] with z hz
    intro a
    simp only [Finset.mul_sum, ← hz, mul_left_comm]

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- In any finite linear parametrization, the actual paired family has a
jointly analytic coefficient after the fixed marked-point correction.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14. -/
theorem s2e_paired_family_pole_correction
    (hE : Module.finrank ℂ E = 1) {r n m : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin n → C)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (b : Fin m → b3_HolForm E C × (Fin r → ℂ)) (p : C) :
    ∃ g : (Fin m → ℂ) × ℂ → ℂ,
      (∀ a, AnalyticAt ℂ g (a, 0)) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a, (if p ∈ Set.range y then z else 1) *
        HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (∑ i, a i • b i)) p z =
          g (a, z)) := by
  classical
  let f := fun i => HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (b i)) p
  have heq (a : Fin m → ℂ) (z : ℂ) :
      HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (∑ i, a i • b i)) p z =
        ∑ i, a i * f i z := by
    simp only [map_sum, map_smul, HurwitzPrymRR_loc, b4cov_coef,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f]
  by_cases hp : p ∈ Set.range y
  · obtain ⟨g, hg, he⟩ := s2e_linear_simple_pole_family f
      (fun i => (s2e_pairedDifferentialLinear_simple_poles hE w horder
        (b i).1 (b i).2 p).1)
      (fun i => (s2e_pairedDifferentialLinear_simple_poles hE w horder
        (b i).1 (b i).2 p).2)
    refine ⟨g, hg, ?_⟩
    filter_upwards [he] with z hz
    intro a
    simpa only [ite_eq_left hp, heq] using hz a
  · refine ⟨fun az => ∑ i, az.1 i * f i az.2, ?_, ?_⟩
    · intro a
      apply Finset.analyticAt_fun_sum
      intro i hi
      have ha : AnalyticAt ℂ (fun az : (Fin m → ℂ) × ℂ => az.1 i) (a, 0) :=
        ((ContinuousLinearMap.proj i : (Fin m → ℂ) →L[ℂ] ℂ).comp
          (ContinuousLinearMap.fst ℂ (Fin m → ℂ) ℂ)).analyticAt _
      have hf : AnalyticAt ℂ (f i) 0 :=
        s2e_pairedDifferentialLinear_analyticAt hE w (b i).1 (b i).2 p
          (fun j => hout j p hp)
      have hc : AnalyticAt ℂ (fun az : (Fin m → ℂ) × ℂ => f i az.2) (a, 0) :=
        AnalyticAt.comp (g := f i) (f := fun az : (Fin m → ℂ) × ℂ => az.2) hf
          (analyticAt_snd (𝕜 := ℂ) (p := (a, 0)))
      exact ha.mul hc
    · exact Filter.Eventually.of_forall (fun z a => by
        simp only [ite_eq_right hp, one_mul, heq])

/-- The analytic order of any pole-corrected coefficient equals the adjusted
multiplicity, with no nonvanishing-residue premise.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, divisors and linear systems. -/
theorem s2e_pole_corrected_order
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r n : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin n → C) (hy : Function.Injective y)
    (θ : b3_HolForm E C) (a : Fin r → ℂ) (hv : (θ, a) ≠ 0) (p : C)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (he : (fun z => (if p ∈ Set.range y then z else 1) *
      HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (θ, a)) p z)
        =ᶠ[𝓝[≠] 0] g) :
    ∃ d : ℕ, analyticOrderAt g 0 = d ∧
      (d : ℤ) = s2e_adjustedDifferentialDivisor hE w y (θ, a) p := by
  classical
  have hd := s2e_pairedDifferentialLinear_divisor_order hE w x hres θ a hv p
  have hm := (s2e_pairedDifferentialLinear_isMeroForm hE w θ a).2 p
  have hord : meromorphicOrderAt g 0 =
      ((s2e_adjustedDifferentialDivisor hE w y (θ, a) p : ℤ) : WithTop ℤ) := by
    rw [← meromorphicOrderAt_congr he]
    by_cases hp : p ∈ Set.range y
    · have hp' := hp
      obtain ⟨j, hj⟩ := hp'
      have hmark : s2e_markedPoleDivisor y p = 1 := by
        rw [← hj, s2e_markedPoleDivisor_apply_of_injective y hy]
      simp only [ite_eq_left hp]
      change meromorphicOrderAt ((id : ℂ → ℂ) *
        HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (θ, a)) p) 0 = _
      rw [meromorphicOrderAt_mul analyticAt_id.meromorphicAt hm, meromorphicOrderAt_id,
        ← hd]
      simp only [s2e_adjustedDifferentialDivisor, Finsupp.add_apply, hmark,
        WithTop.coe_add, WithTop.coe_one]
      exact add_comm _ _
    · simp only [ite_eq_right hp, one_mul]
      rw [← hd]
      simp only [s2e_adjustedDifferentialDivisor, Finsupp.add_apply,
        s2e_markedPoleDivisor_apply_outside y p hp, add_zero]
  have hn : analyticOrderAt g 0 ≠ ⊤ := by
    intro ht
    have hh := hg.meromorphicOrderAt_eq
    rw [ht, ENat.map_top, hord] at hh
    exact WithTop.coe_ne_top hh
  obtain ⟨d, hd'⟩ := ENat.ne_top_iff_exists.mp hn
  refine ⟨d, hd'.symm, ?_⟩
  rw [hg.meromorphicOrderAt_eq, ← hd', ENat.map_natCast] at hord
  exact_mod_cast hord

/-- Within a chart containing no other marked point, the corrected coefficient
has the adjusted multiplicity at each chart point where it is analytic.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, divisors and linear systems. -/
theorem s2e_pole_corrected_chart_order
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r n : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin n → C) (hy : Function.Injective y)
    (v : b3_HolForm E C × (Fin r → ℂ)) (hv : v ≠ 0) (p : C) (z : ℂ)
    (ht : extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈
      (extChartAt 𝓘(ℂ, E) p).target)
    (haway : z ≠ 0 → (extChartAt 𝓘(ℂ, E) p).symm
      (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z) ∉ Set.range y)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g z)
    (he : (fun ζ => (if p ∈ Set.range y then ζ else 1) *
      HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w v) p ζ)
        =ᶠ[𝓝[≠] z] g) :
    ∃ d : ℕ, analyticOrderAt g z = d ∧ (d : ℤ) =
      s2e_adjustedDifferentialDivisor hE w y v
        ((extChartAt 𝓘(ℂ, E) p).symm
          (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z)) := by
  classical
  by_cases hz : z = 0
  · subst z
    simpa only [map_zero, add_zero, extChartAt_to_inv] using
      s2e_pole_corrected_order hE w x hres y hy v.1 v.2 hv p g hg he
  let q := (extChartAt 𝓘(ℂ, E) p).symm
    (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z)
  have hq : q ∈ (extChartAt 𝓘(ℂ, E) p).source :=
    (extChartAt 𝓘(ℂ, E) p).map_target ht
  have hcoord : (b4cov_lineEquiv hE).symm
      (extChartAt 𝓘(ℂ, E) p q - extChartAt 𝓘(ℂ, E) p p) = z := by
    rw [(extChartAt 𝓘(ℂ, E) p).right_inv ht, add_sub_cancel_left,
      ContinuousLinearEquiv.symm_apply_apply]
  have hc := HurwitzPrymRR_ord_chart hE
    (s2e_pairedDifferentialLinear hE w v)
    (s2e_pairedDifferentialLinear_fibre_linear hE w v.1 v.2) p q hq
  rw [hcoord] at hc
  have hd := s2e_pairedDifferentialLinear_divisor_order hE w x hres v.1 v.2 hv q
  have hord : meromorphicOrderAt g z =
      ((s2e_adjustedDifferentialDivisor hE w y v q : ℤ) : WithTop ℤ) := by
    rw [← meromorphicOrderAt_congr he]
    have he' : meromorphicOrderAt (fun ζ => (if p ∈ Set.range y then ζ else 1) *
        HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w v) p ζ) z =
        meromorphicOrderAt (HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w v) p) z := by
      by_cases hp : p ∈ Set.range y
      · simp only [ite_eq_left hp]
        exact meromorphicOrderAt_mul_of_ne_zero analyticAt_id hz
      · simp only [ite_eq_right hp, one_mul]
    rw [he', ← hc, ← hd]
    simp only [s2e_adjustedDifferentialDivisor, Finsupp.add_apply,
      s2e_markedPoleDivisor_apply_outside y q (haway hz), add_zero]
  have hn : analyticOrderAt g z ≠ ⊤ := by
    intro ht'
    have hh := hg.meromorphicOrderAt_eq
    rw [ht', ENat.map_top, hord] at hh
    exact WithTop.coe_ne_top hh
  obtain ⟨d, hd'⟩ := ENat.ne_top_iff_exists.mp hn
  refine ⟨d, hd'.symm, ?_⟩
  rw [hg.meromorphicOrderAt_eq, ← hd', ENat.map_natCast] at hord
  exact_mod_cast hord

end HodgeLean.Foundations.Program

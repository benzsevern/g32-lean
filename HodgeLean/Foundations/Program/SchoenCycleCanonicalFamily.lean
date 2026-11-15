import HodgeLean.Foundations.Program.SchoenCycleCanonicalDivisors
import Mathlib.Analysis.Calculus.ImplicitContDiff
import HodgeLean.Foundations.AnalyticDivisorAlgebraic4
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceFinite

/-! # Local canonical differential families
Centred coefficients of actual holomorphic differentials vary analytically with their parameters.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The actual centred coefficient of a linear family of holomorphic differentials. -/
def s2e_holomorphicCoefficientFamily
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C) (p : C)
    (az : (Fin n → ℂ) × ℂ) : ℂ :=
  ∑ i, az.1 i * HurwitzPrymRR_loc hE (b i) p az.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The parameter equation is the coefficient of the corresponding actual differential. -/
theorem s2e_holomorphicCoefficientFamily_eq_loc
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C) (p : C)
    (az : (Fin n → ℂ) × ℂ) :
    s2e_holomorphicCoefficientFamily hE b p az =
      HurwitzPrymRR_loc hE (∑ i, az.1 i • b i : b3_HolForm E C) p az.2 := by
  classical
  simp only [s2e_holomorphicCoefficientFamily, HurwitzPrymRR_loc, b4cov_coef,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual coefficient equation is jointly analytic in parameters and the curve coordinate. -/
theorem s2e_holomorphicCoefficientFamily_analyticAt
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (p : C) (a : Fin n → ℂ) :
    AnalyticAt ℂ (s2e_holomorphicCoefficientFamily hE b p) (a, 0) := by
  classical
  apply Finset.analyticAt_fun_sum
  intro i hi
  have hcoef : AnalyticAt ℂ (fun az : (Fin n → ℂ) × ℂ => az.1 i) (a, 0) := by
    exact ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)).analyticAt (a, 0)
  have hloc : AnalyticAt ℂ (HurwitzPrymRR_loc hE (b i).val p) 0 :=
    RiemannRochEichler_loc_analytic hE (b i) p
  exact hcoef.mul (AnalyticAt.comp
    (f := fun az : (Fin n → ℂ) × ℂ => az.2)
    (g := HurwitzPrymRR_loc hE (b i).val p) hloc
    ((ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).analyticAt (a, 0)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The vertical derivative of the family is the derivative of its actual differential. -/
theorem s2e_holomorphicCoefficientFamily_vertical
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (p : C) (a : Fin n → ℂ) :
    fderiv ℂ (s2e_holomorphicCoefficientFamily hE b p) (a, 0) ∘L
        ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (deriv (HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) p) 0) := by
  have hins : HasFDerivAt (fun z : ℂ => (a, z))
      (ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ) 0 :=
    (hasFDerivAt_const a 0).prodMk (hasFDerivAt_id 0)
  have hc := (s2e_holomorphicCoefficientFamily_analyticAt hE b p a).differentiableAt.hasFDerivAt.comp 0 hins
  have he : (fun z => s2e_holomorphicCoefficientFamily hE b p (a, z)) =
      HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) p := by
    funext z
    exact s2e_holomorphicCoefficientFamily_eq_loc hE b p (a, z)
  have hd := (RiemannRochEichler_loc_analytic hE (∑ i, a i • b i) p).differentiableAt.hasDerivAt
  have hc' : HasFDerivAt
      (HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) p)
      (fderiv ℂ (s2e_holomorphicCoefficientFamily hE b p) (a, 0) ∘L
        ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ) 0 := by
    simpa only [Function.comp_def, he] using hc
  exact hc'.unique hd.hasFDerivAt

/-- A simple zero makes the vertical derivative of the actual family invertible. -/
theorem s2e_holomorphicCoefficientFamily_vertical_isInvertible
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (p : C) (a : Fin n → ℂ)
    (hsimple : deriv (HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) p) 0 ≠ 0) :
    (fderiv ℂ (s2e_holomorphicCoefficientFamily hE b p) (a, 0) ∘L
      ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ).IsInvertible := by
  rw [s2e_holomorphicCoefficientFamily_vertical]
  let d := deriv (HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) p) 0
  have hd : d ≠ 0 := hsimple
  change (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).IsInvertible
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d⁻¹)
  · ext
    simp [hd]
  · ext
    simp [hd]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A simple canonical zero has an analytic parameter branch with local uniqueness. -/
theorem s2e_holomorphicFamily_simple_zero_branch
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (p : C) (a : Fin n → ℂ)
    (hzero : HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) p 0 = 0)
    (hsimple : deriv (HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) p) 0 ≠ 0) :
    ∃ z : (Fin n → ℂ) → ℂ,
      AnalyticAt ℂ z a ∧ z a = 0 ∧
      (∀ᶠ a' in 𝓝 a,
        HurwitzPrymRR_loc hE (∑ i, a' i • b i : b3_HolForm E C) p (z a') = 0) ∧
      (∀ᶠ az : (Fin n → ℂ) × ℂ in 𝓝 (a, 0),
        HurwitzPrymRR_loc hE (∑ i, az.1 i • b i : b3_HolForm E C) p az.2 = 0 ↔
          z az.1 = az.2) := by
  let hc : ContDiffAt ℂ ω (s2e_holomorphicCoefficientFamily hE b p) (a, 0) :=
    (s2e_holomorphicCoefficientFamily_analyticAt hE b p a).contDiffAt
  let hi := s2e_holomorphicCoefficientFamily_vertical_isInvertible hE b p a hsimple
  let z := hc.implicitFunction (by simp) hi
  have hz : s2e_holomorphicCoefficientFamily hE b p (a, 0) = 0 :=
    (s2e_holomorphicCoefficientFamily_eq_loc hE b p (a, 0)).trans hzero
  refine ⟨z, (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt,
    hc.implicitFunction_apply_self (by simp) hi, ?_, ?_⟩
  · simpa only [hz, s2e_holomorphicCoefficientFamily_eq_loc] using
      hc.eventually_apply_implicitFunction (by simp) hi
  · simpa only [hz, s2e_holomorphicCoefficientFamily_eq_loc] using
      hc.eventually_apply_eq_iff_implicitFunction (by simp) hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The implicit simple zero defines an actual holomorphic moving point of the curve. -/
theorem s2e_holomorphicFamily_simple_zero_point
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (p : C) (a : Fin n → ℂ)
    (hzero : HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) p 0 = 0)
    (hsimple : deriv (HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) p) 0 ≠ 0) :
    ∃ (z : (Fin n → ℂ) → ℂ) (x : (Fin n → ℂ) → C),
      AnalyticAt ℂ z a ∧ z a = 0 ∧
      ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, E) ω x a ∧ x a = p ∧
      (∀ a', x a' = (extChartAt 𝓘(ℂ, E) p).symm
        (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE (z a'))) ∧
      (∀ᶠ a' in 𝓝 a,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE (z a') ∈
          (extChartAt 𝓘(ℂ, E) p).target ∧
        HurwitzPrymRR_loc hE (∑ i, a' i • b i : b3_HolForm E C) p (z a') = 0) := by
  obtain ⟨z, hz, hza, heq, _⟩ :=
    s2e_holomorphicFamily_simple_zero_branch hE b p a hzero hsimple
  let A : (Fin n → ℂ) → E := fun a' =>
    extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE (z a')
  have hA : ContDiffAt ℂ ω A a :=
    contDiffAt_const.add ((b4cov_lineEquiv hE).contDiff.contDiffAt.comp a hz.contDiffAt)
  have hAa : A a = extChartAt 𝓘(ℂ, E) p p := by
    simp only [A, hza, map_zero, add_zero]
  have ht : A a ∈ (extChartAt 𝓘(ℂ, E) p).target := by
    rw [hAa]
    exact mem_extChartAt_target p
  have hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω
      (extChartAt 𝓘(ℂ, E) p).symm (A a) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds ht)
  refine ⟨z, (extChartAt 𝓘(ℂ, E) p).symm ∘ A, hz, hza,
    hi.comp a hA.contMDiffAt, ?_, fun _ => rfl, ?_⟩
  · change (extChartAt 𝓘(ℂ, E) p).symm (A a) = p
    rw [hAa]
    exact extChartAt_to_inv p
  · exact (hA.continuousAt.eventually
      ((isOpen_extChartAt_target p).mem_nhds ht)).and heq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Vanishing of a chart coefficient means vanishing of the actual cotangent fibre. -/
theorem s2e_holomorphic_coefficient_zero_iff_fibre_zero
    (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) (p : C) (z : ℂ)
    (ht : extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈
      (extChartAt 𝓘(ℂ, E) p).target) :
    HurwitzPrymRR_loc hE θ p z = 0 ↔
      ∀ v : TangentSpace 𝓘(ℂ, E)
        ((extChartAt 𝓘(ℂ, E) p).symm
          (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z)),
        θ.val ⟨_, v⟩ = 0 := by
  let q := (extChartAt 𝓘(ℂ, E) p).symm
    (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z)
  let L := b4cov_lineEquiv hE
  have hq : q ∈ (extChartAt 𝓘(ℂ, E) p).source :=
    (extChartAt 𝓘(ℂ, E) p).map_target ht
  change θ.val ⟨q, b4cov_vec p q (L 1)⟩ = 0 ↔ ∀ v : TangentSpace 𝓘(ℂ, E) q, θ.val ⟨q, v⟩ = 0
  constructor
  · intro hz v
    let c := L.symm (trivializationAt E (TangentSpace 𝓘(ℂ, E)) p ⟨q, v⟩).2
    have hv : v = b4cov_vec p q (c • L 1) := by
      rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
      exact (b4cov_vec_triv p q hq v).symm
    have h0 : θ.val ⟨q, 0⟩ = 0 := by
      have hh := θ.property.2 q 1 0 0
      simp only [one_smul, add_zero, one_mul] at hh
      linear_combination -hh
    rw [hv, b4cov_vec_smul p q hq]
    have hh := θ.property.2 q c (b4cov_vec p q (L 1)) 0
    simpa only [add_zero, hz, h0, mul_zero] using hh
  · intro h
    exact h _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Positive canonical divisor multiplicity is exactly vanishing of the cotangent fibre. -/
theorem s2e_holomorphic_divisor_pos_iff_fibre_zero
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) (hθ : θ ≠ 0) (p : C) :
    0 < b4c_divForm (hE := hE) θ p ↔
      ∀ v : TangentSpace 𝓘(ℂ, E) p, θ.val ⟨p, v⟩ = 0 := by
  let w : b4c_MeroForm E C hE := ⟨θ, RiemannRochAna_hol_isMeroForm hE θ⟩
  have he := RiemannRochAna_coe_divForm_apply hE w
    (b4c_meroForm_orderSupport_finite_aux hE w) p
    (RiemannRochAna_hol_order_ne_top hE θ hθ p)
  have ha := RiemannRochEichler_loc_analytic hE θ p
  have hc : Tendsto (HurwitzPrymRR_loc hE θ p) (𝓝[≠] 0)
      (𝓝 (HurwitzPrymRR_loc hE θ p 0)) :=
    ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz : HurwitzPrymRR_loc hE θ p 0 = 0 ↔
      ∀ v : TangentSpace 𝓘(ℂ, E) p, θ.val ⟨p, v⟩ = 0 := by
    have hh := s2e_holomorphic_coefficient_zero_iff_fibre_zero hE θ p 0
      (by simpa only [map_zero, add_zero] using mem_extChartAt_target p)
    have hpt : (extChartAt 𝓘(ℂ, E) p).symm
        (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE 0) = p := by
      rw [map_zero, add_zero]
      exact extChartAt_to_inv p
    rw [hpt] at hh
    exact hh
  rw [← hz]
  constructor
  · intro hp
    have ho : 0 < meromorphicOrderAt (HurwitzPrymRR_loc hE θ p) 0 := by
      rw [← he]
      exact_mod_cast hp
    exact tendsto_nhds_unique hc (tendsto_zero_of_meromorphicOrderAt_pos ho)
  · intro hp
    have ho := (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp
      (by simpa only [hp] using hc)
    rw [← he] at ho
    exact_mod_cast ho

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A nonzero member of a finite holomorphic differential family stays nonzero nearby. -/
theorem s2e_holomorphicFamily_eventually_ne_zero
    {n : ℕ} (b : Fin n → b3_HolForm E C) (a : Fin n → ℂ)
    (ha : (∑ i, a i • b i : b3_HolForm E C) ≠ 0) :
    ∀ᶠ a' in 𝓝 a, (∑ i, a' i • b i : b3_HolForm E C) ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : TangentBundle 𝓘(ℂ, E) C,
      (∑ i, a i • b i : b3_HolForm E C).val v ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply ha
    exact Subtype.ext (funext hn)
  have hv' : (∑ i, a i * (b i).val v) ≠ 0 := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using hv
  have hc : ContinuousAt (fun a' : Fin n → ℂ => ∑ i, a' i * (b i).val v) a :=
    (continuous_finsetSum Finset.univ
      (fun i _ => (continuous_apply i).mul continuous_const)).continuousAt
  filter_upwards [hc.eventually (isOpen_compl_singleton.mem_nhds hv')] with a' ha'
  intro hz
  apply ha'
  change (∑ i, a' i * (b i).val v) = 0
  have hh := congrArg (fun θ : b3_HolForm E C => θ.val v) hz
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A simple zero moves holomorphically inside the support of the actual canonical divisor. -/
theorem s2e_holomorphicFamily_simple_zero_divisor
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (p : C) (a : Fin n → ℂ)
    (hzero : HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) p 0 = 0)
    (hsimple : deriv (HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) p) 0 ≠ 0) :
    ∃ x : (Fin n → ℂ) → C,
      ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, E) ω x a ∧ x a = p ∧
      (∀ᶠ a' in 𝓝 a,
        0 < b4c_divForm (hE := hE) (∑ i, a' i • b i : b3_HolForm E C) (x a')) := by
  obtain ⟨z, x, hz, hza, hx, hxa, hdef, heq⟩ :=
    s2e_holomorphicFamily_simple_zero_point hE b p a hzero hsimple
  have hn : (∑ i, a i • b i : b3_HolForm E C) ≠ 0 := by
    intro h
    apply hsimple
    rw [h]
    change deriv (0 : ℂ → ℂ) 0 = 0
    simp
  refine ⟨x, hx, hxa, ?_⟩
  filter_upwards [heq, s2e_holomorphicFamily_eventually_ne_zero b a hn] with a' ha' hn'
  apply (s2e_holomorphic_divisor_pos_iff_fibre_zero hE _ hn' (x a')).mpr
  have hh := (s2e_holomorphic_coefficient_zero_iff_fibre_zero hE
    (∑ i, a' i • b i : b3_HolForm E C) p (z a') ha'.1).mp ha'.2
  rw [← hdef a'] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Near a simple canonical divisor, holomorphic moving points enumerate the entire divisor. -/
theorem s2e_holomorphicFamily_simple_divisor_lift
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n N : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ i, a i • b i : b3_HolForm E C) ≠ 0)
    (p : Fin N → C) (hp : Function.Injective p)
    (hzero : ∀ j, HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) (p j) 0 = 0)
    (hsimple : ∀ j, deriv (HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) (p j)) 0 ≠ 0)
    (hdegree : (N : ℤ) = 2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2) :
    ∃ x : (Fin n → ℂ) → Fin N → C,
      (∀ j, ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, E) ω (fun a' => x a' j) a) ∧
      x a = p ∧
      (∀ᶠ a' in 𝓝 a,
        (∑ i, a' i • b i : b3_HolForm E C) ≠ 0 ∧
        b4c_divForm (hE := hE) (∑ i, a' i • b i : b3_HolForm E C) =
          ∑ j, Finsupp.single (x a' j) (1 : ℤ)) := by
  classical
  choose x hx hxa hpos using fun j =>
    s2e_holomorphicFamily_simple_zero_divisor hE b (p j) a (hzero j) (hsimple j)
  have hpair (i j : Fin N) (hij : i ≠ j) :
      ∀ᶠ a' in 𝓝 a, x i a' ≠ x j a' := by
    have hc := (hx i).continuousAt.prodMk (hx j).continuousAt
    have hmem : (x i a, x j a) ∈ {q : C × C | q.1 ≠ q.2} := by
      simp only [Set.mem_setOf_eq, hxa]
      exact fun h => hij (hp h)
    exact hc.eventually ((isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hmem)
  have hi := eventually_all.2 fun i => eventually_all.2 fun j =>
    eventually_all.2 fun hij : i ≠ j => hpair i j hij
  refine ⟨fun a' j => x j a', hx, funext hxa, ?_⟩
  filter_upwards [eventually_all.2 hpos, hi,
    s2e_holomorphicFamily_eventually_ne_zero b a hne] with a' hpos' hi' hn'
  have hinj : Function.Injective (fun j => x j a') := by
    intro i j he
    by_contra hij
    exact hi' i j hij he
  refine ⟨hn', s2e_effectiveDivisor_eq_distinct_tuple _
    (s2e_holomorphic_divisor_effective hE _ hn')
    ((s2e_holomorphic_divisor_degree hE _ hn').trans hdegree.symm)
    _ hinj hpos'⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The analytic order in a centred chart is the actual canonical divisor multiplicity. -/
theorem s2e_holomorphic_divisor_analytic_order
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) (hθ : θ ≠ 0) (p : C) :
    ∃ d : ℕ, analyticOrderAt (HurwitzPrymRR_loc hE θ p) 0 = d ∧
      (d : ℤ) = b4c_divForm (hE := hE) θ p := by
  have ha := RiemannRochEichler_loc_analytic hE θ p
  have hn : analyticOrderAt (HurwitzPrymRR_loc hE θ p) 0 ≠ ⊤ := by
    intro ht
    have hh := ha.meromorphicOrderAt_eq
    simp only [ht, ENat.map_top] at hh
    exact RiemannRochAna_hol_order_ne_top hE θ hθ p hh
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hn
  refine ⟨d, hd.symm, ?_⟩
  let w : b4c_MeroForm E C hE := ⟨θ, RiemannRochAna_hol_isMeroForm hE θ⟩
  have he := RiemannRochAna_coe_divForm_apply hE w
    (b4c_meroForm_orderSupport_finite_aux hE w) p
    (RiemannRochAna_hol_order_ne_top hE θ hθ p)
  change ((b4c_divForm (hE := hE) θ p : ℤ) : WithTop ℤ) =
    meromorphicOrderAt (HurwitzPrymRR_loc hE θ p) 0 at he
  rw [ha.meromorphicOrderAt_eq, ← hd, ENat.map_natCast] at he
  have hh : b4c_divForm (hE := hE) θ p = (d : ℤ) := by exact_mod_cast he
  exact hh.symm

/-- A holomorphic differential coefficient is analytic throughout its line chart. -/
theorem s2e_holomorphic_coefficient_analyticAt
    (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) (p : C) (z : ℂ)
    (ht : extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈
      (extChartAt 𝓘(ℂ, E) p).target) :
    AnalyticAt ℂ (HurwitzPrymRR_loc hE θ p) z := by
  have hf := b4cov_coef_analyticAt θ.val θ.property.1 p (b4cov_lineEquiv hE 1)
    (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z) ht
  have hg : AnalyticAt ℂ (fun w : ℂ =>
      extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w) z :=
    analyticAt_const.add ((b4cov_lineEquiv hE).toContinuousLinearMap.analyticAt z)
  exact AnalyticAt.comp (f := fun w : ℂ =>
    extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w)
    (g := b4cov_coef θ.val p (b4cov_lineEquiv hE 1)) hf hg

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Chart coefficient orders recover canonical multiplicities at every point of that chart. -/
theorem s2e_holomorphic_divisor_order_on_chart
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) (hθ : θ ≠ 0)
    (p : C) (z : ℂ)
    (ht : extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈
      (extChartAt 𝓘(ℂ, E) p).target) :
    ∃ d : ℕ, analyticOrderAt (HurwitzPrymRR_loc hE θ p) z = d ∧
      (d : ℤ) = b4c_divForm (hE := hE) θ
        ((extChartAt 𝓘(ℂ, E) p).symm
          (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z)) := by
  let q := (extChartAt 𝓘(ℂ, E) p).symm
    (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z)
  have hq : q ∈ (extChartAt 𝓘(ℂ, E) p).source :=
    (extChartAt 𝓘(ℂ, E) p).map_target ht
  have hm := HurwitzPrymRR_ord_chart hE θ.val θ.property.2 p q hq
  have hcoord : (b4cov_lineEquiv hE).symm
      (extChartAt 𝓘(ℂ, E) p q - extChartAt 𝓘(ℂ, E) p p) = z := by
    rw [(extChartAt 𝓘(ℂ, E) p).right_inv ht, add_sub_cancel_left,
      ContinuousLinearEquiv.symm_apply_apply]
  rw [hcoord] at hm
  have he : analyticOrderAt (HurwitzPrymRR_loc hE θ q) 0 =
      analyticOrderAt (HurwitzPrymRR_loc hE θ p) z := by
    apply WithTop.map_injective (f := fun m : ℕ => (m : ℤ)) (by intro i j h; change (i : ℤ) = (j : ℤ) at h; omega)
    change ENat.map (fun m : ℕ => (m : ℤ)) _ = ENat.map (fun m : ℕ => (m : ℤ)) _
    rw [← (RiemannRochEichler_loc_analytic hE θ q).meromorphicOrderAt_eq,
      ← (s2e_holomorphic_coefficient_analyticAt hE θ p z ht).meromorphicOrderAt_eq]
    exact hm
  obtain ⟨d, hd, hD⟩ := s2e_holomorphic_divisor_analytic_order hE θ hθ q
  exact ⟨d, he.symm.trans hd, hD⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual canonical multiplicities persist as zero counts in arbitrarily small chart discs. -/
theorem s2e_holomorphicFamily_local_zero_count
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ i, a i • b i : b3_HolForm E C) ≠ 0)
    (p : C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (r δ : ℝ), (d : ℤ) = b4c_divForm (hE := hE)
        (∑ i, a i • b i : b3_HolForm E C) p ∧
      0 < r ∧ r < ε ∧ 0 < δ ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈
          (extChartAt 𝓘(ℂ, E) p).target) ∧
      AnalyticOnNhd ℂ (s2e_holomorphicCoefficientFamily hE b p)
        (Metric.closedBall a δ ×ˢ Metric.closedBall (0 : ℂ) r) ∧
      (∀ a' ∈ Metric.closedBall a δ, ∀ z ∈ Metric.sphere (0 : ℂ) r,
        HurwitzPrymRR_loc hE (∑ i, a' i • b i : b3_HolForm E C) p z ≠ 0) ∧
      ∀ a' ∈ Metric.ball a δ,
        HodgeLean.Foundations.AnalyticDivisorAlgebraic4.zeroCount
          (HurwitzPrymRR_loc hE (∑ i, a' i • b i : b3_HolForm E C) p) 0 r = d := by
  obtain ⟨d, hd, hD⟩ := s2e_holomorphic_divisor_analytic_order hE _ hne p
  have haxis : (fun z => s2e_holomorphicCoefficientFamily hE b p (a, z)) =
      HurwitzPrymRR_loc hE (∑ i, a i • b i : b3_HolForm E C) p := by
    funext z
    exact s2e_holomorphicCoefficientFamily_eq_loc hE b p (a, z)
  have hline : ContinuousAt (fun z : ℂ =>
      extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z) 0 :=
    continuousAt_const.add (b4cov_lineEquiv hE).continuousAt
  have ht0 : extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE 0 ∈
      (extChartAt 𝓘(ℂ, E) p).target := by
    simpa only [map_zero, add_zero] using mem_extChartAt_target p
  obtain ⟨ρ, hρ, hρt⟩ := Metric.eventually_nhds_iff_ball.mp
    (hline.eventually ((isOpen_extChartAt_target p).mem_nhds ht0))
  have hord : analyticOrderAt
      (fun z => s2e_holomorphicCoefficientFamily hE b p (a, z)) 0 = d := by
    rw [haxis]
    exact hd
  obtain ⟨r, hr, hrε, δ, hδ, hf, hb, hc⟩ :=
    HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_exists_zeroCount_eq_order
      (s2e_holomorphicCoefficientFamily_analyticAt hE b p a) hord (lt_min hε hρ)
  refine ⟨d, r, δ, hD, hr, hrε.trans_le (min_le_left _ _), hδ, ?_, hf, ?_, ?_⟩
  · intro z hz
    exact hρt z ((Metric.mem_closedBall.mp hz).trans_lt
      (hrε.trans_le (min_le_right _ _)))
  · intro a' ha' z hz
    simpa only [s2e_holomorphicCoefficientFamily_eq_loc] using hb a' ha' z hz
  · intro a' ha'
    simpa only [s2e_holomorphicCoefficientFamily_eq_loc] using hc a' ha'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Weierstrass preparation of the actual differential family has its canonical multiplicity. -/
theorem s2e_holomorphicFamily_preparation
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ i, a i • b i : b3_HolForm E C) ≠ 0) (p : C) :
    ∃ d : ℕ, (d : ℤ) = b4c_divForm (hE := hE)
        (∑ i, a i • b i : b3_HolForm E C) p ∧
      ∃ u : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        ∃ c : Fin d → (Fin n → ℂ) → ℂ,
          (∀ j, AnalyticAt ℂ (c j) 0 ∧ c j 0 = 0) ∧
          (fun tz : (Fin n → ℂ) × ℂ => HurwitzPrymRR_loc hE
            (∑ i, (a + tz.1) i • b i : b3_HolForm E C) p tz.2) =ᶠ[𝓝 0]
            fun tz => u tz * HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c tz := by
  obtain ⟨d, hd, hD⟩ := s2e_holomorphic_divisor_analytic_order hE _ hne p
  have hs : AnalyticAt ℂ (fun tz : (Fin n → ℂ) × ℂ => (a + tz.1, tz.2)) 0 :=
    (analyticAt_const.add analyticAt_fst).prod analyticAt_snd
  have hf' : AnalyticAt ℂ (fun tz : (Fin n → ℂ) × ℂ =>
      s2e_holomorphicCoefficientFamily hE b p (a + tz.1, tz.2)) 0 :=
    (s2e_holomorphicCoefficientFamily_analyticAt hE b p a).comp_of_eq hs (by simp)
  have hf : AnalyticAt ℂ (fun tz : (Fin n → ℂ) × ℂ => HurwitzPrymRR_loc hE
      (∑ i, (a + tz.1) i • b i : b3_HolForm E C) p tz.2) 0 := by
    simpa only [s2e_holomorphicCoefficientFamily_eq_loc] using hf'
  refine ⟨d, hD, ?_⟩
  exact HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_weierstrass_preparation
    hf (by simpa only [add_zero] using hd)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Analytic local polynomials retain every actual canonical multiplicity, including repeated zeros. -/
theorem s2e_holomorphicFamily_local_polynomial
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ i, a i • b i : b3_HolForm E C) ≠ 0)
    (p : C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (r δ : ℝ) (c : Fin d → (Fin n → ℂ) → ℂ),
      (d : ℤ) = b4c_divForm (hE := hE) (∑ i, a i • b i : b3_HolForm E C) p ∧
      0 < r ∧ r < ε ∧ 0 < δ ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈
          (extChartAt 𝓘(ℂ, E) p).target) ∧
      (∀ j, AnalyticOnNhd ℂ (c j) (Metric.ball a δ)) ∧
      (∀ᶠ a' in 𝓝 a,
        (∑ i, a' i • b i : b3_HolForm E C) ≠ 0 ∧
        (∀ z, HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a', z) = 0 →
          z ∈ Metric.ball (0 : ℂ) r) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) r, ∃ e : ℕ,
          analyticOrderAt
            (fun w => HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a', w)) z = e ∧
          (e : ℤ) = b4c_divForm (hE := hE) (∑ i, a' i • b i : b3_HolForm E C)
            ((extChartAt 𝓘(ℂ, E) p).symm
              (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z))) := by
  obtain ⟨d, r, δ, hD, hr, hrε, hδ, ht, hf, hb, hcount⟩ :=
    s2e_holomorphicFamily_local_zero_count hE b a hne p hε
  have hbF : ∀ a' ∈ Metric.closedBall a δ, ∀ z ∈ Metric.sphere (0 : ℂ) r,
      s2e_holomorphicCoefficientFamily hE b p (a', z) ≠ 0 := by
    intro a' ha' z hz
    rw [s2e_holomorphicCoefficientFamily_eq_loc]
    exact hb a' ha' z hz
  have hc0 : HodgeLean.Foundations.AnalyticDivisorAlgebraic4.zeroCount
      (fun z => s2e_holomorphicCoefficientFamily hE b p (a, z)) 0 r = d := by
    simpa only [s2e_holomorphicCoefficientFamily_eq_loc] using
      hcount a (Metric.mem_ball_self hδ)
  obtain ⟨c, hc, hroots⟩ :=
    HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_exists_monicInLast_orders hf hbF hc0
  refine ⟨d, r, δ, c, hD, hr, hrε, hδ, ht, hc, ?_⟩
  filter_upwards [Metric.ball_mem_nhds a hδ,
    s2e_holomorphicFamily_eventually_ne_zero b a hne] with a' ha' hn'
  obtain ⟨hroot, horder⟩ := hroots a' ha'
  refine ⟨hn', hroot, ?_⟩
  intro z hz
  obtain ⟨e, he, hdiv⟩ := s2e_holomorphic_divisor_order_on_chart hE _ hn' p z
    (ht z (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz).le))
  refine ⟨e, ?_, hdiv⟩
  have heq : analyticOrderAt
      (fun w => HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a', w)) z =
        analyticOrderAt (HurwitzPrymRR_loc hE (∑ i, a' i • b i : b3_HolForm E C) p) z := by
    simpa only [s2e_holomorphicCoefficientFamily_eq_loc] using horder z hz
  exact heq.trans he

/-- A monic complex polynomial has an exact tuple presentation with every root multiplicity. -/
theorem s2e_monic_polynomial_exists_root_tuple {d : ℕ}
    (q : Polynomial ℂ) (hq : q.Monic) (hd : q.natDegree = d) :
    ∃ z : Fin d → ℂ, q = ∏ i, (Polynomial.X - Polynomial.C (z i)) := by
  classical
  have hs := IsAlgClosed.splits q
  have hc : q.roots.card = d := hs.natDegree_eq_card_roots.symm.trans hd
  obtain ⟨z, hz⟩ := s2e_sym_exists_enumeration (⟨q.roots, hc⟩ : Sym ℂ d)
  change (List.ofFn z : Multiset ℂ) = q.roots at hz
  refine ⟨z, ?_⟩
  rw [hs.eq_prod_roots_of_monic hq, ← hz]
  simp only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
    Function.comp_def, List.prod_ofFn]

/-- Exact root-tuple presentations of a nonzero polynomial form a finite fibre. -/
theorem s2e_polynomial_root_tuples_finite {d : ℕ}
    (q : Polynomial ℂ) (hq : q ≠ 0) :
    Set.Finite {z : Fin d → ℂ | q = ∏ i, (Polynomial.X - Polynomial.C (z i))} := by
  classical
  have hf : (Set.univ.pi (fun _ : Fin d => {w : ℂ | q.IsRoot w})).Finite :=
    Set.Finite.pi fun _ => Polynomial.finite_setOfPred_isRoot hq
  apply hf.subset
  intro z hz i hi
  change q.eval (z i) = 0
  rw [hz]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (z i))

/-- Coefficients of a root-tuple polynomial are analytic even where roots coincide. -/
theorem s2e_rootTuple_coefficient_analyticAt {d : ℕ} (k : ℕ) (z₀ : Fin d → ℂ) :
    AnalyticAt ℂ (fun z : Fin d → ℂ =>
      (∏ i, (Polynomial.X - Polynomial.C (z i))).coeff k) z₀ := by
  classical
  have hfactor (i : Fin d) (j : ℕ) : AnalyticAt ℂ
      (fun z : Fin d → ℂ => (Polynomial.X - Polynomial.C (z i)).coeff j) z₀ := by
    by_cases hj0 : j = 0
    · subst j
      have he : (fun z : Fin d → ℂ =>
          (Polynomial.X - Polynomial.C (z i)).coeff 0) = fun z => -z i := by
        funext z
        simp
      rw [he]
      exact ((ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ).analyticAt z₀).neg
    · by_cases hj1 : j = 1
      · subst j
        simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin d → ℂ => (1 : ℂ)) z₀)
      · have he : (fun z : Fin d → ℂ =>
            (Polynomial.X - Polynomial.C (z i)).coeff j) = fun _ => 0 := by
          funext z
          simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C, hj0, Ne.symm hj1]
        rw [he]
        exact analyticAt_const
  have hprod (s : Finset (Fin d)) : ∀ j, AnalyticAt ℂ
      (fun z : Fin d → ℂ => (∏ i ∈ s, (Polynomial.X - Polynomial.C (z i))).coeff j) z₀ := by
    induction s using Finset.induction_on with
    | empty =>
      intro j
      simp only [Finset.prod_empty]
      exact analyticAt_const
    | @insert i s hi ih =>
      intro j
      simp only [Finset.prod_insert hi, Polynomial.coeff_mul]
      apply Finset.analyticAt_fun_sum
      intro kl hkl
      exact (hfactor i kl.1).mul (ih kl.2)
  exact hprod Finset.univ k

/-- Root-tuple coefficient equations vary analytically in parameters and roots together. -/
theorem s2e_rootTuple_coefficient_equation_analyticAt {n d : ℕ}
    {c : (Fin n → ℂ) → ℂ} {a : Fin n → ℂ} (hc : AnalyticAt ℂ c a)
    (k : ℕ) (z : Fin d → ℂ) :
    AnalyticAt ℂ (fun az : (Fin n → ℂ) × (Fin d → ℂ) =>
      (∏ i, (Polynomial.X - Polynomial.C (az.2 i))).coeff k - c az.1) (a, z) := by
  have hl : AnalyticAt ℂ (fun az : (Fin n → ℂ) × (Fin d → ℂ) =>
      (∏ i, (Polynomial.X - Polynomial.C (az.2 i))).coeff k) (a, z) :=
    (s2e_rootTuple_coefficient_analyticAt k z).comp_of_eq
      ((ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin d → ℂ)).analyticAt (a, z)) rfl
  have hr : AnalyticAt ℂ (fun az : (Fin n → ℂ) × (Fin d → ℂ) => c az.1) (a, z) :=
    hc.comp_of_eq
      ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) (Fin d → ℂ)).analyticAt (a, z)) rfl
  exact hl.sub hr

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact root-tuple incidence is locally analytic and has finite fibres over nonzero polynomials. -/
theorem s2e_rootTuple_incidence_analytic_finite {n d : ℕ}
    (q : (Fin n → ℂ) → Polynomial ℂ) (a : Fin n → ℂ)
    (hdegree : ∀ a', (q a').natDegree ≤ d)
    (hq : ∀ k, AnalyticAt ℂ (fun a' => (q a').coeff k) a)
    (z : Fin d → ℂ) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {az : (Fin n → ℂ) × (Fin d → ℂ) |
        q az.1 = ∏ i, (Polynomial.X - Polynomial.C (az.2 i))} (a, z) ∧
      ∀ a', q a' ≠ 0 →
        Set.Finite {z' : Fin d → ℂ | q a' = ∏ i, (Polynomial.X - Polynomial.C (z' i))} := by
  classical
  let g (j : Fin (d + 1)) (az : (Fin n → ℂ) × (Fin d → ℂ)) : ℂ :=
    (∏ i, (Polynomial.X - Polynomial.C (az.2 i))).coeff j.val - (q az.1).coeff j.val
  have hg (j : Fin (d + 1)) : AnalyticAt ℂ (g j) (a, z) :=
    s2e_rootTuple_coefficient_equation_analyticAt (hq j.val) j.val z
  have hevent : ∀ᶠ az in 𝓝 (a, z), ∀ j : Fin (d + 1), AnalyticAt ℂ (g j) az :=
    eventually_all.2 fun j => (hg j).eventually_analyticAt
  obtain ⟨V, hVS, hV, haV⟩ := eventually_nhds_iff.mp hevent
  refine ⟨⟨V, hV, haV, Fin (d + 1), inferInstance, g,
    fun j y hy => hVS y hy j, ?_⟩, fun a' ha' => s2e_polynomial_root_tuples_finite (q a') ha'⟩
  intro az haz
  have hprod : (∏ i : Fin d, (Polynomial.X - Polynomial.C (az.2 i))).natDegree ≤ d := by
    calc
      _ ≤ ∑ i : Fin d, (Polynomial.X - Polynomial.C (az.2 i)).natDegree :=
        Polynomial.natDegree_prod_le Finset.univ (fun i => Polynomial.X - Polynomial.C (az.2 i))
      _ = d := by simp
  change q az.1 = (∏ i, (Polynomial.X - Polynomial.C (az.2 i))) ↔ ∀ j, g j az = 0
  rw [Polynomial.ext_iff_natDegree_le (hdegree az.1) hprod]
  constructor
  · intro h j
    exact sub_eq_zero.mpr (h j.val (by omega)).symm
  · intro h k hk
    exact (sub_eq_zero.mp (h ⟨k, by omega⟩)).symm

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An analytic monic family has a locally analytic root-tuple cover with nonempty finite fibres. -/
theorem s2e_monic_rootTuple_analytic_cover {n d : ℕ}
    (c : Fin d → (Fin n → ℂ) → ℂ) (a : Fin n → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) a) :
    (∀ z : Fin d → ℂ, HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {az : (Fin n → ℂ) × (Fin d → ℂ) |
        monicPoly c az.1 = ∏ i, (Polynomial.X - Polynomial.C (az.2 i))} (a, z)) ∧
      ∀ a', Set.Finite {z : Fin d → ℂ |
        monicPoly c a' = ∏ i, (Polynomial.X - Polynomial.C (z i))} ∧
        ∃ z : Fin d → ℂ, monicPoly c a' = ∏ i, (Polynomial.X - Polynomial.C (z i)) := by
  have hm (a' : Fin n → ℂ) := spec_monicPoly_aux c a'
  have hd (a' : Fin n → ℂ) : (monicPoly c a').natDegree ≤ d := by
    have hh := (hm a').2.1
    omega
  refine ⟨fun z => (s2e_rootTuple_incidence_analytic_finite (monicPoly c) a hd
    (gaga5b_analyticAt_coeff_monicPoly hc) z).1, ?_⟩
  intro a'
  exact ⟨s2e_polynomial_root_tuples_finite _ (hm a').1.ne_zero,
    s2e_monic_polynomial_exists_root_tuple _ (hm a').1 (hm a').2.1⟩

/-- Every exact root tuple of a nonzero polynomial is isolated, including repeated roots. -/
theorem s2e_polynomial_root_tuple_isolated {d : ℕ} (q : Polynomial ℂ) (hq : q ≠ 0)
    (z : Fin d → ℂ) (hz : q = ∏ i, (Polynomial.X - Polynomial.C (z i))) :
    ∃ r > 0, ∀ w : Fin d → ℂ, dist w z < r →
      q = ∏ i, (Polynomial.X - Polynomial.C (w i)) → w = z := by
  have hf := s2e_polynomial_root_tuples_finite q hq (d := d)
  obtain ⟨r, hr, he⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete hf.isDiscrete hz
  refine ⟨r, hr, fun w hw hq' => ?_⟩
  have hm : w ∈ Metric.ball z r ∩ {w : Fin d → ℂ |
      q = ∏ i, (Polynomial.X - Polynomial.C (w i))} := ⟨hw, hq'⟩
  rw [he] at hm
  exact hm

/-- Appending analytic evaluation coordinates to root incidence gives a locally analytic graph. -/
theorem s2e_rootTuple_graph_analytic {n d b : ℕ}
    (q : (Fin n → ℂ) → Polynomial ℂ) (a : Fin n → ℂ)
    (hdegree : ∀ a', (q a').natDegree ≤ d)
    (hq : ∀ k, AnalyticAt ℂ (fun a' => (q a').coeff k) a)
    (F : (Fin d → ℂ) → (Fin b → ℂ)) (z : Fin d → ℂ)
    (hF : AnalyticAt ℂ F z) (y : Fin b → ℂ) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {p : ((Fin n → ℂ) × (Fin b → ℂ)) × (Fin d → ℂ) |
        q p.1.1 = ∏ i, (Polynomial.X - Polynomial.C (p.2 i)) ∧ F p.2 = p.1.2}
      ((a, y), z) := by
  let φ := fun p : ((Fin n → ℂ) × (Fin b → ℂ)) × (Fin d → ℂ) => (p.1.1, p.2)
  have hφ : ∀ p, AnalyticAt ℂ φ p := fun p => (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  have hi := (s2e_rootTuple_incidence_analytic_finite q a hdegree hq z).1.preimage hφ
    (y₀ := ((a, y), z))
  obtain ⟨V, hVo, hVp, κ, hκ, g, hg, he⟩ := hi
  letI : Finite κ := hκ
  let G := fun j : Fin b => fun p : ((Fin n → ℂ) × (Fin b → ℂ)) × (Fin d → ℂ) =>
    F p.2 j - p.1.2 j
  have hG : ∀ j, AnalyticAt ℂ (G j) ((a, y), z) := by
    intro j
    have hl : AnalyticAt ℂ (fun p : ((Fin n → ℂ) × (Fin b → ℂ)) × (Fin d → ℂ) =>
        F p.2 j) ((a, y), z) :=
      (analyticAt_pi_iff.mp hF j).comp_of_eq analyticAt_snd rfl
    have hm : AnalyticAt ℂ (fun p : ((Fin n → ℂ) × (Fin b → ℂ)) × (Fin d → ℂ) =>
        p.1.2) ((a, y), z) := analyticAt_snd.comp analyticAt_fst
    have hr : AnalyticAt ℂ (fun p : ((Fin n → ℂ) × (Fin b → ℂ)) × (Fin d → ℂ) =>
        p.1.2 j) ((a, y), z) :=
      ((ContinuousLinearMap.proj j : (Fin b → ℂ) →L[ℂ] ℂ).analyticAt y).comp_of_eq hm rfl
    exact hl.sub hr
  have hall : ∀ᶠ p in nhds ((a, y), z), ∀ j, AnalyticAt ℂ (G j) p :=
    eventually_all.2 fun j => (hG j).eventually_analyticAt
  obtain ⟨W, hWsub, hWo, hWp⟩ := eventually_nhds_iff.mp hall
  refine ⟨V ∩ W, hVo.inter hWo, ⟨hVp, hWp⟩, κ ⊕ Fin b, inferInstance,
    Sum.elim g G, ?_, ?_⟩
  · intro j p hp
    cases j with
    | inl j => exact hg j p hp.1
    | inr j => exact hWsub p hp.2 j
  · intro p hp
    have hh := he p hp.1
    change (q p.1.1 = ∏ i, (Polynomial.X - Polynomial.C (p.2 i))) ↔ _ at hh
    constructor
    · rintro ⟨hq', hF'⟩ j
      cases j with
      | inl j => exact hh.mp hq' j
      | inr j => exact sub_eq_zero.mpr (congrFun hF' j)
    · intro h
      refine ⟨hh.mpr (fun j => h (Sum.inl j)), ?_⟩
      funext j
      exact sub_eq_zero.mp (h (Sum.inr j))

/-- Eliminating isolated root tuples gives a local analytic evaluation image through collisions. -/
theorem s2e_rootTuple_evaluation_image_analytic {n d b : ℕ}
    (q : (Fin n → ℂ) → Polynomial ℂ) (a : Fin n → ℂ)
    (hdegree : ∀ a', (q a').natDegree ≤ d)
    (hq : ∀ k, AnalyticAt ℂ (fun a' => (q a').coeff k) a)
    (hqa : q a ≠ 0) (F : (Fin d → ℂ) → (Fin b → ℂ))
    (z : Fin d → ℂ) (hz : q a = ∏ i, (Polynomial.X - Polynomial.C (z i)))
    (hF : AnalyticAt ℂ F z) :
    ∃ ρ > 0, ∀ ε, 0 < ε → ε ≤ ρ →
      HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
        {ay : (Fin n → ℂ) × (Fin b → ℂ) | ∃ w : Fin d → ℂ,
          dist w z < ε ∧
          q ay.1 = ∏ i, (Polynomial.X - Polynomial.C (w i)) ∧ F w = ay.2}
        (a, F z) := by
  have hg := s2e_rootTuple_graph_analytic q a hdegree hq F z hF (F z)
  obtain ⟨r, hr, hiso⟩ := s2e_polynomial_root_tuple_isolated (q a) hqa z hz
  exact HodgeLean.Foundations.Analytic.anf_eliminate d hg
    ⟨r, hr, fun w hw h => hiso w hw h.1⟩

/-- Symmetric evaluation is constant on exact root presentations, with repeated roots retained. -/
theorem s2e_rootTuple_symmetric_evaluation_eq {d : ℕ} {T : Type*}
    (F : (Fin d → ℂ) → T)
    (hF : ∀ (w : Fin d → ℂ) (σ : Equiv.Perm (Fin d)), F (fun i => w (σ i)) = F w)
    (z w : Fin d → ℂ)
    (h : (∏ i, (Polynomial.X - Polynomial.C (z i))) =
      ∏ i, (Polynomial.X - Polynomial.C (w i))) : F z = F w := by
  have hr (v : Fin d → ℂ) :
      (∏ i, (Polynomial.X - Polynomial.C (v i))).roots = (List.ofFn v : Multiset ℂ) := by
    simpa only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
      Function.comp_def, List.prod_ofFn] using
      Polynomial.roots_multiset_prod_X_sub_C (List.ofFn v : Multiset ℂ)
  have hm : (List.ofFn z : Multiset ℂ) = List.ofFn w :=
    (hr z).symm.trans ((congrArg Polynomial.roots h).trans (hr w))
  obtain ⟨σ, hσ⟩ := s2e_tuple_permutation_of_multiset_eq z w hm
  have hz : z = fun i => w (σ i) := funext (fun i => (hσ i).symm)
  rw [hz]
  exact hF w σ

/-- A monic polynomial has exactly one value under symmetric evaluation of its root tuples. -/
theorem s2e_monic_rootTuple_evaluation_unique {d : ℕ} {T : Type*}
    (q : Polynomial ℂ) (hq : q.Monic) (hd : q.natDegree = d)
    (F : (Fin d → ℂ) → T)
    (hF : ∀ (w : Fin d → ℂ) (σ : Equiv.Perm (Fin d)), F (fun i => w (σ i)) = F w) :
    ∃! y : T, ∃ z : Fin d → ℂ,
      q = ∏ i, (Polynomial.X - Polynomial.C (z i)) ∧ F z = y := by
  obtain ⟨z, hz⟩ := s2e_monic_polynomial_exists_root_tuple q hq hd
  refine ⟨F z, ⟨z, hz, rfl⟩, ?_⟩
  rintro y ⟨w, hw, rfl⟩
  exact s2e_rootTuple_symmetric_evaluation_eq F hF w z (hw.symm.trans hz)

/-- Every exact tuple of roots of a centred monic family remains in a prescribed small ball. -/
theorem s2e_monic_rootTuples_eventually_small {n d : ℕ}
    (c : Fin d → (Fin n → ℂ) → ℂ)
    (hc : ∀ j, ContinuousAt (c j) 0) (hc0 : ∀ j, c j 0 = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in nhds (0 : Fin n → ℂ), ∀ z : Fin d → ℂ,
      monicPoly c a = ∏ i, (Polynomial.X - Polynomial.C (z i)) → dist z 0 < ε := by
  have hs := HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_monicInLast_roots_small hc hc0 hε
  filter_upwards [hs] with a ha z hz
  rw [dist_zero_right, pi_norm_lt_iff hε]
  intro i
  apply ha (z i)
  rw [← (spec_monicPoly_aux c a).2.2, hz]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (z i))

/-- The full evaluation relation of a centred monic family is locally analytic. -/
theorem s2e_monic_evaluation_relation_analytic {n d b : ℕ}
    (c : Fin d → (Fin n → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) (hc0 : ∀ j, c j 0 = 0)
    (F : (Fin d → ℂ) → (Fin b → ℂ)) (hF : AnalyticAt ℂ F 0) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {ay : (Fin n → ℂ) × (Fin b → ℂ) | ∃ z : Fin d → ℂ,
        monicPoly c ay.1 = ∏ i, (Polynomial.X - Polynomial.C (z i)) ∧ F z = ay.2}
      (0, F 0) := by
  have hm (a : Fin n → ℂ) := spec_monicPoly_aux c a
  have hz : monicPoly c 0 = ∏ i : Fin d, (Polynomial.X - Polynomial.C ((0 : Fin d → ℂ) i)) := by
    simp [monicPoly, hc0]
  obtain ⟨ρ, hρ, hproj⟩ := s2e_rootTuple_evaluation_image_analytic (monicPoly c) 0
    (fun a => le_of_eq (hm a).2.1) (gaga5b_analyticAt_coeff_monicPoly hc)
    (hm 0).1.ne_zero F 0 hz hF
  have hs := s2e_monic_rootTuples_eventually_small c (fun j => (hc j).continuousAt) hc0 hρ
  have he : ∀ᶠ ay : (Fin n → ℂ) × (Fin b → ℂ) in nhds (0, F 0),
      ∀ z : Fin d → ℂ, monicPoly c ay.1 = ∏ i, (Polynomial.X - Polynomial.C (z i)) →
        dist z 0 < ρ := (continuous_fst.tendsto (0, F 0)).eventually hs
  apply (hproj ρ hρ le_rfl).congr
  filter_upwards [he] with ay hay
  constructor
  · rintro ⟨z, _, hz, hy⟩
    exact ⟨z, hz, hy⟩
  · rintro ⟨z, hz, hy⟩
    exact ⟨z, hay z hz, hz, hy⟩

/-- Evaluate a monic family on a chosen exact root tuple, retaining every multiplicity. -/
def s2e_monicRootEvaluation {n d : ℕ} {T : Type*}
    (c : Fin d → (Fin n → ℂ) → ℂ) (F : (Fin d → ℂ) → T) (a : Fin n → ℂ) : T :=
  F (s2e_monic_polynomial_exists_root_tuple (monicPoly c a)
    (spec_monicPoly_aux c a).1 (spec_monicPoly_aux c a).2.1).choose

/-- Symmetric monic evaluation agrees with every exact tuple of roots. -/
theorem s2e_monicRootEvaluation_eq {n d : ℕ} {T : Type*}
    (c : Fin d → (Fin n → ℂ) → ℂ) (F : (Fin d → ℂ) → T)
    (hF : ∀ (w : Fin d → ℂ) (σ : Equiv.Perm (Fin d)), F (fun i => w (σ i)) = F w)
    (a : Fin n → ℂ) (z : Fin d → ℂ)
    (hz : monicPoly c a = ∏ i, (Polynomial.X - Polynomial.C (z i))) :
    s2e_monicRootEvaluation c F a = F z := by
  apply s2e_rootTuple_symmetric_evaluation_eq F hF
  exact (s2e_monic_polynomial_exists_root_tuple (monicPoly c a)
    (spec_monicPoly_aux c a).1 (spec_monicPoly_aux c a).2.1).choose_spec.symm.trans hz

/-- Symmetric analytic evaluation of a centred monic family has a locally analytic graph. -/
theorem s2e_monicRootEvaluation_graph_analytic {n d b : ℕ}
    (c : Fin d → (Fin n → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) (hc0 : ∀ j, c j 0 = 0)
    (F : (Fin d → ℂ) → (Fin b → ℂ)) (hFa : AnalyticAt ℂ F 0)
    (hF : ∀ (w : Fin d → ℂ) (σ : Equiv.Perm (Fin d)), F (fun i => w (σ i)) = F w) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {ay : (Fin n → ℂ) × (Fin b → ℂ) | s2e_monicRootEvaluation c F ay.1 = ay.2}
      (0, s2e_monicRootEvaluation c F 0) := by
  have hz : monicPoly c 0 = ∏ i : Fin d, (Polynomial.X - Polynomial.C ((0 : Fin d → ℂ) i)) := by
    simp [monicPoly, hc0]
  rw [s2e_monicRootEvaluation_eq c F hF 0 0 hz]
  apply (s2e_monic_evaluation_relation_analytic c hc hc0 F hFa).congr
  apply Filter.Eventually.of_forall
  intro ay
  constructor
  · rintro ⟨z, hz, hy⟩
    exact (s2e_monicRootEvaluation_eq c F hF ay.1 z hz).trans hy
  · intro hy
    obtain ⟨z, hz⟩ := s2e_monic_polynomial_exists_root_tuple (monicPoly c ay.1)
      (spec_monicPoly_aux c ay.1).1 (spec_monicPoly_aux c ay.1).2.1
    exact ⟨z, hz, (s2e_monicRootEvaluation_eq c F hF ay.1 z hz).symm.trans hy⟩

/-- Symmetric root evaluation is continuous at a centred collision fibre. -/
theorem s2e_monicRootEvaluation_continuousAt {n d : ℕ} {T : Type*} [TopologicalSpace T]
    (c : Fin d → (Fin n → ℂ) → ℂ)
    (hc : ∀ j, ContinuousAt (c j) 0) (hc0 : ∀ j, c j 0 = 0)
    (F : (Fin d → ℂ) → T) (hFc : ContinuousAt F 0)
    (hF : ∀ (w : Fin d → ℂ) (σ : Equiv.Perm (Fin d)), F (fun i => w (σ i)) = F w) :
    ContinuousAt (s2e_monicRootEvaluation c F) 0 := by
  let R := fun a : Fin n → ℂ => (s2e_monic_polynomial_exists_root_tuple (monicPoly c a)
    (spec_monicPoly_aux c a).1 (spec_monicPoly_aux c a).2.1).choose
  have hR : Tendsto R (nhds 0) (nhds 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [s2e_monic_rootTuples_eventually_small c hc hc0 hε] with a ha
    exact ha (R a) (s2e_monic_polynomial_exists_root_tuple (monicPoly c a)
      (spec_monicPoly_aux c a).1 (spec_monicPoly_aux c a).2.1).choose_spec
  have hz : monicPoly c 0 = ∏ i : Fin d, (Polynomial.X - Polynomial.C ((0 : Fin d → ℂ) i)) := by
    simp [monicPoly, hc0]
  change Tendsto (s2e_monicRootEvaluation c F) (nhds 0) (nhds (s2e_monicRootEvaluation c F 0))
  rw [s2e_monicRootEvaluation_eq c F hF 0 0 hz]
  exact hFc.tendsto.comp hR

/-- Analytic orders of an exact root polynomial equal the actual tuple fibre cardinalities. -/
theorem s2e_rootTuple_analytic_order {d : ℕ} (q : Polynomial ℂ)
    (z : Fin d → ℂ) (hz : q = ∏ i, (Polynomial.X - Polynomial.C (z i))) (w : ℂ) :
    analyticOrderAt (fun v => q.eval v) w = (Fintype.card {i : Fin d // z i = w} : ℕ∞) := by
  classical
  have hq : q ≠ 0 := by
    rw [hz]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero (z i))
  have hr : q.roots = (List.ofFn z : Multiset ℂ) := by
    rw [hz]
    simpa only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
      Function.comp_def, List.prod_ofFn] using
      Polynomial.roots_multiset_prod_X_sub_C (List.ofFn z : Multiset ℂ)
  rw [HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_analyticOrderAt_polynomial_eval hq,
    ← Polynomial.count_roots, hr]
  simp only [Multiset.coe_count]
  exact_mod_cast s2e_tuple_count_eq_fiber_card z w

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every exact local polynomial tuple represents the actual nearby canonical multiplicities. -/
theorem s2e_holomorphicFamily_local_root_multiplicities
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ i, a i • b i : b3_HolForm E C) ≠ 0)
    (p : C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (r δ : ℝ) (c : Fin d → (Fin n → ℂ) → ℂ),
      (d : ℤ) = b4c_divForm (hE := hE) (∑ i, a i • b i : b3_HolForm E C) p ∧
      0 < r ∧ r < ε ∧ 0 < δ ∧
      (∀ w ∈ Metric.closedBall (0 : ℂ) r,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) p).target) ∧
      (∀ j, AnalyticOnNhd ℂ (c j) (Metric.ball a δ)) ∧
      ∀ᶠ a' in nhds a,
        (∑ i, a' i • b i : b3_HolForm E C) ≠ 0 ∧
        ∀ z : Fin d → ℂ, monicPoly c a' = ∏ i, (Polynomial.X - Polynomial.C (z i)) →
          (∀ i, z i ∈ Metric.ball (0 : ℂ) r) ∧
          ∀ w ∈ Metric.ball (0 : ℂ) r,
            (Fintype.card {i : Fin d // z i = w} : ℤ) =
              b4c_divForm (hE := hE) (∑ i, a' i • b i : b3_HolForm E C)
                ((extChartAt 𝓘(ℂ, E) p).symm
                  (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w)) := by
  obtain ⟨d, r, δ, c, hd, hr, hrε, hδ, ht, hc, he⟩ :=
    s2e_holomorphicFamily_local_polynomial hE b a hne p hε
  refine ⟨d, r, δ, c, hd, hr, hrε, hδ, ht, hc, ?_⟩
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

/-- Local root counts give an actual subdivisor of the holomorphic differential divisor. -/
theorem s2e_holomorphic_divisor_local_tuple_le
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) (hθ : θ ≠ 0)
    (p : C) (r : ℝ)
    (ht : ∀ w ∈ Metric.ball (0 : ℂ) r,
      extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w ∈ (extChartAt 𝓘(ℂ, E) p).target)
    {d : ℕ} (z : Fin d → ℂ) (hz : ∀ i, z i ∈ Metric.ball (0 : ℂ) r)
    (hm : ∀ w ∈ Metric.ball (0 : ℂ) r,
      (Fintype.card {i : Fin d // z i = w} : ℤ) = b4c_divForm (hE := hE) θ
        ((extChartAt 𝓘(ℂ, E) p).symm (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w))) :
    (∑ i, Finsupp.single
      ((extChartAt 𝓘(ℂ, E) p).symm (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE (z i)))
      (1 : ℤ)) ≤ b4c_divForm (hE := hE) θ := by
  apply s2e_tuple_divisor_le_of_injective_coordinates _
    (s2e_holomorphic_divisor_effective hE θ hθ) (Metric.ball (0 : ℂ) r)
    (fun w => (extChartAt 𝓘(ℂ, E) p).symm
      (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w)) ?_ z hz
  · intro w hw
    exact le_of_eq (hm w hw)
  · intro u hu v hv huv
    have he := (extChartAt 𝓘(ℂ, E) p).symm.injOn (ht u hu) (ht v hv) huv
    exact (b4cov_lineEquiv hE).injective (add_left_cancel he)

/-- A sufficiently small curve chart disc lies in any prescribed neighbourhood of its centre. -/
theorem s2e_curve_chart_disc_inside (hE : Module.finrank ℂ E = 1) (p : C)
    (U : Set C) (hU : U ∈ nhds p) :
    ∃ r > 0, ∀ w ∈ Metric.ball (0 : ℂ) r,
      extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w ∈ (extChartAt 𝓘(ℂ, E) p).target ∧
      (extChartAt 𝓘(ℂ, E) p).symm
        (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w) ∈ U := by
  have hl : ContinuousAt (fun w : ℂ => extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w) 0 :=
    continuousAt_const.add (b4cov_lineEquiv hE).continuousAt
  have hc := (continuousAt_extChartAt_symm (I := 𝓘(ℂ, E)) p).comp_of_eq hl
    (by simp only [map_zero, add_zero])
  have hp : (extChartAt 𝓘(ℂ, E) p).symm
      (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE 0) = p := by
    rw [map_zero, add_zero]
    exact extChartAt_to_inv p
  have hu : ∀ᶠ w in nhds (0 : ℂ), (extChartAt 𝓘(ℂ, E) p).symm
      (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w) ∈ U := by
    apply hc
    simpa only [Function.comp_def, hp] using hU
  have ht0 : extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE 0 ∈
      (extChartAt 𝓘(ℂ, E) p).target := by
    simpa only [map_zero, add_zero] using mem_extChartAt_target (I := 𝓘(ℂ, E)) p
  exact Metric.eventually_nhds_iff_ball.mp
    ((hl.eventually ((isOpen_extChartAt_target p).mem_nhds ht0)).and hu)

/-- Distinct finitely many curve points have pairwise disjoint valid coordinate discs. -/
theorem s2e_curve_chart_discs_disjoint [T2Space C] {ι : Type} [Fintype ι]
    (hE : Module.finrank ℂ E = 1) (p : ι → C) (hp : Function.Injective p) :
    ∃ r : ι → ℝ, (∀ i, 0 < r i) ∧
      (∀ i w, w ∈ Metric.ball (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (p i)).target) ∧
      Pairwise (fun i j => Disjoint
        ((fun w => (extChartAt 𝓘(ℂ, E) (p i)).symm
          (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)) '' Metric.ball 0 (r i))
        ((fun w => (extChartAt 𝓘(ℂ, E) (p j)).symm
          (extChartAt 𝓘(ℂ, E) (p j) (p j) + b4cov_lineEquiv hE w)) '' Metric.ball 0 (r j))) := by
  obtain ⟨U, hU, hsep⟩ := (Set.finite_range p).t2_separation
  have hd (i : ι) := s2e_curve_chart_disc_inside hE (p i) (U (p i))
    ((hU (p i)).2.mem_nhds (hU (p i)).1)
  choose r hr hrt using hd
  refine ⟨r, hr, fun i w hw => (hrt i w hw).1, ?_⟩
  intro i j hij
  apply (hsep (Set.mem_range_self i) (Set.mem_range_self j) (hp.ne hij)).mono
  · rintro x ⟨w, hw, rfl⟩
    exact (hrt i w hw).2
  · rintro x ⟨w, hw, rfl⟩
    exact (hrt j w hw).2

/-- Disjoint valid local root tuples of full degree recover the actual holomorphic divisor. -/
theorem s2e_holomorphic_divisor_eq_disjoint_local_tuples
    [T2Space C] [CompactSpace C] [ConnectedSpace C] {ι : Type} [Fintype ι]
    (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) (hθ : θ ≠ 0)
    (p : ι → C) (r : ι → ℝ) (d : ι → ℕ) (z : (i : ι) → Fin (d i) → ℂ)
    (ht : ∀ i w, w ∈ Metric.ball (0 : ℂ) (r i) →
      extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w ∈
        (extChartAt 𝓘(ℂ, E) (p i)).target)
    (hz : ∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i))
    (hm : ∀ i w, w ∈ Metric.ball (0 : ℂ) (r i) →
      (Fintype.card {j : Fin (d i) // z i j = w} : ℤ) = b4c_divForm (hE := hE) θ
        ((extChartAt 𝓘(ℂ, E) (p i)).symm
          (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)))
    (hd : b4c_deg (b4c_divForm (E := E) (C := C) (hE := hE) θ) = ((∑ i, d i : ℕ) : ℤ))
    (hdis : Pairwise (fun i j => Disjoint
      ((fun w => (extChartAt 𝓘(ℂ, E) (p i)).symm
        (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)) '' Metric.ball 0 (r i))
      ((fun w => (extChartAt 𝓘(ℂ, E) (p j)).symm
        (extChartAt 𝓘(ℂ, E) (p j) (p j) + b4cov_lineEquiv hE w)) '' Metric.ball 0 (r j)))) :
    b4c_divForm (hE := hE) θ = ∑ i, ∑ j, Finsupp.single
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
  apply s2e_effectiveDivisor_eq_cluster_sum _ (s2e_holomorphic_divisor_effective hE θ hθ)
    d hd (fun i j => g i (z i j))
  · intro i
    exact s2e_holomorphic_divisor_local_tuple_le hE θ hθ (p i) (r i) (ht i) (z i) (hz i) (hm i)
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (hdis hij) (hsub i hx) (hsub j hy)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finitely many actual zero clusters have simultaneous analytic polynomial presentations. -/
theorem s2e_holomorphicFamily_finite_local_polynomials
    [T2Space C] [CompactSpace C] [ConnectedSpace C] {ι : Type} [Fintype ι]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ j, a j • b j : b3_HolForm E C) ≠ 0)
    (p : ι → C) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ (d : ι → ℕ) (r δ : ι → ℝ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ),
      (∀ i, (d i : ℤ) = b4c_divForm (hE := hE) (∑ j, a j • b j : b3_HolForm E C) (p i)) ∧
      (∀ i, 0 < r i ∧ r i < ε i ∧ 0 < δ i) ∧
      (∀ i w, w ∈ Metric.closedBall (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (p i)).target) ∧
      (∀ i j, AnalyticOnNhd ℂ (c i j) (Metric.ball a (δ i))) ∧
      ∀ᶠ a' in nhds a,
        (∑ j, a' j • b j : b3_HolForm E C) ≠ 0 ∧
        ∀ i (z : Fin (d i) → ℂ),
          monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z j)) →
          (∀ j, z j ∈ Metric.ball (0 : ℂ) (r i)) ∧
          ∀ w ∈ Metric.ball (0 : ℂ) (r i),
            (Fintype.card {j : Fin (d i) // z j = w} : ℤ) =
              b4c_divForm (hE := hE) (∑ j, a' j • b j : b3_HolForm E C)
                ((extChartAt 𝓘(ℂ, E) (p i)).symm
                  (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)) := by
  choose d r δ c hd hr hre hδ ht hc he using fun i =>
    s2e_holomorphicFamily_local_root_multiplicities hE b a hne (p i) (hε i)
  refine ⟨d, r, δ, c, hd, fun i => ⟨hr i, hre i, hδ i⟩, ht, hc, ?_⟩
  filter_upwards [eventually_all.mpr he, s2e_holomorphicFamily_eventually_ne_zero b a hne]
    with a' ha' hn'
  exact ⟨hn', fun i => (ha' i).2⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Simultaneous polynomial clusters covering the initial degree recover every nearby divisor. -/
theorem s2e_holomorphicFamily_cluster_divisor_presentation
    [T2Space C] [CompactSpace C] [ConnectedSpace C] {ι : Type} [Fintype ι]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ j, a j • b j : b3_HolForm E C) ≠ 0)
    (p : ι → C) (hp : Function.Injective p)
    (hsum : (∑ i, b4c_divForm (hE := hE) (∑ j, a j • b j : b3_HolForm E C) (p i)) =
      b4c_deg (b4c_divForm (E := E) (C := C) (hE := hE) (∑ j, a j • b j : b3_HolForm E C))) :
    ∃ (d : ι → ℕ) (r δ : ι → ℝ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ),
      (∀ i, (d i : ℤ) = b4c_divForm (hE := hE) (∑ j, a j • b j : b3_HolForm E C) (p i)) ∧
      (∀ i, 0 < r i ∧ 0 < δ i) ∧
      (∀ i w, w ∈ Metric.closedBall (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (p i)).target) ∧
      (∀ i j, AnalyticOnNhd ℂ (c i j) (Metric.ball a (δ i))) ∧
      ∀ᶠ a' in nhds a,
        (∑ j, a' j • b j : b3_HolForm E C) ≠ 0 ∧
        ∀ z : (i : ι) → Fin (d i) → ℂ,
          (∀ i, monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
          (∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i)) ∧
          b4c_divForm (hE := hE) (∑ j, a' j • b j : b3_HolForm E C) =
            ∑ i, ∑ j, Finsupp.single
              ((extChartAt 𝓘(ℂ, E) (p i)).symm
                (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE (z i j))) (1 : ℤ) := by
  obtain ⟨ε, hε, _, hsep⟩ := s2e_curve_chart_discs_disjoint hE p hp
  obtain ⟨d, r, δ, c, hd, hr, ht, hc, he⟩ :=
    s2e_holomorphicFamily_finite_local_polynomials hE b a hne p ε hε
  refine ⟨d, r, δ, c, hd, fun i => ⟨(hr i).1, (hr i).2.2⟩, ht, hc, ?_⟩
  filter_upwards [he] with a' ha'
  refine ⟨ha'.1, fun z hz => ?_⟩
  have hzi : ∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i) :=
    fun i => (ha'.2 i (z i) (hz i)).1
  refine ⟨hzi, ?_⟩
  have hdeg : b4c_deg (b4c_divForm (E := E) (C := C) (hE := hE)
      (∑ j, a' j • b j : b3_HolForm E C)) = ((∑ i, d i : ℕ) : ℤ) := by
    rw [s2e_holomorphic_divisor_degree hE _ ha'.1,
      ← s2e_holomorphic_divisor_degree hE _ hne, ← hsum]
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => (hd i).symm)
  apply s2e_holomorphic_divisor_eq_disjoint_local_tuples hE _ ha'.1 p r d z
    (fun i w hw => ht i w (Metric.ball_subset_closedBall hw)) hzi
    (fun i => (ha'.2 i (z i) (hz i)).2) hdeg
  intro i j hij
  exact (hsep hij).mono
    (Set.image_mono (Metric.ball_subset_ball (hr i).2.1.le))
    (Set.image_mono (Metric.ball_subset_ball (hr j).2.1.le))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual initial canonical support supplies a simultaneous presentation of nearby divisors. -/
theorem s2e_holomorphicFamily_support_divisor_presentation
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ j, a j • b j : b3_HolForm E C) ≠ 0) :
    let D := b4c_divForm (E := E) (C := C) (hE := hE) (∑ j, a j • b j : b3_HolForm E C)
    ∃ (d : D.support → ℕ) (r δ : D.support → ℝ) (c : (i : D.support) → Fin (d i) → (Fin n → ℂ) → ℂ),
      (∀ i, (d i : ℤ) = b4c_divForm (hE := hE) (∑ j, a j • b j : b3_HolForm E C) (i : C)) ∧
      (∀ i, 0 < r i ∧ 0 < δ i) ∧
      (∀ i w, w ∈ Metric.closedBall (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (i : C) (i : C) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (i : C)).target) ∧
      (∀ i j, AnalyticOnNhd ℂ (c i j) (Metric.ball a (δ i))) ∧
      ∀ᶠ a' in nhds a,
        (∑ j, a' j • b j : b3_HolForm E C) ≠ 0 ∧
        ∀ z : (i : D.support) → Fin (d i) → ℂ,
          (∀ i, monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
          (∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i)) ∧
          b4c_divForm (hE := hE) (∑ j, a' j • b j : b3_HolForm E C) =
            ∑ i : D.support, ∑ j : Fin (d i), Finsupp.single
              ((extChartAt 𝓘(ℂ, E) (i : C)).symm
                (extChartAt 𝓘(ℂ, E) (i : C) (i : C) + b4cov_lineEquiv hE (z i j))) (1 : ℤ) := by
  dsimp only
  let D := b4c_divForm (E := E) (C := C) (hE := hE) (∑ j, a j • b j : b3_HolForm E C)
  apply s2e_holomorphicFamily_cluster_divisor_presentation hE b a hne
    (fun i : D.support => (i : C)) Subtype.val_injective
  change (∑ i : D.support, D i) = b4c_deg D
  simp [b4c_deg, Finsupp.sum, Finset.sum_attach]

/-- Simultaneous monic cluster equations have nonempty finite exact-tuple fibres. -/
theorem s2e_monic_cluster_rootTuples_finite_nonempty {ι : Type} [Fintype ι] {n : ℕ}
    (d : ι → ℕ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ) (a : Fin n → ℂ) :
    Set.Finite {z : (i : ι) → Fin (d i) → ℂ |
      ∀ i, monicPoly (c i) a = ∏ j, (Polynomial.X - Polynomial.C (z i j))} ∧
    ∃ z : (i : ι) → Fin (d i) → ℂ,
      ∀ i, monicPoly (c i) a = ∏ j, (Polynomial.X - Polynomial.C (z i j)) := by
  classical
  have hf : (Set.univ.pi (fun i => {z : Fin (d i) → ℂ |
      monicPoly (c i) a = ∏ j, (Polynomial.X - Polynomial.C (z j))})).Finite :=
    Set.Finite.pi fun i => s2e_polynomial_root_tuples_finite _ (spec_monicPoly_aux (c i) a).1.ne_zero
  refine ⟨hf.subset (fun z hz i _ => hz i), ?_⟩
  choose z hz using fun i => s2e_monic_polynomial_exists_root_tuple (monicPoly (c i) a)
    (spec_monicPoly_aux (c i) a).1 (spec_monicPoly_aux (c i) a).2.1
  exact ⟨z, hz⟩

/-- Finite simultaneous local analytic conditions are locally analytic. -/
theorem s2e_analyticNear_finite_inter {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ι : Type} [Fintype ι] (S : ι → Set V) (x : V)
    (hS : ∀ i, HodgeLean.Foundations.Analytic.anf_IsAnalyticNear (S i) x) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear (⋂ i, S i) x := by
  classical
  choose U hU hx κ hκ g hg he using hS
  letI : ∀ i, Finite (κ i) := hκ
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, Set.mem_iInter.mpr hx,
    (i : ι) × κ i, inferInstance, (fun j => g j.1 j.2), ?_, ?_⟩
  · intro j y hy
    exact hg j.1 j.2 y (Set.mem_iInter.mp hy j.1)
  · intro y hy
    constructor
    · intro h j
      exact (he j.1 y (Set.mem_iInter.mp hy j.1)).mp (Set.mem_iInter.mp h j.1) j.2
    · intro h
      apply Set.mem_iInter.mpr
      intro i
      exact (he i y (Set.mem_iInter.mp hy i)).mpr (fun j => h ⟨i, j⟩)

/-- The simultaneous monic root-cluster incidence is locally analytic at every tuple. -/
theorem s2e_monic_cluster_incidence_analytic {ι : Type} [Fintype ι] {n : ℕ}
    (d : ι → ℕ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ) (a : Fin n → ℂ)
    (hc : ∀ i j, AnalyticAt ℂ (c i j) a) (z : (i : ι) → Fin (d i) → ℂ) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {az : (Fin n → ℂ) × ((i : ι) → Fin (d i) → ℂ) |
        ∀ i, monicPoly (c i) az.1 = ∏ j, (Polynomial.X - Polynomial.C (az.2 i j))} (a, z) := by
  let S := fun i : ι => {az : (Fin n → ℂ) × ((j : ι) → Fin (d j) → ℂ) |
    monicPoly (c i) az.1 = ∏ j, (Polynomial.X - Polynomial.C (az.2 i j))}
  have hi : ∀ i, HodgeLean.Foundations.Analytic.anf_IsAnalyticNear (S i) (a, z) := by
    intro i
    let φ := fun az : (Fin n → ℂ) × ((j : ι) → Fin (d j) → ℂ) => (az.1, az.2 i)
    have hφ : ∀ az, AnalyticAt ℂ φ az := by
      intro az
      have hp : AnalyticAt ℂ
          (fun az : (Fin n → ℂ) × ((j : ι) → Fin (d j) → ℂ) => az.2 i) az :=
        ((ContinuousLinearMap.proj i : ((j : ι) → Fin (d j) → ℂ) →L[ℂ] (Fin (d i) → ℂ)).analyticAt az.2).comp_of_eq
          analyticAt_snd rfl
      exact analyticAt_fst.prod hp
    exact ((s2e_monic_rootTuple_analytic_cover (c i) a (hc i)).1 (z i)).preimage hφ (y₀ := (a, z))
  have hh := s2e_analyticNear_finite_inter S (a, z) hi
  apply hh.congr
  exact Filter.Eventually.of_forall (fun az => by simp only [Set.mem_iInter, S, Set.mem_ofPred_eq])

/-- Analytic evaluation coordinates can be appended to any locally analytic incidence. -/
theorem s2e_analytic_incidence_evaluation_graph {n b : ℕ} {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : Set ((Fin n → ℂ) × V)) (a : Fin n → ℂ) (z : V)
    (hA : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear A (a, z))
    (F : V → (Fin b → ℂ)) (hF : AnalyticAt ℂ F z) (y : Fin b → ℂ) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {p : ((Fin n → ℂ) × (Fin b → ℂ)) × V | (p.1.1, p.2) ∈ A ∧ F p.2 = p.1.2}
      ((a, y), z) := by
  let φ := fun p : ((Fin n → ℂ) × (Fin b → ℂ)) × V => (p.1.1, p.2)
  have hφ : ∀ p, AnalyticAt ℂ φ p := fun p => (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  have hi := hA.preimage hφ (y₀ := ((a, y), z))
  obtain ⟨U, hVo, hVp, κ, hκ, g, hg, he⟩ := hi
  letI : Finite κ := hκ
  let G := fun j : Fin b => fun p : ((Fin n → ℂ) × (Fin b → ℂ)) × V =>
    F p.2 j - p.1.2 j
  have hG : ∀ j, AnalyticAt ℂ (G j) ((a, y), z) := by
    intro j
    have hl : AnalyticAt ℂ (fun p : ((Fin n → ℂ) × (Fin b → ℂ)) × V =>
        F p.2 j) ((a, y), z) :=
      (analyticAt_pi_iff.mp hF j).comp_of_eq analyticAt_snd rfl
    have hm : AnalyticAt ℂ (fun p : ((Fin n → ℂ) × (Fin b → ℂ)) × V =>
        p.1.2) ((a, y), z) := analyticAt_snd.comp analyticAt_fst
    have hr : AnalyticAt ℂ (fun p : ((Fin n → ℂ) × (Fin b → ℂ)) × V =>
        p.1.2 j) ((a, y), z) :=
      ((ContinuousLinearMap.proj j : (Fin b → ℂ) →L[ℂ] ℂ).analyticAt y).comp_of_eq hm rfl
    exact hl.sub hr
  have hall : ∀ᶠ p in nhds ((a, y), z), ∀ j, AnalyticAt ℂ (G j) p :=
    eventually_all.2 fun j => (hG j).eventually_analyticAt
  obtain ⟨W, hWsub, hWo, hWp⟩ := eventually_nhds_iff.mp hall
  refine ⟨U ∩ W, hVo.inter hWo, ⟨hVp, hWp⟩, κ ⊕ Fin b, inferInstance,
    Sum.elim g G, ?_, ?_⟩
  · intro j p hp
    cases j with
    | inl j => exact hg j p hp.1
    | inr j => exact hWsub p hp.2 j
  · intro p hp
    have hh := he p hp.1
    change ((p.1.1, p.2) ∈ A) ↔ _ at hh
    constructor
    · rintro ⟨hq', hF'⟩ j
      cases j with
      | inl j => exact hh.mp hq' j
      | inr j => exact sub_eq_zero.mpr (congrFun hF' j)
    · intro h
      refine ⟨hh.mpr (fun j => h (Sum.inl j)), ?_⟩
      funext j
      exact sub_eq_zero.mp (h (Sum.inr j))

/-- Finite analytic fibres can be eliminated after a continuous linear choice of coordinates. -/
theorem s2e_analytic_finite_projection_in_coordinates {B V : Type}
    [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ}
    (e : V ≃L[ℂ] (Fin k → ℂ)) (A : Set (B × V)) (y : B) (z : V)
    (hA : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear A (y, z))
    (hz : (y, z) ∈ A) (hfin : Set.Finite {w : V | (y, w) ∈ A}) :
    ∃ ρ > 0, ∀ ε, 0 < ε → ε ≤ ρ →
      HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
        {y' : B | ∃ w : V, dist (e w) (e z) < ε ∧ (y', w) ∈ A} y := by
  let φ := fun p : B × (Fin k → ℂ) => (p.1, e.symm p.2)
  let A' := φ ⁻¹' A
  have hφ : ∀ p, AnalyticAt ℂ φ p := by
    intro p
    exact analyticAt_fst.prod (e.symm.analyticAt p.2 |>.comp_of_eq analyticAt_snd rfl)
  have ha : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear A (φ (y, e z)) := by
    simpa only [φ, ContinuousLinearEquiv.symm_apply_apply] using hA
  have ha' : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear A' (y, e z) :=
    ha.preimage hφ (y₀ := (y, e z))
  have hf : Set.Finite {u : Fin k → ℂ | (y, u) ∈ A'} := by
    change Set.Finite (e.symm ⁻¹' {w : V | (y, w) ∈ A})
    exact Set.Finite.preimage e.symm.injective.injOn hfin
  have hz' : e z ∈ {u : Fin k → ℂ | (y, u) ∈ A'} := by
    change (y, e.symm (e z)) ∈ A
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hz
  obtain ⟨r, hr, hiso⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete hf.isDiscrete hz'
  have hi : ∃ r > 0, ∀ u, dist u (e z) < r → (y, u) ∈ A' → u = e z := by
    refine ⟨r, hr, fun u hu hua => ?_⟩
    have hm : u ∈ Metric.ball (e z) r ∩ {u | (y, u) ∈ A'} := ⟨hu, hua⟩
    rw [hiso] at hm
    exact hm
  obtain ⟨ρ, hρ, he⟩ := HodgeLean.Foundations.Analytic.anf_eliminate k ha' hi
  refine ⟨ρ, hρ, fun ε hε hερ => (he ε hε hερ).congr ?_⟩
  apply Filter.Eventually.of_forall
  intro y'
  constructor
  · rintro ⟨u, hu, hua⟩
    exact ⟨e.symm u, by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hu, hua⟩
  · rintro ⟨w, hw, hwa⟩
    refine ⟨e w, hw, ?_⟩
    simpa only [A', φ, Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hwa

/-- Simultaneous monic clusters have locally analytic evaluation images after fibre elimination. -/
theorem s2e_monic_cluster_evaluation_image_analytic {ι : Type} [Fintype ι] {n b k : ℕ}
    (d : ι → ℕ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ) (a : Fin n → ℂ)
    (hc : ∀ i j, AnalyticAt ℂ (c i j) a)
    (e : ((i : ι) → Fin (d i) → ℂ) ≃L[ℂ] (Fin k → ℂ))
    (F : ((i : ι) → Fin (d i) → ℂ) → (Fin b → ℂ))
    (z : (i : ι) → Fin (d i) → ℂ)
    (hz : ∀ i, monicPoly (c i) a = ∏ j, (Polynomial.X - Polynomial.C (z i j)))
    (hF : AnalyticAt ℂ F z) :
    ∃ ρ > 0, ∀ ε, 0 < ε → ε ≤ ρ →
      HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
        {ay : (Fin n → ℂ) × (Fin b → ℂ) | ∃ w : (i : ι) → Fin (d i) → ℂ,
          dist (e w) (e z) < ε ∧
          (∀ i, monicPoly (c i) ay.1 = ∏ j, (Polynomial.X - Polynomial.C (w i j))) ∧
          F w = ay.2} (a, F z) := by
  have hA := s2e_monic_cluster_incidence_analytic d c a hc z
  have hg := s2e_analytic_incidence_evaluation_graph _ a z hA F hF (F z)
  apply s2e_analytic_finite_projection_in_coordinates e _ (a, F z) z hg ⟨hz, rfl⟩
  exact (s2e_monic_cluster_rootTuples_finite_nonempty d c a).1.subset (fun w hw => hw.1)

/-- All exact tuples of finitely many centred monic clusters are uniformly small nearby. -/
theorem s2e_monic_cluster_rootTuples_eventually_small {ι : Type} [Fintype ι] {n : ℕ}
    (d : ι → ℕ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ)
    (hc : ∀ i j, ContinuousAt (c i j) 0) (hc0 : ∀ i j, c i j 0 = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in nhds (0 : Fin n → ℂ), ∀ z : (i : ι) → Fin (d i) → ℂ,
      (∀ i, monicPoly (c i) a = ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
      dist z 0 < ε := by
  have he := eventually_all.mpr (fun i =>
    s2e_monic_rootTuples_eventually_small (c i) (hc i) (hc0 i) hε)
  filter_upwards [he] with a ha z hz
  rw [dist_zero_right, pi_norm_lt_iff hε]
  intro i
  simpa only [dist_zero_right] using ha i (z i) (hz i)

/-- The full evaluation relation of simultaneous centred monic clusters is locally analytic. -/
theorem s2e_monic_cluster_evaluation_relation_analytic {ι : Type} [Fintype ι] {n b : ℕ}
    (d : ι → ℕ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ)
    (hc : ∀ i j, AnalyticAt ℂ (c i j) 0) (hc0 : ∀ i j, c i j 0 = 0)
    (F : ((i : ι) → Fin (d i) → ℂ) → (Fin b → ℂ)) (hF : AnalyticAt ℂ F 0) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {ay : (Fin n → ℂ) × (Fin b → ℂ) | ∃ z : (i : ι) → Fin (d i) → ℂ,
        (∀ i, monicPoly (c i) ay.1 = ∏ j, (Polynomial.X - Polynomial.C (z i j))) ∧
        F z = ay.2} (0, F 0) := by
  let V := (i : ι) → Fin (d i) → ℂ
  let e : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
    (Module.finBasis ℂ V).equivFun.toContinuousLinearEquiv
  have hz : ∀ i, monicPoly (c i) 0 =
      ∏ j, (Polynomial.X - Polynomial.C ((0 : V) i j)) := by
    intro i
    simp [monicPoly, hc0, V]
  obtain ⟨ρ, hρ, hproj⟩ := s2e_monic_cluster_evaluation_image_analytic d c 0 hc e F 0 hz hF
  have he : ∀ᶠ z : V in nhds 0, e z ∈ Metric.ball (e 0) ρ :=
    (e.continuous.tendsto 0).eventually (Metric.ball_mem_nhds (e 0) hρ)
  obtain ⟨δ, hδ, hδe⟩ := Metric.eventually_nhds_iff_ball.mp he
  have hs := s2e_monic_cluster_rootTuples_eventually_small d c
    (fun i j => (hc i j).continuousAt) hc0 hδ
  have hall : ∀ᶠ ay : (Fin n → ℂ) × (Fin b → ℂ) in nhds (0, F 0),
      ∀ z : V, (∀ i, monicPoly (c i) ay.1 =
        ∏ j, (Polynomial.X - Polynomial.C (z i j))) → dist z 0 < δ :=
    (continuous_fst.tendsto (0, F 0)).eventually hs
  apply (hproj ρ hρ le_rfl).congr
  filter_upwards [hall] with ay hay
  constructor
  · rintro ⟨z, _, hz, hy⟩
    exact ⟨z, hz, hy⟩
  · rintro ⟨z, hz, hy⟩
    exact ⟨z, hδe z (hay z hz), hz, hy⟩


/-- Independent permutations of clusters preserve evaluation of every exact presentation. -/
theorem s2e_cluster_symmetric_evaluation_eq {ι : Type} (d : ι → ℕ) {T : Type*}
    (F : ((i : ι) → Fin (d i) → ℂ) → T)
    (hF : ∀ z (σ : (i : ι) → Equiv.Perm (Fin (d i))),
      F (fun i j => z i (σ i j)) = F z)
    (z w : (i : ι) → Fin (d i) → ℂ)
    (h : ∀ i, (∏ j, (Polynomial.X - Polynomial.C (z i j))) =
      ∏ j, (Polynomial.X - Polynomial.C (w i j))) : F z = F w := by
  have hp : ∀ i, ∃ σ : Equiv.Perm (Fin (d i)), ∀ j, w i (σ j) = z i j := by
    intro i
    have hr (v : Fin (d i) → ℂ) :
        (∏ j, (Polynomial.X - Polynomial.C (v j))).roots = (List.ofFn v : Multiset ℂ) := by
      simpa only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
        Function.comp_def, List.prod_ofFn] using
        Polynomial.roots_multiset_prod_X_sub_C (List.ofFn v : Multiset ℂ)
    exact s2e_tuple_permutation_of_multiset_eq (z i) (w i)
      ((hr (z i)).symm.trans ((congrArg Polynomial.roots (h i)).trans (hr (w i))))
  choose σ hσ using hp
  have hz : z = fun i j => w i (σ i j) := funext (fun i => funext (fun j => (hσ i j).symm))
  rw [hz]
  exact hF w σ


/-- Evaluation of exact centred cluster presentations gives an analytic graph. -/
theorem s2e_monic_cluster_graph_analytic {ι : Type} [Fintype ι] {n b : ℕ}
    (d : ι → ℕ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ)
    (hc : ∀ i j, AnalyticAt ℂ (c i j) 0) (hc0 : ∀ i j, c i j 0 = 0)
    (F : ((i : ι) → Fin (d i) → ℂ) → (Fin b → ℂ)) (hF : AnalyticAt ℂ F 0)
    (g : (Fin n → ℂ) → (Fin b → ℂ))
    (hg : ∀ᶠ a in nhds (0 : Fin n → ℂ), ∀ z, (∀ i, monicPoly (c i) a =
      ∏ j, (Polynomial.X - Polynomial.C (z i j))) → F z = g a) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {ay : (Fin n → ℂ) × (Fin b → ℂ) | g ay.1 = ay.2} (0, g 0) := by
  have hz : ∀ i, monicPoly (c i) 0 =
      ∏ j, (Polynomial.X - Polynomial.C ((0 : (i : ι) → Fin (d i) → ℂ) i j)) := by
    intro i
    simp [monicPoly, hc0]
  rw [← hg.self_of_nhds 0 hz]
  apply (s2e_monic_cluster_evaluation_relation_analytic d c hc hc0 F hF).congr
  have he := (continuous_fst.tendsto (0, F 0)).eventually hg
  filter_upwards [he] with ay hay
  constructor
  · rintro ⟨z, hz, hy⟩
    exact (hay z hz).symm.trans hy
  · intro hy
    obtain ⟨z, hz⟩ := (s2e_monic_cluster_rootTuples_finite_nonempty d c ay.1).2
    exact ⟨z, hz, (hay z hz).trans hy⟩


/-- Exact centred cluster evaluation is continuous through simultaneous collisions. -/
theorem s2e_monic_cluster_evaluation_continuousAt {ι : Type} [Fintype ι] {n : ℕ}
    {T : Type*} [TopologicalSpace T]
    (d : ι → ℕ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ)
    (hc : ∀ i j, ContinuousAt (c i j) 0) (hc0 : ∀ i j, c i j 0 = 0)
    (F : ((i : ι) → Fin (d i) → ℂ) → T) (hF : ContinuousAt F 0)
    (g : (Fin n → ℂ) → T)
    (hg : ∀ᶠ a in nhds (0 : Fin n → ℂ), ∀ z,
      (∀ i, monicPoly (c i) a = ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
      F z = g a) : ContinuousAt g 0 := by
  let R := fun a : Fin n → ℂ =>
    (s2e_monic_cluster_rootTuples_finite_nonempty d c a).2.choose
  have hR (a : Fin n → ℂ) : ∀ i, monicPoly (c i) a =
      ∏ j, (Polynomial.X - Polynomial.C (R a i j)) :=
    (s2e_monic_cluster_rootTuples_finite_nonempty d c a).2.choose_spec
  have ht : Tendsto R (nhds 0) (nhds 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [s2e_monic_cluster_rootTuples_eventually_small d c hc hc0 hε] with a ha
    exact ha (R a) (hR a)
  have hz : ∀ i, monicPoly (c i) 0 =
      ∏ j, (Polynomial.X - Polynomial.C ((0 : (i : ι) → Fin (d i) → ℂ) i j)) := by
    intro i
    simp [monicPoly, hc0]
  change Tendsto g (nhds 0) (nhds (g 0))
  rw [← hg.self_of_nhds 0 hz]
  apply (hF.tendsto.comp ht).congr'
  filter_upwards [hg] with a ha
  exact ha (R a) (hR a)


/-- Full order at the chart origin forces every lower monic coefficient to vanish. -/
theorem s2e_monic_coefficients_zero_of_full_order {n d : ℕ}
    (c : Fin d → (Fin n → ℂ) → ℂ) (a : Fin n → ℂ)
    (horder : analyticOrderAt (fun w => (monicPoly c a).eval w) 0 = (d : ℕ∞)) :
    ∀ j, c j a = 0 := by
  classical
  obtain ⟨z, hz⟩ := s2e_monic_polynomial_exists_root_tuple (monicPoly c a)
    (spec_monicPoly_aux c a).1 (spec_monicPoly_aux c a).2.1
  have hcard : Fintype.card {j : Fin d // z j = 0} = d := by
    have h := (s2e_rootTuple_analytic_order (monicPoly c a) z hz 0).symm.trans horder
    exact_mod_cast h
  have hu : {j : Fin d | z j = 0} = Set.univ := by
    apply (set_fintype_card_eq_univ_iff _).mp
    change Fintype.card {j : Fin d // z j = 0} = Fintype.card (Fin d)
    simpa only [Fintype.card_fin] using hcard
  have hz0 : z = 0 := by
    funext j
    have hj : j ∈ {j : Fin d | z j = 0} := by rw [hu]; trivial
    exact hj
  have hq : monicPoly c a = Polynomial.X ^ d := by
    simpa [hz0] using hz
  intro j
  have he := congrArg (fun q : Polynomial ℂ => q.coeff (j : ℕ)) hq
  simpa [gaga5b_coeff_monicPoly, ne_of_lt j.isLt, ← Fin.ext_iff] using he


/-- Actual local canonical polynomials are centred at their initial zero. -/
theorem s2e_holomorphicFamily_centred_local_polynomial
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ i, a i • b i : b3_HolForm E C) ≠ 0)
    (p : C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (r δ : ℝ) (c : Fin d → (Fin n → ℂ) → ℂ),
      (d : ℤ) = b4c_divForm (hE := hE) (∑ i, a i • b i : b3_HolForm E C) p ∧
      0 < r ∧ r < ε ∧ 0 < δ ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈
          (extChartAt 𝓘(ℂ, E) p).target) ∧
      (∀ j, AnalyticOnNhd ℂ (c j) (Metric.ball a δ)) ∧
      (∀ j, c j a = 0) ∧
      (∀ᶠ a' in 𝓝 a,
        (∑ i, a' i • b i : b3_HolForm E C) ≠ 0 ∧
        (∀ z, HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a', z) = 0 →
          z ∈ Metric.ball (0 : ℂ) r) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) r, ∃ e : ℕ,
          analyticOrderAt
            (fun w => HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a', w)) z = e ∧
          (e : ℤ) = b4c_divForm (hE := hE) (∑ i, a' i • b i : b3_HolForm E C)
            ((extChartAt 𝓘(ℂ, E) p).symm
              (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z))) := by
  obtain ⟨d, r, δ, c, hD, hr, hrε, hδ, ht, hc, hrest⟩ :=
    s2e_holomorphicFamily_local_polynomial hE b a hne p hε
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

/-- Centred local root tuples retain the actual nearby canonical multiplicities. -/
theorem s2e_holomorphicFamily_centred_local_root_multiplicities
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ i, a i • b i : b3_HolForm E C) ≠ 0)
    (p : C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (r δ : ℝ) (c : Fin d → (Fin n → ℂ) → ℂ),
      (d : ℤ) = b4c_divForm (hE := hE) (∑ i, a i • b i : b3_HolForm E C) p ∧
      0 < r ∧ r < ε ∧ 0 < δ ∧
      (∀ w ∈ Metric.closedBall (0 : ℂ) r,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) p).target) ∧
      (∀ j, AnalyticOnNhd ℂ (c j) (Metric.ball a δ)) ∧
      (∀ j, c j a = 0) ∧
      ∀ᶠ a' in nhds a,
        (∑ i, a' i • b i : b3_HolForm E C) ≠ 0 ∧
        ∀ z : Fin d → ℂ, monicPoly c a' = ∏ i, (Polynomial.X - Polynomial.C (z i)) →
          (∀ i, z i ∈ Metric.ball (0 : ℂ) r) ∧
          ∀ w ∈ Metric.ball (0 : ℂ) r,
            (Fintype.card {i : Fin d // z i = w} : ℤ) =
              b4c_divForm (hE := hE) (∑ i, a' i • b i : b3_HolForm E C)
                ((extChartAt 𝓘(ℂ, E) p).symm
                  (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE w)) := by
  obtain ⟨d, r, δ, c, hd, hr, hrε, hδ, ht, hc, hc0, he⟩ :=
    s2e_holomorphicFamily_centred_local_polynomial hE b a hne p hε
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
/-- Finite canonical clusters have simultaneous centred analytic polynomial presentations. -/
theorem s2e_holomorphicFamily_finite_centred_local_polynomials
    [T2Space C] [CompactSpace C] [ConnectedSpace C] {ι : Type} [Fintype ι]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ j, a j • b j : b3_HolForm E C) ≠ 0)
    (p : ι → C) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ (d : ι → ℕ) (r δ : ι → ℝ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ),
      (∀ i, (d i : ℤ) = b4c_divForm (hE := hE) (∑ j, a j • b j : b3_HolForm E C) (p i)) ∧
      (∀ i, 0 < r i ∧ r i < ε i ∧ 0 < δ i) ∧
      (∀ i w, w ∈ Metric.closedBall (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (p i)).target) ∧
      (∀ i j, AnalyticOnNhd ℂ (c i j) (Metric.ball a (δ i))) ∧
      (∀ i j, c i j a = 0) ∧
      ∀ᶠ a' in nhds a,
        (∑ j, a' j • b j : b3_HolForm E C) ≠ 0 ∧
        ∀ i (z : Fin (d i) → ℂ),
          monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z j)) →
          (∀ j, z j ∈ Metric.ball (0 : ℂ) (r i)) ∧
          ∀ w ∈ Metric.ball (0 : ℂ) (r i),
            (Fintype.card {j : Fin (d i) // z j = w} : ℤ) =
              b4c_divForm (hE := hE) (∑ j, a' j • b j : b3_HolForm E C)
                ((extChartAt 𝓘(ℂ, E) (p i)).symm
                  (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)) := by
  choose d r δ c hd hr hre hδ ht hc hc0 he using fun i =>
    s2e_holomorphicFamily_centred_local_root_multiplicities hE b a hne (p i) (hε i)
  refine ⟨d, r, δ, c, hd, fun i => ⟨hr i, hre i, hδ i⟩, ht, hc, hc0, ?_⟩
  filter_upwards [eventually_all.mpr he, s2e_holomorphicFamily_eventually_ne_zero b a hne]
    with a' ha' hn'
  exact ⟨hn', fun i => (ha' i).2⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Centred simultaneous polynomial clusters recover every nearby canonical divisor. -/
theorem s2e_holomorphicFamily_centred_cluster_divisor_presentation
    [T2Space C] [CompactSpace C] [ConnectedSpace C] {ι : Type} [Fintype ι]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ j, a j • b j : b3_HolForm E C) ≠ 0)
    (p : ι → C) (hp : Function.Injective p)
    (hsum : (∑ i, b4c_divForm (hE := hE) (∑ j, a j • b j : b3_HolForm E C) (p i)) =
      b4c_deg (b4c_divForm (E := E) (C := C) (hE := hE) (∑ j, a j • b j : b3_HolForm E C))) :
    ∃ (d : ι → ℕ) (r δ : ι → ℝ) (c : (i : ι) → Fin (d i) → (Fin n → ℂ) → ℂ),
      (∀ i, (d i : ℤ) = b4c_divForm (hE := hE) (∑ j, a j • b j : b3_HolForm E C) (p i)) ∧
      (∀ i, 0 < r i ∧ 0 < δ i) ∧
      (∀ i w, w ∈ Metric.closedBall (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (p i)).target) ∧
      (∀ i j, AnalyticOnNhd ℂ (c i j) (Metric.ball a (δ i))) ∧
      (∀ i j, c i j a = 0) ∧
      ∀ᶠ a' in nhds a,
        (∑ j, a' j • b j : b3_HolForm E C) ≠ 0 ∧
        ∀ z : (i : ι) → Fin (d i) → ℂ,
          (∀ i, monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
          (∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i)) ∧
          b4c_divForm (hE := hE) (∑ j, a' j • b j : b3_HolForm E C) =
            ∑ i, ∑ j, Finsupp.single
              ((extChartAt 𝓘(ℂ, E) (p i)).symm
                (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE (z i j))) (1 : ℤ) := by
  obtain ⟨ε, hε, _, hsep⟩ := s2e_curve_chart_discs_disjoint hE p hp
  obtain ⟨d, r, δ, c, hd, hr, ht, hc, hc0, he⟩ :=
    s2e_holomorphicFamily_finite_centred_local_polynomials hE b a hne p ε hε
  refine ⟨d, r, δ, c, hd, fun i => ⟨(hr i).1, (hr i).2.2⟩, ht, hc, hc0, ?_⟩
  filter_upwards [he] with a' ha'
  refine ⟨ha'.1, fun z hz => ?_⟩
  have hzi : ∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i) :=
    fun i => (ha'.2 i (z i) (hz i)).1
  refine ⟨hzi, ?_⟩
  have hdeg : b4c_deg (b4c_divForm (E := E) (C := C) (hE := hE)
      (∑ j, a' j • b j : b3_HolForm E C)) = ((∑ i, d i : ℕ) : ℤ) := by
    rw [s2e_holomorphic_divisor_degree hE _ ha'.1,
      ← s2e_holomorphic_divisor_degree hE _ hne, ← hsum]
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => (hd i).symm)
  apply s2e_holomorphic_divisor_eq_disjoint_local_tuples hE _ ha'.1 p r d z
    (fun i w hw => ht i w (Metric.ball_subset_closedBall hw)) hzi
    (fun i => (ha'.2 i (z i) (hz i)).2) hdeg
  intro i j hij
  exact (hsep hij).mono
    (Set.image_mono (Metric.ball_subset_ball (hr i).2.1.le))
    (Set.image_mono (Metric.ball_subset_ball (hr j).2.1.le))


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual initial canonical support has a centred simultaneous divisor presentation. -/
theorem s2e_holomorphicFamily_centred_support_divisor_presentation
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (b : Fin n → b3_HolForm E C)
    (a : Fin n → ℂ) (hne : (∑ j, a j • b j : b3_HolForm E C) ≠ 0) :
    let D := b4c_divForm (E := E) (C := C) (hE := hE) (∑ j, a j • b j : b3_HolForm E C)
    ∃ (d : D.support → ℕ) (r δ : D.support → ℝ) (c : (i : D.support) → Fin (d i) → (Fin n → ℂ) → ℂ),
      (∀ i, (d i : ℤ) = b4c_divForm (hE := hE) (∑ j, a j • b j : b3_HolForm E C) (i : C)) ∧
      (∀ i, 0 < r i ∧ 0 < δ i) ∧
      (∀ i w, w ∈ Metric.closedBall (0 : ℂ) (r i) →
        extChartAt 𝓘(ℂ, E) (i : C) (i : C) + b4cov_lineEquiv hE w ∈
          (extChartAt 𝓘(ℂ, E) (i : C)).target) ∧
      (∀ i j, AnalyticOnNhd ℂ (c i j) (Metric.ball a (δ i))) ∧
      (∀ i j, c i j a = 0) ∧
      ∀ᶠ a' in nhds a,
        (∑ j, a' j • b j : b3_HolForm E C) ≠ 0 ∧
        ∀ z : (i : D.support) → Fin (d i) → ℂ,
          (∀ i, monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
          (∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i)) ∧
          b4c_divForm (hE := hE) (∑ j, a' j • b j : b3_HolForm E C) =
            ∑ i : D.support, ∑ j : Fin (d i), Finsupp.single
              ((extChartAt 𝓘(ℂ, E) (i : C)).symm
                (extChartAt 𝓘(ℂ, E) (i : C) (i : C) + b4cov_lineEquiv hE (z i j))) (1 : ℤ) := by
  dsimp only
  let D := b4c_divForm (E := E) (C := C) (hE := hE) (∑ j, a j • b j : b3_HolForm E C)
  apply s2e_holomorphicFamily_centred_cluster_divisor_presentation hE b a hne
    (fun i : D.support => (i : C)) Subtype.val_injective
  change (∑ i : D.support, D i) = b4c_deg D
  simp [b4c_deg, Finsupp.sum, Finset.sum_attach]


open CategoryTheory AlgebraicGeometry in
/-- Centred polynomial clusters evaluate to the actual nearby canonical quotient point. -/
theorem s2e_canonicalFamily_centred_cluster_evaluation
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (N : ℕ) (γ : HodgeLean.Adapters.g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    {m : ℕ} (b : Fin m → b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))
    (a : Fin m → ℂ) (hne : (∑ j, a j • b j : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) ≠ 0) :
    let hE := Module.finrank_fin_fun (n := 1) ℂ
    let D := b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z) (hE := hE) (∑ j, a j • b j : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))
    ∃ (d : D.support → ℕ) (c : (i : D.support) → Fin (d i) → (Fin m → ℂ) → ℂ)
      (e : Fin N ≃ ((i : D.support) × Fin (d i))),
      (∀ i j, AnalyticAt ℂ (c i j) a) ∧ (∀ i j, c i j a = 0) ∧
      ∀ᶠ a' in nhds a, ∃ hn : (∑ j, a' j • b j : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) ≠ 0,
        ∀ z : (i : D.support) → Fin (d i) → ℂ,
          (∀ i, monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
          s2e_canonicalQuotientPoint Z B N γ hg (Projectivization.mk ℂ (∑ j, a' j • b j : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) hn) =
            Point.map γ (s2_lift N (fun k =>
              (extChartAt 𝓘(ℂ, Fin 1 → ℂ) ((e k).1 : ComplexPoint Z)).symm
                (extChartAt 𝓘(ℂ, Fin 1 → ℂ) ((e k).1 : ComplexPoint Z) ((e k).1 : ComplexPoint Z) +
                  b4cov_lineEquiv hE (z (e k).1 (e k).2)))) := by
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let hE := Module.finrank_fin_fun (n := 1) ℂ
  let D := b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z) (hE := hE) (∑ j, a j • b j : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))
  obtain ⟨d, r, δ, c, hd, hr, ht, hc, hc0, he⟩ :=
    s2e_holomorphicFamily_centred_support_divisor_presentation hE b a hne
  have hsum : (∑ i, d i) = N := by
    have hi : ((∑ i, d i : ℕ) : ℤ) = (N : ℤ) := by
      rw [Nat.cast_sum]
      calc
        (∑ i, (d i : ℤ)) = ∑ i : D.support, D i :=
          Finset.sum_congr rfl (fun i _ => hd i)
        _ = b4c_deg D := by simp [b4c_deg, Finsupp.sum, Finset.sum_attach]
        _ = (N : ℤ) := (s2e_holomorphic_divisor_degree hE _ hne).trans hg.symm
    exact_mod_cast hi
  let e : Fin N ≃ ((i : D.support) × Fin (d i)) :=
    (Fintype.equivFinOfCardEq (show Fintype.card ((i : D.support) × Fin (d i)) = N by
      simpa only [Fintype.card_sigma, Fintype.card_fin] using hsum)).symm
  refine ⟨d, c, e, fun i j => hc i j a (Metric.mem_ball_self (hr i).2), hc0, ?_⟩
  filter_upwards [he] with a' ha'
  refine ⟨ha'.1, fun z hz => ?_⟩
  exact s2e_canonicalQuotientPoint_eq_clusters Z B N γ hγ hg _ ha'.1 d e
    (fun i j => (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (i : ComplexPoint Z)).symm
      (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (i : ComplexPoint Z) (i : ComplexPoint Z) +
        b4cov_lineEquiv hE (z i j))) (ha'.2 z hz).2


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.Adapters in
/-- Native quotient evaluation is analytic in centred scalar curve coordinates. -/
theorem s2e_curve_tuple_evaluation_chart_analytic
    (Z B : Over (Spec ↧ℂ)) [IsProjective Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] (N q : ℕ) [SmoothOfRelativeDimension q B.hom]
    (γ : g3_power Z N ⟶ B) (p : Fin N → ComplexPoint Z)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (L : V →L[ℂ] (Fin N → ℂ)) :
    AnalyticAt ℂ (fun w : V => localChart B q (Point.map γ (s2_lift N p))
      (Point.map γ (s2_lift N (fun k =>
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k)).symm
          (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k) (p k) +
            b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) (L w k)))))) 0 := by
  letI : SmoothOfRelativeDimension (N * 1) (g3_power Z N).hom :=
    spec_g3_smoothOfRelativeDimension_power Z 1 N
  have hp : ∀ i, Point.map (g3_proj Z N i) (s2_lift N p) = p i := by
    intro i
    exact s2_check_lift_proj N p i
  have hn := s2e_projective_tuple_map_chart_analytic Z B N 1 q γ (s2_lift N p)
  simp only [hp] at hn
  let A := fun w : V => fun i : Fin N => localChart Z 1 (p i) (p i) +
    b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) (L w i)
  have ha : AnalyticAt ℂ A 0 := by
    apply AnalyticAt.pi
    intro i
    exact analyticAt_const.add
      (((b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).toContinuousLinearMap.analyticAt _).comp
        (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp L).analyticAt 0))
  have hA0 : A 0 = fun i => localChart Z 1 (p i) (p i) := by
    simp [A]
  have hh := hn.comp_of_eq ha hA0
  have hchart (x : ComplexPoint Z) : chartAt (Fin 1 → ℂ) x = localChart Z 1 x := rfl
  simpa only [hchart, A, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, hchart] using hh


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint in
/-- The actual canonical quotient family has an analytic graph in affine parameter and native target charts. -/
theorem s2e_canonicalFamily_chart_graph_analytic
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (N q : ℕ) [SmoothOfRelativeDimension q B.hom]
    (γ : HodgeLean.Adapters.g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    {m : ℕ} (b : Fin m → b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))
    (a : Fin m → ℂ) (hne : (∑ j, a j • b j) ≠ 0) :
    let Q := s2e_canonicalQuotientPoint Z B N γ hg (Projectivization.mk ℂ (∑ j, a j • b j) hne)
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {ty : (Fin m → ℂ) × (Fin q → ℂ) |
        ∃ hn : (∑ j, (a + ty.1) j • b j) ≠ 0,
          localChart B q Q (s2e_canonicalQuotientPoint Z B N γ hg
            (Projectivization.mk ℂ (∑ j, (a + ty.1) j • b j) hn)) = ty.2}
      (0, localChart B q Q Q) := by
  let Q := s2e_canonicalQuotientPoint Z B N γ hg (Projectivization.mk ℂ (∑ j, a j • b j) hne)
  let hE := Module.finrank_fin_fun (n := 1) ℂ
  let D := b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z) (hE := hE)
    (∑ j, a j • b j : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))
  obtain ⟨d, c, e, hc, hc0, he⟩ := s2e_canonicalFamily_centred_cluster_evaluation Z B N γ hγ hg b a hne
  let V := (i : D.support) → Fin (d i) → ℂ
  let p : Fin N → ComplexPoint Z := fun k => (e k).1
  let L : V →L[ℂ] (Fin N → ℂ) := ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (e k).2 : (Fin (d (e k).1) → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj (e k).1)
  let F : V → (Fin q → ℂ) := fun z => localChart B q Q
    (Point.map γ (s2_lift N (fun k =>
      (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k)).symm
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k) (p k) + b4cov_lineEquiv hE (L z k)))))
  have hz0 : ∀ i, monicPoly (c i) a =
      ∏ j, (Polynomial.X - Polynomial.C ((0 : V) i j)) := by
    intro i
    simp [monicPoly, hc0, V]
  have hQ : Q = Point.map γ (s2_lift N p) := by
    obtain ⟨hn, hh⟩ := he.self_of_nhds
    simpa only [Pi.zero_apply, map_zero, add_zero, extChartAt_to_inv] using hh 0 hz0
  have hF : AnalyticAt ℂ F 0 := by
    have hh := s2e_curve_tuple_evaluation_chart_analytic Z B N q γ p L
    rw [← hQ] at hh
    exact hh
  have hF0 : F 0 = localChart B q Q Q := by
    simp only [F, map_zero, Pi.zero_apply, add_zero, extChartAt_to_inv]
    rw [← hQ]
  let c' := fun i j t => c i j (a + t)
  have hc' : ∀ i j, AnalyticAt ℂ (c' i j) 0 := by
    intro i j
    exact (hc i j).comp_of_eq (analyticAt_const.add analyticAt_id) (add_zero a)
  have hc0' : ∀ i j, c' i j 0 = 0 := by
    intro i j
    simpa only [c', add_zero] using hc0 i j
  have hrel := s2e_monic_cluster_evaluation_relation_analytic d c' hc' hc0' F hF
  rw [hF0] at hrel
  apply hrel.congr
  have het : ∀ᶠ t : Fin m → ℂ in nhds 0, ∃ hn : (∑ j, (a + t) j • b j) ≠ 0,
      ∀ z : V, (∀ i, monicPoly (c i) (a + t) =
        ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
      s2e_canonicalQuotientPoint Z B N γ hg (Projectivization.mk ℂ (∑ j, (a + t) j • b j) hn) =
        Point.map γ (s2_lift N (fun k =>
          (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k)).symm
            (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k) (p k) + b4cov_lineEquiv hE (L z k)))) := by
    have ht : Tendsto (fun t : Fin m → ℂ => a + t) (nhds 0) (nhds a) := by
      simpa only [add_zero] using
        (show Continuous (fun t : Fin m → ℂ => a + t) from continuous_const.add continuous_id).tendsto
          (0 : Fin m → ℂ)
    exact ht.eventually he
  have hey := (continuous_fst.tendsto (0, localChart B q Q Q)).eventually het
  filter_upwards [hey] with ty hty
  obtain ⟨hn, hval⟩ := hty
  constructor
  · rintro ⟨z, hz, hy⟩
    refine ⟨hn, ?_⟩
    rw [hval z hz]
    exact hy
  · rintro ⟨hn', hy⟩
    obtain ⟨z, hz⟩ := (s2e_monic_cluster_rootTuples_finite_nonempty d c' ty.1).2
    refine ⟨z, hz, ?_⟩
    rw [hval z hz] at hy
    exact hy


/-- A continuous local section identifies a finite analytic projection with its full target locus. -/
theorem s2e_analytic_projection_of_local_section {B V : Type}
    [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ}
    (e : V ≃L[ℂ] (Fin k → ℂ)) (A : Set (B × V)) (G : Set B)
    (y : B) (z : V)
    (hA : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear A (y, z))
    (hz : (y, z) ∈ A) (hfin : Set.Finite {w : V | (y, w) ∈ A})
    (r : B → V) (hr : ContinuousAt r y) (hry : r y = z)
    (himage : ∀ y' w, (y', w) ∈ A → y' ∈ G)
    (hsection : ∀ᶠ y' in nhds y, y' ∈ G → (y', r y') ∈ A) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear G y := by
  obtain ⟨ρ, hρ, he⟩ := s2e_analytic_finite_projection_in_coordinates e A y z hA hz hfin
  have hc : ContinuousAt (fun y' => e (r y')) y := e.continuous.continuousAt.comp hr
  have hb : ∀ᶠ y' in nhds y, dist (e (r y')) (e z) < ρ := by
    have hh := hc.eventually (Metric.ball_mem_nhds (e (r y)) hρ)
    simpa only [hry, Metric.mem_ball] using hh
  apply (he ρ hρ le_rfl).congr
  filter_upwards [hb, hsection] with y' hy' hs
  constructor
  · rintro ⟨w, _, hw⟩
    exact himage y' w hw
  · intro hy
    exact ⟨r y', hy', hs hy⟩


open CategoryTheory AlgebraicGeometry in
/-- Evaluation of centred curve tuples is continuous in the actual quotient topology. -/
theorem s2e_curve_tuple_evaluation_continuousAt
    (Z B : Over (Spec ↧ℂ)) [IsProjective Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] (N : ℕ)
    (γ : HodgeLean.Adapters.g3_power Z N ⟶ B) (p : Fin N → ComplexPoint Z)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (L : V →L[ℂ] (Fin N → ℂ)) :
    ContinuousAt (fun w : V => Point.map γ (s2_lift N (fun k =>
      (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k)).symm
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k) (p k) +
          b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) (L w k))))) 0 := by
  apply (Point.continuous_map γ).continuousAt.comp
  apply (s2e_projective_tuple_lift_continuous Z N).continuousAt.comp
  apply continuousAt_pi.mpr
  intro k
  have hl : ContinuousAt (fun w : V =>
      extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k) (p k) +
        b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) (L w k)) 0 :=
    continuousAt_const.add
      ((b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).continuousAt.comp
        ((continuous_apply k).comp L.continuous).continuousAt)
  exact (continuousAt_extChartAt_symm (I := 𝓘(ℂ, Fin 1 → ℂ)) (p k)).comp_of_eq hl
    (by simp)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory AlgebraicGeometry in
/-- Any local evaluation of the actual canonical family is continuous through repeated zeros. -/
theorem s2e_canonicalFamily_evaluation_continuousAt
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (N : ℕ) (γ : HodgeLean.Adapters.g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    {m : ℕ} (b : Fin m → b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))
    (a : Fin m → ℂ) (hne : (∑ j, a j • b j) ≠ 0)
    (g : (Fin m → ℂ) → ComplexPoint B)
    (hge : ∀ᶠ a' in nhds a, ∃ hn : (∑ j, a' j • b j) ≠ 0,
      g a' = s2e_canonicalQuotientPoint Z B N γ hg
        (Projectivization.mk ℂ (∑ j, a' j • b j) hn)) : ContinuousAt g a := by
  let hE := Module.finrank_fin_fun (n := 1) ℂ
  let D := b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z) (hE := hE)
    (∑ j, a j • b j : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))
  obtain ⟨d, c, e, hc, hc0, he⟩ :=
    s2e_canonicalFamily_centred_cluster_evaluation Z B N γ hγ hg b a hne
  let V := (i : D.support) → Fin (d i) → ℂ
  let p : Fin N → ComplexPoint Z := fun k => (e k).1
  let L : V →L[ℂ] (Fin N → ℂ) := ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (e k).2 : (Fin (d (e k).1) → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj (e k).1)
  let F : V → ComplexPoint B := fun z => Point.map γ (s2_lift N (fun k =>
    (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k)).symm
      (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k) (p k) + b4cov_lineEquiv hE (L z k))))
  have hF : ContinuousAt F 0 := s2e_curve_tuple_evaluation_continuousAt Z B N γ p L
  let c' := fun i j t => c i j (a + t)
  have hc' : ∀ i j, ContinuousAt (c' i j) 0 := by
    intro i j
    exact (hc i j).continuousAt.comp_of_eq
      (continuousAt_const.add continuousAt_id) (add_zero a)
  have hc0' : ∀ i j, c' i j 0 = 0 := by
    intro i j
    simpa only [c', add_zero] using hc0 i j
  have ht : Tendsto (fun t : Fin m → ℂ => a + t) (nhds 0) (nhds a) := by
    simpa only [add_zero] using
      (show Continuous (fun t : Fin m → ℂ => a + t) from continuous_const.add continuous_id).tendsto
        (0 : Fin m → ℂ)
  have htrans : ContinuousAt (fun t => g (a + t)) 0 := by
    apply s2e_monic_cluster_evaluation_continuousAt d c' hc' hc0' F hF
    filter_upwards [ht.eventually he, ht.eventually hge] with t he' hg'
    obtain ⟨hn, hval⟩ := he'
    obtain ⟨hn', hg'⟩ := hg'
    intro z hz
    exact (hval z hz).symm.trans hg'.symm
  have hh := htrans.comp_of_eq
    (show ContinuousAt (fun x : Fin m → ℂ => x - a) a from
      continuousAt_id.sub continuousAt_const) (sub_self a)
  change ContinuousAt (fun x => g (a + (x - a))) a at hh
  have heq : (fun x => g (a + (x - a))) = g := by
    funext x
    congr 1
    abel
  rwa [heq] at hh

end HodgeLean.Foundations.Program

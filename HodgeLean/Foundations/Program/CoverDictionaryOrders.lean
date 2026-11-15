import HodgeLean.Foundations.Program.CoverDictionaryEuler
import HodgeLean.Foundations.Program.CoverDictionaryBranch
import HodgeLean.Foundations.Program.KernelFramesFamilyTaylor

/-! # B6-5 stage 5d, stage four: orders of local forms in one complex variable

General statements. A meromorphic germ is bounded on a punctured neighbourhood exactly when its
order is nonnegative (`caf_bdd_iff_order_nonneg`). For a local parameter `κ` with a simple zero,
the order of `κⁿ · ρ(t + κᵉ) · u` is `n + e · ord_t ρ + ord u` (`caf_order_comp_mul`). Orders of
the components of a vector are preserved by an analytic matrix that is invertible at the point
(`caf_order_matrix_iff`), and an analytic matrix with value `1` respects a pattern of bounds
differing by at most one (`caf_order_unipotent`). The order of a rational function at a point is
nonnegative exactly where its denominator does not vanish (`caf_order_ratFunc_nonneg_iff`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Matrix
open scoped Topology
namespace HodgeLean.Foundations.Program

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Boundedness and order.** A germ meromorphic at `z₀` is bounded on a punctured
neighbourhood exactly when its order there is nonnegative. -/
theorem caf_bdd_iff_order_nonneg (f : ℂ → E) (z₀ : ℂ) (hf : MeromorphicAt f z₀) :
    (∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀, ‖f z‖ ≤ B) ↔ 0 ≤ meromorphicOrderAt f z₀ := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hneg
    push Not at hneg
    have ht := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
    rw [← tendsto_norm_atTop_iff_cobounded] at ht
    have h2 := ht.eventually (eventually_gt_atTop B)
    obtain ⟨z, h1, h3⟩ := (hB.and h2).exists
    linarith
  · intro h
    obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf h
    refine ⟨‖c‖ + 1, ?_⟩
    have := hc.norm.eventually (gt_mem_nhds (lt_add_one ‖c‖))
    filter_upwards [this] with z hz using hz.le

/-- Integer form of the order condition: `0 ≤ n + e k + c` with `c = e − 1`. -/
theorem caf_int_div_le_iff (e : ℕ) (he : 0 < e) (n k : ℤ) :
    0 ≤ n + k * e + ((e : ℤ) - 1) ↔ (-n) / (e : ℤ) ≤ k := by
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  rw [Int.ediv_le_iff_le_mul he']
  generalize k * (e : ℤ) = m
  omega

/-- A local parameter with a simple zero has order one. -/
theorem caf_order_param (κ : ℂ → ℂ) (z₀ : ℂ) (hκ : AnalyticAt ℂ κ z₀) (hκ0 : κ z₀ = 0)
    (hκ' : deriv κ z₀ ≠ 0) : meromorphicOrderAt κ z₀ = 1 := by
  have h := hκ.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hκ'
  simp only [hκ0, sub_zero] at h
  rw [hκ.meromorphicOrderAt_eq, show analyticOrderAt (fun z ↦ κ z) z₀ = 1 from h]
  rfl

/-- The analytic order of `κᵉ` for a simple zero `κ`. -/
theorem caf_analyticOrder_param_pow (κ : ℂ → ℂ) (z₀ : ℂ) (hκ : AnalyticAt ℂ κ z₀)
    (hκ0 : κ z₀ = 0) (hκ' : deriv κ z₀ ≠ 0) (e : ℕ) :
    analyticOrderAt (fun z ↦ κ z ^ e) z₀ = e := by
  have h := hκ.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hκ'
  simp only [hκ0, sub_zero] at h
  rw [show (fun z ↦ κ z ^ e) = κ ^ e from rfl, analyticOrderAt_pow hκ,
    show analyticOrderAt κ z₀ = 1 from h, nsmul_one]

/-- **Order under `y ↦ t + κᵉ`.** -/
theorem caf_order_comp_param (ρ : ℂ → E) (t z₀ : ℂ) (κ : ℂ → ℂ) (hκ : AnalyticAt ℂ κ z₀)
    (hκ0 : κ z₀ = 0) (hκ' : deriv κ z₀ ≠ 0) (e : ℕ) (he : 0 < e) (hρ : MeromorphicAt ρ t) :
    MeromorphicAt (fun z ↦ ρ (t + κ z ^ e)) z₀ ∧
      meromorphicOrderAt (fun z ↦ ρ (t + κ z ^ e)) z₀ = meromorphicOrderAt ρ t * e := by
  set g : ℂ → ℂ := fun z ↦ t + κ z ^ e
  have hg : AnalyticAt ℂ g z₀ := analyticAt_const.add (hκ.pow e)
  have hgz : g z₀ = t := by simp [g, hκ0, zero_pow he.ne']
  have hord : analyticOrderAt (fun z ↦ g z - g z₀) z₀ = e := by
    rw [hgz]
    simp only [g, add_sub_cancel_left]
    exact caf_analyticOrder_param_pow κ z₀ hκ hκ0 hκ' e
  have hρ' : MeromorphicAt ρ (g z₀) := by rw [hgz]; exact hρ
  refine ⟨hρ'.comp_analyticAt hg, ?_⟩
  have hnc : ¬ EventuallyConst g (𝓝 z₀) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hord]
    exact ENat.natCast_ne_top e
  have := hρ'.meromorphicOrderAt_comp hg hnc
  rw [hord, hgz] at this
  exact this

/-- **The order of `κⁿ · ρ(t + κᵉ) · u`.** -/
theorem caf_order_comp_mul (ρ : ℂ → ℂ) (t z₀ : ℂ) (κ u : ℂ → ℂ) (hκ : AnalyticAt ℂ κ z₀)
    (hκ0 : κ z₀ = 0) (hκ' : deriv κ z₀ ≠ 0) (e : ℕ) (he : 0 < e) (hρ : MeromorphicAt ρ t)
    (hu : MeromorphicAt u z₀) (n : ℤ) :
    MeromorphicAt (fun z ↦ κ z ^ n * ρ (t + κ z ^ e) * u z) z₀ ∧
      meromorphicOrderAt (fun z ↦ κ z ^ n * ρ (t + κ z ^ e) * u z) z₀ =
        (n : WithTop ℤ) + meromorphicOrderAt ρ t * e + meromorphicOrderAt u z₀ := by
  obtain ⟨hc, hco⟩ := caf_order_comp_param ρ t z₀ κ hκ hκ0 hκ' e he hρ
  have hk : MeromorphicAt (fun z ↦ κ z ^ n) z₀ := hκ.meromorphicAt.zpow n
  have hko : meromorphicOrderAt (fun z ↦ κ z ^ n) z₀ = n := by
    rw [show (fun z ↦ κ z ^ n) = κ ^ n from rfl, meromorphicOrderAt_zpow hκ.meromorphicAt,
      caf_order_param κ z₀ hκ hκ0 hκ']
    simp
  refine ⟨(hk.mul hc).mul hu, ?_⟩
  rw [show (fun z ↦ κ z ^ n * ρ (t + κ z ^ e) * u z) =
      ((fun z ↦ κ z ^ n) * fun z ↦ ρ (t + κ z ^ e)) * u from rfl,
    meromorphicOrderAt_mul (hk.mul hc) hu, meromorphicOrderAt_mul hk hc, hko, hco]

/-- **The order condition for `κⁿ · ρ(t + κᵉ) · u`** with `ord u = c`. -/
theorem caf_order_comp_mul_nonneg_iff (ρ : ℂ → ℂ) (t z₀ : ℂ) (κ u : ℂ → ℂ)
    (hκ : AnalyticAt ℂ κ z₀) (hκ0 : κ z₀ = 0) (hκ' : deriv κ z₀ ≠ 0) (e : ℕ) (he : 0 < e)
    (hρ : MeromorphicAt ρ t) (hu : MeromorphicAt u z₀) (c : ℤ)
    (huo : meromorphicOrderAt u z₀ = c) (n : ℤ) (k : ℤ)
    (hk : ∀ o : ℤ, 0 ≤ n + o * e + c ↔ k ≤ o) :
    0 ≤ meromorphicOrderAt (fun z ↦ κ z ^ n * ρ (t + κ z ^ e) * u z) z₀ ↔
      (k : WithTop ℤ) ≤ meromorphicOrderAt ρ t := by
  rw [(caf_order_comp_mul ρ t z₀ κ u hκ hκ0 hκ' e he hρ hu n).2, huo]
  cases h : meromorphicOrderAt ρ t with
  | top =>
    have he' : ((e : ℕ) : WithTop ℤ) ≠ 0 := by exact_mod_cast he.ne'
    rw [WithTop.top_mul he', WithTop.add_top, WithTop.top_add]
    simp
  | coe o =>
    have : ((n : WithTop ℤ) + (o : WithTop ℤ) * ((e : ℤ) : WithTop ℤ) + (c : WithTop ℤ)) =
        ((n + o * e + c : ℤ) : WithTop ℤ) := by push_cast; rfl
    rw [show ((e : ℕ) : WithTop ℤ) = ((e : ℤ) : WithTop ℤ) from rfl, this]
    rw [WithTop.coe_nonneg, WithTop.coe_le_coe]
    exact hk o


/-- An analytic germ vanishing at the point has order at least one. -/
theorem caf_one_le_order_of_zero (f : ℂ → ℂ) (z₀ : ℂ) (hf : AnalyticAt ℂ f z₀) (h0 : f z₀ = 0) :
    1 ≤ meromorphicOrderAt f z₀ := by
  rw [hf.meromorphicOrderAt_eq]
  have h := analyticOrderAt_ne_zero.mpr ⟨hf, h0⟩
  cases ho : analyticOrderAt f z₀ with
  | top => simp
  | coe n =>
    rw [ho] at h
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h)
    simp only [ENat.map_natCast, WithTop.coe_natCast]
    exact_mod_cast hn

/-- An analytic germ has nonnegative order, zero if it does not vanish at the point. -/
theorem caf_order_analytic_nonneg (f : ℂ → ℂ) (z₀ : ℂ) (hf : AnalyticAt ℂ f z₀) :
    0 ≤ meromorphicOrderAt f z₀ := hf.meromorphicOrderAt_nonneg

/-- Lower bounds for finite sums. -/
theorem caf_order_sum_ge {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) (z₀ : ℂ)
    (hf : ∀ i ∈ S, MeromorphicAt (f i) z₀) (n : WithTop ℤ)
    (h : ∀ i ∈ S, n ≤ meromorphicOrderAt (f i) z₀) :
    MeromorphicAt (fun z ↦ ∑ i ∈ S, f i z) z₀ ∧
      n ≤ meromorphicOrderAt (fun z ↦ ∑ i ∈ S, f i z) z₀ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simp [MeromorphicAt.const (0 : ℂ) z₀], ?_⟩
    simp [meromorphicOrderAt_const]
  | insert a S ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
    have hfa := hf a (Finset.mem_insert_self a S)
    have heq : (fun z ↦ ∑ i ∈ insert a S, f i z) = f a + fun z ↦ ∑ i ∈ S, f i z := by
      funext z; simp [Finset.sum_insert ha]
    rw [heq]
    refine ⟨hfa.add h1, le_trans ?_ (meromorphicOrderAt_add hfa h1)⟩
    exact le_min (h a (Finset.mem_insert_self a S)) h2

/-- Components of `A F` are meromorphic. -/
theorem caf_meromorphic_mulVec (A : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (F : ℂ → Fin 4 → ℂ) (z₀ : ℂ)
    (hA : ∀ i j, MeromorphicAt (fun z ↦ A z i j) z₀)
    (hF : ∀ j, MeromorphicAt (fun z ↦ F z j) z₀) (i : Fin 4) :
    MeromorphicAt (fun z ↦ (A z *ᵥ F z) i) z₀ := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  exact ((((hA i 0).mul (hF 0)).add ((hA i 1).mul (hF 1))).add ((hA i 2).mul (hF 2))).add
    ((hA i 3).mul (hF 3))

/-- **Lower bounds for the components of `A F`.** -/
theorem caf_order_mulVec_ge (A : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (F : ℂ → Fin 4 → ℂ) (z₀ : ℂ)
    (hA : ∀ i j, MeromorphicAt (fun z ↦ A z i j) z₀)
    (hF : ∀ j, MeromorphicAt (fun z ↦ F z j) z₀) (n : Fin 4 → WithTop ℤ)
    (h : ∀ i j, n i ≤ meromorphicOrderAt (fun z ↦ A z i j) z₀ +
      meromorphicOrderAt (fun z ↦ F z j) z₀) (i : Fin 4) :
    MeromorphicAt (fun z ↦ (A z *ᵥ F z) i) z₀ ∧
      n i ≤ meromorphicOrderAt (fun z ↦ (A z *ᵥ F z) i) z₀ := by
  have heq : (fun z ↦ (A z *ᵥ F z) i) = fun z ↦ ∑ j ∈ Finset.univ,
      ((fun z ↦ A z i j) * fun z ↦ F z j) z := by
    funext z; simp [Matrix.mulVec, dotProduct]
  rw [heq]
  refine caf_order_sum_ge _ _ z₀ (fun j _ ↦ (hA i j).mul (hF j)) (n i) fun j _ ↦ ?_
  rw [meromorphicOrderAt_mul (hA i j) (hF j)]
  exact h i j

/-- Matrices with analytic entries and invertible value: entries of the inverse are analytic. -/
theorem caf_inv_entries_analyticAt (A : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (z₀ : ℂ)
    (hA : ∀ i j, AnalyticAt ℂ (fun z ↦ A z i j) z₀) (hdet : (A z₀).det ≠ 0) :
    (∀ i j, AnalyticAt ℂ (fun z ↦ (A z)⁻¹ i j) z₀) ∧ ∀ᶠ z in 𝓝 z₀, (A z).det ≠ 0 := by
  have h1 : ∀ᶠ z in 𝓝 z₀, ∀ i j, AnalyticAt ℂ (fun z ↦ A z i j) z := by
    simp only [Filter.eventually_all]
    exact fun i j ↦ (hA i j).eventually_analyticAt
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.mp h1
  have hd := b65g_det_analytic (U := ball z₀ r₁) (A := A) fun i j z hz ↦ hb₁ z hz i j
  have hev : ∀ᶠ z in 𝓝 z₀, (∀ i j, AnalyticAt ℂ (fun z ↦ A z i j) z) ∧ (A z).det ≠ 0 :=
    h1.and ((hd z₀ (mem_ball_self hr₁)).continuousAt.eventually_ne hdet)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hinv := b65g_inv_analytic (U := ball z₀ r) (A := A) (fun i j z hz ↦ (hball z hz).1 i j)
    (fun z hz ↦ (hball z hz).2)
  exact ⟨fun i j ↦ hinv i j z₀ (mem_ball_self hr), hev.mono fun z hz ↦ hz.2⟩

/-- **Orders of components under an invertible analytic matrix.** -/
theorem caf_order_matrix_iff (A : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (F : ℂ → Fin 4 → ℂ) (z₀ : ℂ)
    (hA : ∀ i j, AnalyticAt ℂ (fun z ↦ A z i j) z₀) (hdet : (A z₀).det ≠ 0)
    (hF : ∀ j, MeromorphicAt (fun z ↦ F z j) z₀) (n : WithTop ℤ) :
    (∀ i, n ≤ meromorphicOrderAt (fun z ↦ (A z *ᵥ F z) i) z₀) ↔
      ∀ i, n ≤ meromorphicOrderAt (fun z ↦ F z i) z₀ := by
  have key : ∀ (A : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (F : ℂ → Fin 4 → ℂ),
      (∀ i j, AnalyticAt ℂ (fun z ↦ A z i j) z₀) → (∀ j, MeromorphicAt (fun z ↦ F z j) z₀) →
      (∀ i, n ≤ meromorphicOrderAt (fun z ↦ F z i) z₀) →
      ∀ i, n ≤ meromorphicOrderAt (fun z ↦ (A z *ᵥ F z) i) z₀ := by
    intro A F hA hF h i
    refine (caf_order_mulVec_ge A F z₀ (fun i j ↦ (hA i j).meromorphicAt) hF (fun _ ↦ n)
      (fun i j ↦ ?_) i).2
    calc n = 0 + n := (zero_add n).symm
      _ ≤ _ := add_le_add (hA i j).meromorphicOrderAt_nonneg (h j)
  constructor
  · intro h i
    obtain ⟨hB, hev⟩ := caf_inv_entries_analyticAt A z₀ hA hdet
    have hAF : ∀ j, MeromorphicAt (fun z ↦ (A z *ᵥ F z) j) z₀ := fun j ↦
      caf_meromorphic_mulVec A F z₀ (fun i j ↦ (hA i j).meromorphicAt) hF j
    have := key (fun z ↦ (A z)⁻¹) (fun z ↦ A z *ᵥ F z) hB hAF h i
    rwa [meromorphicOrderAt_congr (f₂ := fun z ↦ F z i)] at this
    filter_upwards [nhdsWithin_le_nhds hev] with z hz
    simp only [Matrix.mulVec_mulVec]
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hz), Matrix.one_mulVec]
  · exact key A F hA hF

/-- **Unipotent analytic matrices respect a pattern of bounds** differing by at most one. -/
theorem caf_order_unipotent (N : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (u : ℂ → Fin 4 → ℂ) (z₀ : ℂ)
    (hN : ∀ i j, AnalyticAt ℂ (fun z ↦ N z i j) z₀) (hN1 : N z₀ = 1)
    (hu : ∀ j, MeromorphicAt (fun z ↦ u z j) z₀) (n : Fin 4 → ℤ)
    (hn : ∀ i j, i ≠ j → n i ≤ n j + 1)
    (h : ∀ j, (n j : WithTop ℤ) ≤ meromorphicOrderAt (fun z ↦ u z j) z₀) (i : Fin 4) :
    (n i : WithTop ℤ) ≤ meromorphicOrderAt (fun z ↦ (N z *ᵥ u z) i) z₀ := by
  refine (caf_order_mulVec_ge N u z₀ (fun i j ↦ (hN i j).meromorphicAt) hu (fun i ↦ (n i : _))
    (fun i j ↦ ?_) i).2
  by_cases hij : i = j
  · subst hij
    have h0 : N z₀ i i ≠ 0 := by rw [hN1]; simp
    have : meromorphicOrderAt (fun z ↦ N z i i) z₀ = 0 := by
      rw [(hN i i).meromorphicOrderAt_eq, (hN i i).analyticOrderAt_eq_zero.mpr h0]
      rfl
    rw [this, zero_add]
    exact h i
  · have h0 : N z₀ i j = 0 := by rw [hN1]; simp [hij]
    have h1 := caf_one_le_order_of_zero _ z₀ (hN i j) h0
    calc ((n i : ℤ) : WithTop ℤ) ≤ ((1 + n j : ℤ) : WithTop ℤ) := by
          exact_mod_cast (by linarith [hn i j hij] : n i ≤ 1 + n j)
      _ = 1 + ((n j : ℤ) : WithTop ℤ) := by push_cast; rfl
      _ ≤ _ := add_le_add h1 (h j)

/-- **Bounded vector germs.** For an invertible matrix `K`, the germs `v ⬝ K F` are bounded
on a punctured neighbourhood for every `v` exactly when every component of `F` has nonnegative
order. -/
theorem caf_bdd_vec_iff (K : Matrix (Fin 4) (Fin 4) ℂ) (hK : IsUnit K.det) (F : ℂ → Fin 4 → ℂ)
    (z₀ : ℂ) (hF : ∀ i, MeromorphicAt (fun z ↦ F z i) z₀) :
    (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀, ‖v ⬝ᵥ (K *ᵥ F z)‖ ≤ B) ↔
      ∀ i, 0 ≤ meromorphicOrderAt (fun z ↦ F z i) z₀ := by
  constructor
  · intro h i
    rw [← caf_bdd_iff_order_nonneg _ z₀ (hF i)]
    obtain ⟨B, hB⟩ := h (Pi.single i 1 ᵥ* K⁻¹)
    refine ⟨B, hB.mono fun z hz ↦ ?_⟩
    rwa [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hK,
      Matrix.vecMul_one, single_dotProduct, one_mul] at hz
  · intro h v
    have hb : ∀ i, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀, ‖F z i‖ ≤ B := fun i ↦
      (caf_bdd_iff_order_nonneg _ z₀ (hF i)).mpr (h i)
    choose B hB using hb
    refine ⟨∑ i, ‖(v ᵥ* K) i‖ * B i, ?_⟩
    filter_upwards [Filter.eventually_all.mpr hB] with z hz
    rw [Matrix.dotProduct_mulVec]
    calc ‖(v ᵥ* K) ⬝ᵥ F z‖ = ‖∑ i, (v ᵥ* K) i * F z i‖ := rfl
      _ ≤ ∑ i, ‖(v ᵥ* K) i * F z i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖(v ᵥ* K) i‖ * B i := by
          gcongr with i
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _)

/-! ## Rational functions -/

/-- Evaluation of a rational function is meromorphic at every point. -/
theorem caf_eval_meromorphicAt (r : RatFunc ℂ) (s : ℂ) : MeromorphicAt (b65q_eval r) s := by
  have : b65q_eval r = fun z ↦ r.num.eval z / r.denom.eval z := funext (b65q_eval_eq r)
  rw [this]
  exact ((AnalyticOnNhd.eval_polynomial r.num s (mem_univ _)).meromorphicAt).div
    ((AnalyticOnNhd.eval_polynomial r.denom s (mem_univ _)).meromorphicAt)

/-- Evaluation of a rational function is analytic where its denominator does not vanish. -/
theorem caf_eval_analyticAt (r : RatFunc ℂ) (s : ℂ) (hs : r.denom.eval s ≠ 0) :
    AnalyticAt ℂ (b65q_eval r) s := by
  have : b65q_eval r = fun z ↦ r.num.eval z / r.denom.eval z := funext (b65q_eval_eq r)
  rw [this]
  exact (AnalyticOnNhd.eval_polynomial r.num s (mem_univ _)).div
    (AnalyticOnNhd.eval_polynomial r.denom s (mem_univ _)) hs

/-- **The order of a rational function** at a point is nonnegative exactly where its denominator
does not vanish. -/
theorem caf_order_ratFunc_nonneg_iff (r : RatFunc ℂ) (s : ℂ) :
    0 ≤ meromorphicOrderAt (b65q_eval r) s ↔ r.denom.eval s ≠ 0 := by
  refine ⟨fun h hd ↦ ?_, fun h ↦ (caf_eval_analyticAt r s h).meromorphicOrderAt_nonneg⟩
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg (caf_eval_meromorphicAt r s) h
  have hn : r.num.eval s ≠ 0 := by
    intro hn
    obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom r
    have := congrArg (Polynomial.eval s) hab
    simp [Polynomial.eval_add, Polynomial.eval_mul, hn, hd] at this
  have hfin : ({z | r.denom.eval z = 0} \ {s} : Set ℂ).Finite := by
    refine (Polynomial.rootSet_finite r.denom ℂ).subset ?_
    intro z hz
    rw [Polynomial.mem_rootSet]
    exact ⟨r.denom_ne_zero, by simpa using hz.1⟩
  have hev : ∀ᶠ z in 𝓝[≠] s, r.denom.eval z ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (hfin.isClosed.isOpen_compl.mem_nhds
      (by simp : s ∈ ({z | r.denom.eval z = 0} \ {s} : Set ℂ)ᶜ)), self_mem_nhdsWithin]
      with z hz hzs
    intro h0
    exact hz ⟨h0, hzs⟩
  have hlim : Tendsto (fun z ↦ b65q_eval r z * r.denom.eval z) (𝓝[≠] s) (𝓝 (c * 0)) := by
    refine hc.mul ?_
    rw [← hd]
    exact ((Polynomial.continuous r.denom).tendsto s).mono_left nhdsWithin_le_nhds
  have hlim' : Tendsto (fun z ↦ r.num.eval z) (𝓝[≠] s) (𝓝 (c * 0)) := by
    refine hlim.congr' ?_
    filter_upwards [hev] with z hz
    rw [b65q_eval_eq, div_mul_cancel₀ _ hz]
  have hlim'' : Tendsto (fun z ↦ r.num.eval z) (𝓝[≠] s) (𝓝 (r.num.eval s)) :=
    ((Polynomial.continuous r.num).tendsto s).mono_left nhdsWithin_le_nhds
  rw [mul_zero] at hlim'
  exact hn (tendsto_nhds_unique hlim'' hlim')

/-- **The order at infinity of a rational function**: `ord₀ r(1/w) ≥ 2` exactly when `r = 0`
or `intDegree r ≤ −2`. -/
theorem caf_order_ratFunc_inv (r : RatFunc ℂ) :
    MeromorphicAt (fun w ↦ b65q_eval r w⁻¹) 0 ∧
      ((2 ≤ meromorphicOrderAt (fun w ↦ b65q_eval r w⁻¹) 0) ↔ r = 0 ∨ r.intDegree ≤ -2) := by
  by_cases hr : r = 0
  · subst hr
    have h0 : (fun w : ℂ ↦ b65q_eval 0 w⁻¹) = fun _ ↦ 0 := by funext w; simp [b65q_eval]
    rw [h0]
    exact ⟨MeromorphicAt.const 0 0, by simp [meromorphicOrderAt_const]⟩
  · obtain ⟨h1, h2⟩ := caf_meromorphicOrderAt_inv r hr
    refine ⟨h1, ?_⟩
    change 2 ≤ meromorphicOrderAt (fun w : ℂ ↦ r.eval (RingHom.id ℂ) w⁻¹) 0 ↔ _
    rw [h2, show (2 : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
    simp only [hr, false_or]
    omega

end HodgeLean.Foundations.Program

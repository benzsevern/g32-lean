import HodgeLean.Foundations.Program.GriffithsTransversalityVariation

/-! Surjectivity of the comparison on liftable classes. For a holomorphic form `ω` on the
fibre, the Mittag-Leffler data of `conj ω` give smooth chart functions `τ_a` with
`∂τ_a/∂w̄ = conj ω_a`; their coboundary is a holomorphic scalar cocycle lifted by the
Wirtinger derivatives `∂τ_a/∂w`, and its chain periods are `−conj ∫ ω`.
HC no distance; AV milestone no distance. -/
noncomputable section
open Set Filter Topology Manifold ComplexConjugate
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

section B66gWirtinger

/-- The holomorphic Wirtinger derivative `∂f/∂w`.
Source: Hörmander, *An Introduction to Complex Analysis in Several Variables*, §1.1. -/
def b66g_wd (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  (fderiv ℝ f w 1 - Complex.I * fderiv ℝ f w Complex.I) / 2

/-- The antiholomorphic Wirtinger derivative `∂f/∂w̄`.
Source: Hörmander, §1.1. -/
def b66g_wdb (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  (fderiv ℝ f w 1 + Complex.I * fderiv ℝ f w Complex.I) / 2

theorem b66g_clmR_decomp (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    L v = (L 1 - Complex.I * L Complex.I) / 2 * v +
      (L 1 + Complex.I * L Complex.I) / 2 * conj v := by
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, v = (x : ℂ) + (y : ℂ) * Complex.I :=
    ⟨v.re, v.im, (Complex.re_add_im v).symm⟩
  have h1 : L ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) * L 1 + (y : ℂ) * L Complex.I := by
    have : ((x : ℂ) + (y : ℂ) * Complex.I) = x • (1 : ℂ) + y • Complex.I := by
      simp [Complex.real_smul]
    rw [this, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have h2 : conj ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) - (y : ℂ) * Complex.I := by
    simp [Complex.conj_ofReal]
    ring
  rw [h1, h2]
  linear_combination ((y : ℂ) * L Complex.I) * Complex.I_sq

theorem b66g_fderiv_decomp (f : ℂ → ℂ) (w v : ℂ) :
    fderiv ℝ f w v = b66g_wd f w * v + b66g_wdb f w * conj v :=
  b66g_clmR_decomp _ v

theorem b66g_wd_of_hasDerivAt {f : ℂ → ℂ} {f' w : ℂ} (h : HasDerivAt f f' w) :
    b66g_wd f w = f' ∧ b66g_wdb f w = 0 := by
  have hR := h.hasFDerivAt.restrictScalars ℝ
  have e : ∀ v, fderiv ℝ f w v = f' * v := fun v => by
    rw [hR.fderiv]
    simp [mul_comm]
  unfold b66g_wd b66g_wdb
  rw [e, e]
  constructor
  · linear_combination (-f' / 2) * Complex.I_sq
  · linear_combination (f' / 2) * Complex.I_sq

theorem b66g_hasDerivAt_of_wdb {f : ℂ → ℂ} {w : ℂ} (hd : DifferentiableAt ℝ f w)
    (h0 : b66g_wdb f w = 0) : HasDerivAt f (b66g_wd f w) w := by
  have H : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b66g_wd f w)).restrictScalars ℝ) =
      fderiv ℝ f w := by
    ext1 v
    rw [b66g_fderiv_decomp f w v, h0]
    simp [mul_comm]
  have := (hasFDerivAt_of_restrictScalars ℝ hd.hasFDerivAt H).hasDerivAt
  simpa using this

theorem b66g_wd_conj {h : ℂ → ℂ} {h' w : ℂ} (hh : HasDerivAt h h' w) :
    DifferentiableAt ℝ (fun z => conj (h z)) w ∧
      b66g_wd (fun z => conj (h z)) w = 0 ∧ b66g_wdb (fun z => conj (h z)) w = conj h' := by
  have hc := ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.hasFDerivAt).comp w
    (hh.hasFDerivAt.restrictScalars ℝ)
  have e : ∀ v, fderiv ℝ (fun z => conj (h z)) w v = conj h' * conj v := fun v => by
    rw [show (fun z => conj (h z)) = (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap ∘ h
      from rfl, hc.fderiv]
    simp [mul_comm]
  refine ⟨hc.differentiableAt, ?_, ?_⟩
  · unfold b66g_wd
    rw [e, e]
    simp only [Complex.conj_I, map_one]
    linear_combination (conj h' / 2) * Complex.I_sq
  · unfold b66g_wdb
    rw [e, e]
    simp only [Complex.conj_I, map_one]
    linear_combination (-conj h' / 2) * Complex.I_sq

theorem b66g_wd_sub {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w)
    (hg : DifferentiableAt ℝ g w) :
    b66g_wd (fun z => f z - g z) w = b66g_wd f w - b66g_wd g w ∧
      b66g_wdb (fun z => f z - g z) w = b66g_wdb f w - b66g_wdb g w := by
  have e : fderiv ℝ (fun z => f z - g z) w = fderiv ℝ f w - fderiv ℝ g w := fderiv_sub hf hg
  unfold b66g_wd b66g_wdb
  rw [e]
  simp only [sub_apply]
  constructor <;> ring

theorem b66g_wd_add {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w)
    (hg : DifferentiableAt ℝ g w) :
    b66g_wd (fun z => f z + g z) w = b66g_wd f w + b66g_wd g w ∧
      b66g_wdb (fun z => f z + g z) w = b66g_wdb f w + b66g_wdb g w := by
  have e : fderiv ℝ (fun z => f z + g z) w = fderiv ℝ f w + fderiv ℝ g w := fderiv_add hf hg
  unfold b66g_wd b66g_wdb
  rw [e]
  simp only [add_apply]
  constructor <;> ring

theorem b66g_wd_comp {f h : ℂ → ℂ} {h' w : ℂ} (hf : DifferentiableAt ℝ f (h w))
    (hh : HasDerivAt h h' w) :
    DifferentiableAt ℝ (f ∘ h) w ∧ b66g_wd (f ∘ h) w = b66g_wd f (h w) * h' ∧
      b66g_wdb (f ∘ h) w = b66g_wdb f (h w) * conj h' := by
  have hhR := hh.hasFDerivAt.restrictScalars ℝ
  have hc := hf.hasFDerivAt.comp w hhR
  have e : ∀ v, fderiv ℝ (f ∘ h) w v = fderiv ℝ f (h w) (h' * v) := fun v => by
    rw [hc.fderiv]
    simp [mul_comm]
  refine ⟨hc.differentiableAt, ?_, ?_⟩
  · show (fderiv ℝ (f ∘ h) w 1 - Complex.I * fderiv ℝ (f ∘ h) w Complex.I) / 2 = _
    rw [e, e, b66g_fderiv_decomp f (h w) (h' * 1), b66g_fderiv_decomp f (h w) (h' * Complex.I)]
    simp only [map_mul, Complex.conj_I, mul_one]
    linear_combination ((b66g_wdb f (h w) * conj h' - b66g_wd f (h w) * h') / 2) * Complex.I_sq
  · show (fderiv ℝ (f ∘ h) w 1 + Complex.I * fderiv ℝ (f ∘ h) w Complex.I) / 2 = _
    rw [e, e, b66g_fderiv_decomp f (h w) (h' * 1), b66g_fderiv_decomp f (h w) (h' * Complex.I)]
    simp only [map_mul, Complex.conj_I, mul_one]
    linear_combination ((b66g_wd f (h w) * h' - b66g_wdb f (h w) * conj h') / 2) * Complex.I_sq

end B66gWirtinger

section B66gChartDbar

variable (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)

/-- The tangent vector of the inverse retained coordinate. -/
def b66g_mu (a : b66k_Index R) (w : ℂ) : TangentSpace 𝓘(ℂ, ℂ) (b66g_inv R t a w) :=
  mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66g_inv R t a) w (1 : ℂ)

theorem b66g_sliceD_mu {a : b66k_Index R} {w : ℂ} (hw : w ∈ b66k_domain R t a) :
    b66g_sliceD R t a (b66g_inv R t a w) (b66g_mu R t a w) = 1 := by
  have hinv : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66g_inv R t a) w :=
    (b66g_inv_contMDiffAt R t a hw).mdifferentiableAt (by simp)
  have hsl : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66g_slice R t a) (b66g_inv R t a w) :=
    (b66g_slice_contMDiffAt R t a _ (b66g_inv_mem R t a hw)).mdifferentiableAt (by simp)
  have hev : b66g_slice R t a ∘ b66g_inv R t a =ᶠ[𝓝 w] id := by
    filter_upwards [(b66g_domain_open R t a).mem_nhds hw] with z hz
    exact b66g_slice_inv R t a hz
  have h := mfderiv_comp w hsl hinv
  rw [hev.mfderiv_eq, mfderiv_id] at h
  exact (DFunLike.congr_fun h (1 : ℂ)).symm

/-- The antiholomorphic derivative of a chart expression is the fibre `∂̄`, evaluated on the
coordinate tangent vector. -/
theorem b66g_chart_dbar {u : rf8_fibre R.C t → ℂ} {a : b66k_Index R} {w : ℂ}
    (hw : w ∈ b66k_domain R t a)
    (hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) u (b66g_inv R t a w)) :
    DifferentiableAt ℝ (u ∘ b66g_inv R t a) w ∧
      b66g_wdb (u ∘ b66g_inv R t a) w =
        b4c_dbar ℂ (rf8_fibre R.C t) u ⟨b66g_inv R t a w, b66g_mu R t a w⟩ := by
  have hinvC : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66g_inv R t a) w :=
    (b66g_inv_contMDiffAt R t a hw).mdifferentiableAt (by simp)
  obtain ⟨hinvR, hinvEq⟩ := b3A_mdifferentiableAt_real hinvC
  have hcomp := hu.comp w hinvR
  have hd : DifferentiableAt ℝ (u ∘ b66g_inv R t a) w :=
    mdifferentiableAt_iff_differentiableAt.mp hcomp
  refine ⟨hd, ?_⟩
  have e : ∀ v : ℂ, fderiv ℝ (u ∘ b66g_inv R t a) w v =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) u (b66g_inv R t a w) (v • b66g_mu R t a w) := by
    intro v
    have h1 : fderiv ℝ (u ∘ b66g_inv R t a) w =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (u ∘ b66g_inv R t a) w := mfderiv_eq_fderiv.symm
    rw [h1, mfderiv_comp w hu hinvR]
    change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) u (b66g_inv R t a w)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66g_inv R t a) w v) = _
    have e2 : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66g_inv R t a) w v =
        v • mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66g_inv R t a) w (1 : ℂ) :=
      (hinvEq v).trans (b66g_clm_apply _ v)
    rw [e2]
    rfl
  unfold b66g_wdb b4c_dbar
  rw [e, e, one_smul]
  rfl

end B66gChartDbar

section B66gMLData

variable {R : rf8_SharedFamily} {t : b6t_polydisc mr_base}

/-- Mittag-Leffler data for the conjugate of a holomorphic form.
Source: Forster, *Lectures on Riemann Surfaces*, §§15–16; `b66g_mittagLeffler`. -/
structure b66g_ML (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (φ : b3_HolForm ℂ (rf8_fibre R.C t)) where
  y₀ : rf8_fibre R.C t
  F : rf8_fibre R.C t → ℂ
  P : rf8_fibre R.C t → ℂ
  N : ℕ
  c : Fin N → ℂ
  hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F
  hP : ∀ y, y ≠ y₀ → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ P y
  hFP : ∀ y, y ≠ y₀ → ∀ v : ℂ,
    b4c_dbar ℂ (rf8_fibre R.C t) (F + P) ⟨y, v⟩ = star (φ.1 ⟨y, v⟩)
  hFnear : ∀ᶠ y in 𝓝 y₀, ∀ v : ℂ,
    b4c_dbar ℂ (rf8_fibre R.C t) F ⟨y, v⟩ = star (φ.1 ⟨y, v⟩)
  hPg : P =ᶠ[𝓝 y₀] fun y => ∑ n, c n /
    RiemannRochAna_coordinate (Module.finrank_self ℂ) y₀ y ^ ((n : ℕ) + 1)

theorem b66g_ML_exists (φ : b3_HolForm ℂ (rf8_fibre R.C t)) : Nonempty (b66g_ML R t φ) := by
  obtain ⟨y₀⟩ : Nonempty (rf8_fibre R.C t) := inferInstance
  obtain ⟨F, P, N, c, hF, hP, hFP, hFnear, hPg⟩ :=
    b66g_mittagLeffler (fun p => star (φ.1 p)) (RiemannRochAna_conj_hol_mem φ) y₀
  exact ⟨⟨y₀, F, P, N, c, hF, hP, hFP, hFnear, hPg⟩⟩

variable {φ : b3_HolForm ℂ (rf8_fibre R.C t)} (M : b66g_ML R t φ)

/-- The polar part in a retained chart through the centre is meromorphic at the centre. -/
theorem b66g_ML_mero (a : b66k_Index R) (ha : M.y₀.val ∈ (R.atlas.A a).source) :
    MeromorphicAt (fun w => M.P (b66g_inv R t a w)) (b66g_slice R t a M.y₀) := by
  set w₀ := b66g_slice R t a M.y₀
  have hw₀ : w₀ ∈ b66k_domain R t a := b66g_slice_domain R t a M.y₀ ha
  have hy : b66g_inv R t a w₀ = M.y₀ := b66g_inv_slice_eq R t a M.y₀ ha
  have hk := RiemannRochAna_coordinate_analytic (Module.finrank_self ℂ) M.y₀ M.y₀
    (mem_extChartAt_source M.y₀)
  have hA2 : AnalyticAt ℂ (fun w => RiemannRochAna_coordinate (Module.finrank_self ℂ) M.y₀
      (b66g_inv R t a w)) w₀ :=
    b66g_coord_analytic R t _ a w₀ hw₀ (by
      change ContMDiffAt _ _ _ _ (b66g_inv R t a w₀)
      rw [hy]; exact hk)
  have hM : MeromorphicAt (fun w => ∑ n, M.c n / RiemannRochAna_coordinate
      (Module.finrank_self ℂ) M.y₀ (b66g_inv R t a w) ^ ((n : ℕ) + 1)) w₀ :=
    MeromorphicAt.fun_sum (s := Finset.univ)
      fun n _ => (MeromorphicAt.const (M.c n) w₀).div (hA2.meromorphicAt.pow ((n : ℕ) + 1))
  apply hM.congr
  have htend := (b66g_pt_continuous R t a w₀ hw₀).tendsto
  change Tendsto (b66g_inv R t a) (𝓝 w₀) (𝓝 (b66g_inv R t a w₀)) at htend
  rw [hy] at htend
  filter_upwards [nhdsWithin_le_nhds (htend.eventually M.hPg)] with w hw
  exact hw.symm

theorem b66g_ML_pp (a : b66k_Index R) (ha : M.y₀.val ∈ (R.atlas.A a).source) :
    ∃ (K : ℕ) (d : Fin K → ℂ) (ρ : ℂ → ℂ), AnalyticAt ℂ ρ (b66g_slice R t a M.y₀) ∧
      ∀ᶠ w in 𝓝[≠] (b66g_slice R t a M.y₀), M.P (b66g_inv R t a w) =
        ρ w + ∑ k : Fin K, d k / (w - b66g_slice R t a M.y₀) ^ (k.val + 1) :=
  b66g_principal_part (b66g_ML_mero M a ha)

/-- The holomorphic correction of the polar part in a retained chart. -/
def b66g_ML.g (a : b66k_Index R) : ℂ → ℂ :=
  if ha : M.y₀.val ∈ (R.atlas.A a).source then
    fun w => -∑ k : Fin (b66g_ML_pp M a ha).choose,
      (b66g_ML_pp M a ha).choose_spec.choose k / (w - b66g_slice R t a M.y₀) ^ (k.val + 1)
  else 0

/-- The regular part of the polar part at the centre. -/
def b66g_ML.ρ (a : b66k_Index R) : ℂ → ℂ :=
  if ha : M.y₀.val ∈ (R.atlas.A a).source then
    (b66g_ML_pp M a ha).choose_spec.choose_spec.choose
  else 0

/-- The chart polar part, with its removable value at the centre. -/
def b66g_ML.Q (a : b66k_Index R) (w : ℂ) : ℂ :=
  if M.y₀.val ∈ (R.atlas.A a).source ∧ w = b66g_slice R t a M.y₀ then M.ρ a w
  else M.P (b66g_inv R t a w) + M.g a w

/-- The smooth chart splitting with `∂τ_a/∂w̄ = conj φ_a`. -/
def b66g_ML.τ (a : b66k_Index R) (w : ℂ) : ℂ := M.F (b66g_inv R t a w) + M.Q a w

theorem b66g_ML.g_analytic (a : b66k_Index R) {w : ℂ}
    (hw : M.y₀.val ∈ (R.atlas.A a).source → w ≠ b66g_slice R t a M.y₀) :
    AnalyticAt ℂ (M.g a) w := by
  unfold b66g_ML.g
  split_ifs with ha
  · exact (b66g_polar_analytic _ _ w (hw ha)).neg
  · exact analyticAt_const

theorem b66g_ML.ρ_spec (a : b66k_Index R) (ha : M.y₀.val ∈ (R.atlas.A a).source) :
    AnalyticAt ℂ (M.ρ a) (b66g_slice R t a M.y₀) ∧
      ∀ᶠ w in 𝓝[≠] (b66g_slice R t a M.y₀), M.P (b66g_inv R t a w) + M.g a w = M.ρ a w := by
  obtain ⟨h1, h2⟩ := (b66g_ML_pp M a ha).choose_spec.choose_spec.choose_spec
  refine ⟨by simp only [b66g_ML.ρ, ha, dite_true]; exact h1, ?_⟩
  filter_upwards [h2] with w hw
  simp only [b66g_ML.g, b66g_ML.ρ, ha, dite_true, hw]
  ring

theorem b66g_ML.Q_eq_rho (a : b66k_Index R) (ha : M.y₀.val ∈ (R.atlas.A a).source) :
    M.Q a =ᶠ[𝓝 (b66g_slice R t a M.y₀)] M.ρ a := by
  have h := (b66g_ML.ρ_spec M a ha).2
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h] with w hw
  by_cases hw' : w = b66g_slice R t a M.y₀
  · simp only [b66g_ML.Q, ha, hw', and_self, ite_true]
  · simp only [b66g_ML.Q, ha, hw', and_false, ite_false]
    exact hw hw'

theorem b66g_ML.Q_eq_off (a : b66k_Index R) {w : ℂ}
    (hw : M.y₀.val ∈ (R.atlas.A a).source → w ≠ b66g_slice R t a M.y₀) :
    M.Q a =ᶠ[𝓝 w] fun z => M.P (b66g_inv R t a z) + M.g a z := by
  by_cases ha : M.y₀.val ∈ (R.atlas.A a).source
  · filter_upwards [isOpen_compl_singleton.mem_nhds (hw ha)] with z hz
    simp only [b66g_ML.Q, ha, true_and]
    have hz' : z ≠ b66g_slice R t a M.y₀ := hz
    simp only [hz', ite_false]
  · filter_upwards with z
    simp only [b66g_ML.Q, ha, false_and, ite_false]

/-- The chart coefficient of the form. -/
abbrev b66g_ML.ωa (_M : b66g_ML R t φ) (a : b66k_Index R) : ℂ → ℂ :=
  b66g_coef R t (b66g_ofForm R t φ.1) a

theorem b66g_form_mu (φ : b3_HolForm ℂ (rf8_fibre R.C t)) {a : b66k_Index R} {w : ℂ}
    (hw : w ∈ b66k_domain R t a) :
    φ.1 ⟨b66g_inv R t a w, b66g_mu R t a w⟩ = b66g_coef R t (b66g_ofForm R t φ.1) a w := by
  have h1 := b66g_toForm_apply R t (b66g_ofForm_mem R t φ.2) a (b66g_inv R t a w)
    (b66g_inv_mem R t a hw) (b66g_mu R t a w)
  rw [b66g_toForm_ofForm R t φ.2.2] at h1
  rw [h1, b66g_sliceD_mu R t hw, mul_one]
  rfl

theorem b66g_ML.τ_spec (a : b66k_Index R) {w : ℂ} (hw : w ∈ b66k_domain R t a) :
    DifferentiableAt ℝ (M.τ a) w ∧ b66g_wdb (M.τ a) w = conj (M.ωa a w) := by
  set y := b66g_inv R t a w
  have hφμ := b66g_form_mu φ hw
  by_cases hy : y = M.y₀
  · have ha : M.y₀.val ∈ (R.atlas.A a).source := hy ▸ b66g_inv_mem R t a hw
    have hw0 : w = b66g_slice R t a M.y₀ := by
      rw [← hy]; exact (b66g_slice_inv R t a hw).symm
    have hev : M.τ a =ᶠ[𝓝 w] fun z => M.F (b66g_inv R t a z) + M.ρ a z := by
      have := b66g_ML.Q_eq_rho M a ha
      rw [← hw0] at this
      filter_upwards [this] with z hz
      simp only [b66g_ML.τ, hz]
    have hFd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) M.F y := (M.hF y).mdifferentiableAt (by simp)
    obtain ⟨hd1, hdb1⟩ := b66g_chart_dbar R t hw hFd
    have hρ : AnalyticAt ℂ (M.ρ a) w := by rw [hw0]; exact (b66g_ML.ρ_spec M a ha).1
    have hρd := hρ.differentiableAt.hasDerivAt
    obtain ⟨-, hρb⟩ := b66g_wd_of_hasDerivAt hρd
    have hsum := b66g_wd_add (f := M.F ∘ b66g_inv R t a) hd1
      (hρ.differentiableAt.restrictScalars ℝ)
    have hdiff : DifferentiableAt ℝ (fun z => M.F (b66g_inv R t a z) + M.ρ a z) w :=
      hd1.add (hρ.differentiableAt.restrictScalars ℝ)
    refine ⟨hdiff.congr_of_eventuallyEq hev, ?_⟩
    have hwdb : b66g_wdb (M.τ a) w = b66g_wdb (fun z => M.F (b66g_inv R t a z) + M.ρ a z) w := by
      unfold b66g_wdb; rw [hev.fderiv_eq]
    rw [hwdb]
    have := hsum.2
    simp only [Function.comp_apply] at this
    rw [this, hdb1, hρb, add_zero]
    have hn := M.hFnear.self_of_nhds (b66g_mu R t a w)
    rw [← hy] at hn
    rw [hn, hφμ]
    rfl
  · have hwne : M.y₀.val ∈ (R.atlas.A a).source → w ≠ b66g_slice R t a M.y₀ := by
      intro ha h
      apply hy
      change b66g_inv R t a w = M.y₀
      rw [h]; exact b66g_inv_slice_eq R t a M.y₀ ha
    have hev : M.τ a =ᶠ[𝓝 w] fun z => (M.F + M.P) (b66g_inv R t a z) + M.g a z := by
      filter_upwards [b66g_ML.Q_eq_off M a hwne] with z hz
      simp only [b66g_ML.τ, hz, Pi.add_apply]
      ring
    have hFPd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (M.F + M.P) y :=
      ((M.hF y).add (M.hP y hy)).mdifferentiableAt (by simp)
    obtain ⟨hd1, hdb1⟩ := b66g_chart_dbar R t hw hFPd
    have hg := b66g_ML.g_analytic M a hwne
    obtain ⟨-, hgb⟩ := b66g_wd_of_hasDerivAt hg.differentiableAt.hasDerivAt
    have hsum := b66g_wd_add (f := (M.F + M.P) ∘ b66g_inv R t a) hd1
      (hg.differentiableAt.restrictScalars ℝ)
    have hdiff : DifferentiableAt ℝ (fun z => (M.F + M.P) (b66g_inv R t a z) + M.g a z) w :=
      hd1.add (hg.differentiableAt.restrictScalars ℝ)
    refine ⟨hdiff.congr_of_eventuallyEq hev, ?_⟩
    have hwdb : b66g_wdb (M.τ a) w =
        b66g_wdb (fun z => (M.F + M.P) (b66g_inv R t a z) + M.g a z) w := by
      unfold b66g_wdb; rw [hev.fderiv_eq]
    rw [hwdb]
    have := hsum.2
    simp only [Function.comp_apply] at this
    rw [this, hdb1, hgb, add_zero, M.hFP y hy (b66g_mu R t a w), hφμ]
    rfl

/-- The lift: the holomorphic Wirtinger derivatives of the chart splittings. -/
def b66g_ML.β (a : b66k_Index R) : ℂ → ℂ := b66g_wd (M.τ a)

theorem b66g_ML.β_analytic (a : b66k_Index R) :
    AnalyticOnNhd ℂ (M.β a) (b66k_domain R t a) := by
  intro w₀ hw₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (b66g_domain_open R t a) w₀ hw₀
  have hωan : AnalyticOnNhd ℂ (M.ωa a) (b66k_domain R t a) :=
    (b66g_forms_spec R t 1 (b66g_ofForm_mem R t φ.2)).1 a
  obtain ⟨Ω, hΩ⟩ := (hωan.differentiableOn.mono hball).isExactOn_ball
  let G : ℂ → ℂ := fun z => M.τ a z - conj (Ω z)
  have hG : ∀ z ∈ Metric.ball w₀ r, DifferentiableAt ℝ G z ∧ b66g_wdb G z = 0 ∧
      b66g_wd G z = M.β a z := by
    intro z hz
    obtain ⟨hτd, hτb⟩ := M.τ_spec a (hball hz)
    obtain ⟨hcd, hcw, hcb⟩ := b66g_wd_conj (hΩ z hz)
    have hs := b66g_wd_sub hτd hcd
    refine ⟨hτd.sub hcd, ?_, ?_⟩
    · rw [hs.2, hτb, hcb]; ring
    · rw [hs.1, hcw, sub_zero]; rfl
  have hGd : ∀ z ∈ Metric.ball w₀ r, HasDerivAt G (M.β a z) z := fun z hz => by
    have := b66g_hasDerivAt_of_wdb (hG z hz).1 (hG z hz).2.1
    rwa [(hG z hz).2.2] at this
  have hGdo : DifferentiableOn ℂ G (Metric.ball w₀ r) := fun z hz =>
    (hGd z hz).differentiableAt.differentiableWithinAt
  have hGan : AnalyticOnNhd ℂ G (Metric.ball w₀ r) := hGdo.analyticOnNhd Metric.isOpen_ball
  refine (hGan.deriv w₀ (Metric.mem_ball_self hr)).congr ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with z hz
  exact (hGd z hz).deriv

theorem b66g_coef_law1 {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) {a b : b66k_Index R}
    {w : ℂ} (hw : w ∈ b66k_refinementDomain R t 1 a b) :
    b66g_coef R t q a w = b66g_coef R t q b (b66k_transition R a b (t.val, w)) *
      fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1) := by
  obtain ⟨-, hql, -⟩ := b66g_forms_spec R t 1 hq
  have hb : (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A b).source := by
    have := hw.2; rwa [one_smul] at this
  obtain ⟨-, hx⟩ := b66g_trans_inv R t a b w hw.1 hb
  have hvert := b66g_vertical_eq_D R t a b w hw.1
  have hlaw := hql a b _ (b66g_inv_point R t a w hw.1).1 hb
  simp only [b66g_coef, hx]
  rw [hlaw, pow_one, hvert]
  ring

/-- The coboundary of the chart splittings. -/
def b66g_ML.s : b66k_Cochain R := b66g_scalarBoundary R t M.τ

theorem b66g_refD_eventually {a b : b66k_Index R} {w : ℂ}
    (hw : w ∈ b66k_refinementDomain R t 1 a b) :
    ∀ᶠ z in 𝓝 w, z ∈ b66k_refinementDomain R t 1 a b := by
  filter_upwards [b66g_overlap_eventually R t a b w hw,
    (b66g_domain_open R t a).mem_nhds hw.1] with z hz hzd
  refine ⟨hzd, ?_⟩
  rw [one_smul]
  exact hz.1.2

theorem b66g_ML.S_eventually {a b : b66k_Index R} {w : ℂ}
    (hw : w ∈ b66k_refinementDomain R t 1 a b) :
    (fun z => M.s a b ((R.atlas.A a).symm (t.val, z)).2) =ᶠ[𝓝 w]
      fun z => M.τ a z - M.τ b (b66k_transition R a b (t.val, z)) := by
  filter_upwards [b66g_overlap_eventually R t a b w hw] with z hz
  simp only [b66g_ML.s, b66g_scalarBoundary, hz.1, ↓reduceIte, hz.2.1, hz.2.2]

theorem b66g_ML.S_hasDerivAt {a b : b66k_Index R} {w : ℂ}
    (hw : w ∈ b66k_refinementDomain R t 1 a b) :
    HasDerivAt (fun z => M.τ a z - M.τ b (b66k_transition R a b (t.val, z)))
      (M.β a w - M.β b (b66k_transition R a b (t.val, w)) *
        fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1)) w := by
  obtain ⟨hm, hτd, -, -⟩ := b66g_transition_mem R t a b w hw
  have htr := b66g_transition_hasDerivAt R t a b w hm
  obtain ⟨hτa, hτab⟩ := M.τ_spec a hw.1
  obtain ⟨hτb, hτbb⟩ := M.τ_spec b hτd
  obtain ⟨hcd, hcw, hcb⟩ := b66g_wd_comp (f := M.τ b) hτb htr
  have hs := b66g_wd_sub (f := M.τ a) (g := M.τ b ∘ fun z => b66k_transition R a b (t.val, z))
    hτa hcd
  have hlaw := b66g_coef_law1 (b66g_ofForm_mem R t φ.2) hw
  have h0 : b66g_wdb (fun z => M.τ a z - (M.τ b ∘ fun z => b66k_transition R a b (t.val, z)) z)
      w = 0 := by
    rw [hs.2, hcb, hτab, hτbb]
    change conj (b66g_coef R t (b66g_ofForm R t φ.1) a w) -
      conj (b66g_coef R t (b66g_ofForm R t φ.1) b (b66k_transition R a b (t.val, w))) *
        conj (fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1)) = 0
    rw [hlaw, map_mul, sub_self]
  have hd : HasDerivAt (fun z => M.τ a z - (M.τ b ∘ fun z => b66k_transition R a b (t.val, z)) z)
      (b66g_wd (fun z => M.τ a z - (M.τ b ∘ fun z => b66k_transition R a b (t.val, z)) z) w) w :=
    b66g_hasDerivAt_of_wdb (hτa.sub hcd) h0
  rw [hs.1, hcw] at hd
  exact hd

theorem b66g_ML.s_mem : M.s ∈ b66g_scalarCycles R t := by
  apply Submodule.subset_span
  refine ⟨fun a b w hw => ?_, fun a b x hx => ?_, fun a b c x ha hb hc => ?_⟩
  · refine AnalyticAt.congr ?_ (M.S_eventually hw).symm
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [b66g_refD_eventually hw] with z hz
    exact (M.S_hasDerivAt hz).differentiableAt
  · simp only [b66g_ML.s, b66g_scalarBoundary, hx, ↓reduceIte]
  · have hab : (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source := ⟨ha, hb⟩
    have hac : (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A c).source := ⟨ha, hc⟩
    have hbc : (t, x) ∈ (R.atlas.A b).source ∩ (R.atlas.A c).source := ⟨hb, hc⟩
    simp only [b66g_ML.s, b66g_scalarBoundary, hab, hac, hbc, ↓reduceIte]
    ring

theorem b66g_ML.isLift : b66g_IsLift R t M.s M.β :=
  ⟨M.β_analytic, fun _ _ _ hw => (M.S_hasDerivAt hw).congr_of_eventuallyEq (M.S_eventually hw)⟩

theorem b66g_ML.segInt_beta (a : b66k_Index R) {c e : ℂ} (hseg : b66g_SegIn R t a c e) :
    b66g_segInt (M.β a) c e = M.τ a e - M.τ a c - conj (b66g_segInt (M.ωa a) c e) := by
  set p : ℝ → ℂ := fun r => c + (r : ℂ) * (e - c) with hpdef
  have hpc : Continuous p := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hp : ∀ r : ℝ, HasDerivAt p (e - c) r := fun r => by
    have := ((hasDerivAt_id r).ofReal_comp.mul_const (e - c)).const_add c
    simp only [id, Complex.ofReal_one, one_mul] at this
    exact this
  have hωan : AnalyticOnNhd ℂ (M.ωa a) (b66k_domain R t a) :=
    (b66g_forms_spec R t 1 (b66g_ofForm_mem R t φ.2)).1 a
  set f : ℝ → ℂ := fun r => M.ωa a (p r) * (e - c)
  have hOpen : IsOpen {r : ℝ | p r ∈ b66k_domain R t a} :=
    (b66g_domain_open R t a).preimage hpc
  have hfc : ContinuousOn f {r : ℝ | p r ∈ b66k_domain R t a} := fun r hr =>
    ((hωan _ hr).continuousAt.comp_of_eq hpc.continuousAt rfl).mul
      continuousAt_const |>.continuousWithinAt
  have hIcc : Icc (0 : ℝ) 1 ⊆ {r : ℝ | p r ∈ b66k_domain R t a} := fun r hr => hseg r hr
  set J : ℝ → ℂ := fun r => ∫ ρ in (0 : ℝ)..r, f ρ
  have hJ : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt J (f r) r := by
    intro r hr
    refine intervalIntegral.integral_hasDerivAt_right ?_
      (hfc.stronglyMeasurableAtFilter hOpen r (hIcc hr))
      ((hfc r (hIcc hr)).continuousAt (hOpen.mem_nhds (hIcc hr)))
    apply (hfc.mono ?_).intervalIntegrable
    rw [uIcc_of_le hr.1]
    exact (Icc_subset_Icc le_rfl hr.2).trans hIcc
  set L : ℝ → ℂ := fun r => M.τ a (p r) - conj (J r)
  have hL : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt L (M.β a (p r) * (e - c)) r := by
    intro r hr
    rw [uIcc_of_le zero_le_one] at hr
    obtain ⟨hτd, hτb⟩ := M.τ_spec a (hseg r hr)
    have h1 : HasDerivAt (M.τ a ∘ p) (fderiv ℝ (M.τ a) (p r) (e - c)) r :=
      hτd.hasFDerivAt.comp_hasDerivAt r (hp r)
    have h2 : HasDerivAt (fun r => conj (J r)) (conj (f r)) r := by
      have := ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt r
        (hJ r hr)
      exact this
    convert h1.sub h2 using 1
    · rfl
    · rw [b66g_fderiv_decomp, hτb]
      simp only [f, map_mul]
      unfold b66g_ML.β
      ring
  have hLi : IntervalIntegrable (fun r => M.β a (p r) * (e - c)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    intro r hr
    exact (((M.β_analytic a _ (hseg r hr)).continuousAt.comp_of_eq hpc.continuousAt rfl).mul
      continuousAt_const).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hL hLi
  have hp0 : p 0 = c := by simp [hpdef]
  have hp1 : p 1 = e := by simp [hpdef]
  have hJ0 : J 0 = 0 := intervalIntegral.integral_same
  change ∫ r in (0 : ℝ)..1, M.β a (p r) * (e - c) = _
  rw [hftc]
  simp only [L, hp0, hp1, hJ0, map_zero, sub_zero]
  change M.τ a e - conj (∫ ρ in (0 : ℝ)..1, f ρ) - M.τ a c = _
  have hseq : (∫ ρ in (0 : ℝ)..1, f ρ) = b66g_segInt (M.ωa a) c e := rfl
  rw [hseq]
  ring

theorem b66g_junction {D : b66g_Poly R} (hD : D.Valid t) (v : b66k_Index R → ℂ → ℂ) (k : ℤ) :
    b66g_scalarBoundary R t v (D.a (k + 1)) (D.a k) (D.V t (k + 1)).val.2 =
      v (D.a (k + 1)) (D.c (k + 1)) - v (D.a k) (D.E t.val k) := by
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

/-- Chain periods of the Mittag-Leffler class are the negated conjugate periods of the form. -/
theorem b66g_ML.cdr_eq {D : b66g_Poly R} (hD : D.Valid t) :
    b66g_cdr R t D M.β M.s = -conj (b3_period ℂ (rf8_fibre R.C t) (D.smoothLoop hD) φ) := by
  have hterm : ∀ k : ℤ, b66g_segInt (M.β (D.a k)) (D.c k) (D.E t.val k) +
      M.s (D.a (k + 1)) (D.a k) (D.V t (k + 1)).val.2 =
      (M.τ (D.a (k + 1)) (D.c (k + 1)) - M.τ (D.a k) (D.c k)) -
        conj (b66g_segInt (M.ωa (D.a k)) (D.c k) (D.E t.val k)) := by
    intro k
    rw [M.segInt_beta (D.a k) (hD k).1]
    change _ + b66g_scalarBoundary R t M.τ _ _ _ = _
    rw [b66g_junction hD]
    ring
  have hωan : ∀ k, ContinuousOn (M.ωa (D.a k)) (b66k_domain R t (D.a k)) := fun k =>
    ((b66g_forms_spec R t 1 (b66g_ofForm_mem R t φ.2)).1 (D.a k)).continuousOn
  rw [D.period_eq hD φ (fun k => M.ωa (D.a k)) (fun k y hy v => ?_) hωan]
  · unfold b66g_cdr
    refine (Finset.sum_congr rfl fun (k : ℕ) _ => hterm k).trans ?_
    rw [Finset.sum_sub_distrib, map_sum, ← Finset.sum_neg_distrib]
    have := Finset.sum_range_sub (fun k : ℕ => M.τ (D.a k) (D.c k)) D.N
    push_cast at this
    rw [this]
    have h0 := D.a_add 0
    have h0' := D.c_add 0
    simp only [zero_add] at h0 h0'
    simp only [h0, h0', sub_self, zero_sub]
    rw [Finset.sum_neg_distrib]
    rfl
  · have h1 := b66g_toForm_apply R t (b66g_ofForm_mem R t φ.2) (D.a k) y hy v
    rw [b66g_toForm_ofForm R t φ.2.2] at h1
    rw [h1]
    simp only [b66g_coef, b66g_inv_slice R t (D.a k) y hy]

end B66gMLData

section B66gHodge

variable (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base) {n : ℕ}
  (B : Module.Basis (Fin n) ℤ (b66g_Homology R s))

theorem b66g_P_surjective : Function.Surjective (R.P t) := by
  intro l
  have hle : b3_periodLattice ℂ (rf8_fibre R.C t) ≤ (LinearMap.range (R.P t)).toAddSubgroup.map
      (b3_periodLattice ℂ (rf8_fibre R.C t)).subtype := by
    refine AddSubgroup.closure_le _ |>.2 ?_
    rintro _ ⟨γ, rfl⟩
    exact ⟨b3_latticePeriod ℂ _ γ, ⟨b6m_loopClass _ γ, R.hP t γ⟩, rfl⟩
  obtain ⟨l', ⟨x, hx⟩, hl'⟩ := hle l.property
  refine ⟨x, ?_⟩
  rw [hx]
  exact Subtype.ext hl'

/-- The ℤ-linear functional of periods on a fixed form. -/
def b66g_evalF (κ : b3_HolForm ℂ (rf8_fibre R.C t)) : b6m_H1 (rf8_fibre R.C t) →+ ℂ where
  toFun x := (R.P t x).val κ
  map_zero' := by simp
  map_add' x y := by simp

theorem b66g_perMap_basis_eq_zero {F : b6m_H1 (rf8_fibre R.C t) →ₗ[ℤ] ℂ}
    (hF : ∀ i, F (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i)) = 0)
    (x : b6m_H1 (rf8_fibre R.C t)) : F x = 0 := by
  let B' := B.map (b6m_H1Equiv (b6m_transport mr_base R.C s t))
  rw [← B'.sum_repr x, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.map_smul]
  have : F (B' i) = 0 := by
    rw [show B' i = b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i) from
      Module.Basis.map_apply _ _ _]
    exact hF i
  rw [this, smul_zero]

/-- Conjugates of holomorphic period vectors. -/
def b66g_conjPer : Submodule ℂ (Fin n → ℂ) where
  carrier := {v | (fun i => conj (v i)) ∈ LinearMap.range (b66g_perMap R s t B)}
  add_mem' := by
    intro v w hv hw
    have hv' : (fun i => conj (v i)) ∈ LinearMap.range (b66g_perMap R s t B) := hv
    have hw' : (fun i => conj (w i)) ∈ LinearMap.range (b66g_perMap R s t B) := hw
    have := Submodule.add_mem _ hv' hw'
    change (fun i => conj ((v + w) i)) ∈ LinearMap.range (b66g_perMap R s t B)
    convert this using 1
    funext i
    simp [map_add]
  zero_mem' := by
    change (fun i => conj ((0 : Fin n → ℂ) i)) ∈ LinearMap.range (b66g_perMap R s t B)
    convert Submodule.zero_mem (LinearMap.range (b66g_perMap R s t B)) using 1
    funext i
    simp
  smul_mem' := by
    intro c v hv
    have hv' : (fun i => conj (v i)) ∈ LinearMap.range (b66g_perMap R s t B) := hv
    have := Submodule.smul_mem _ (conj c) hv'
    change (fun i => conj ((c • v) i)) ∈ LinearMap.range (b66g_perMap R s t B)
    convert this using 1
    funext i
    simp [map_mul]

theorem b66g_perMap_inf : LinearMap.range (b66g_perMap R s t B) ⊓ b66g_conjPer R s t B = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨⟨κ₁, rfl⟩, ⟨κ₂, h2⟩⟩
  have hi : ∀ i, (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i))).val κ₂ =
      conj ((R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i))).val κ₁) :=
    fun i => congrFun h2 i
  let ev : b3_periodLattice ℂ (rf8_fibre R.C t) →+ ℂ :=
    { toFun := fun l => l.val κ₂ - conj (l.val κ₁)
      map_zero' := by simp
      map_add' := fun l l' => by simp only [AddSubgroup.coe_add, Pi.add_apply, map_add]; ring }
  let F : b6m_H1 (rf8_fibre R.C t) →ₗ[ℤ] ℂ := ev.toIntLinearMap ∘ₗ R.P t
  have hF := b66g_perMap_basis_eq_zero R s t B (F := F) (fun i => by
    change (R.P t _).val κ₂ - conj ((R.P t _).val κ₁) = 0
    rw [hi i, sub_self])
  have hall : ∀ l : b3_periodLattice ℂ (rf8_fibre R.C t), l.val κ₂ = conj (l.val κ₁) := by
    intro l
    obtain ⟨x, rfl⟩ := b66g_P_surjective R t l
    have := hF x
    change (R.P t x).val κ₂ - conj ((R.P t x).val κ₁) = 0 at this
    exact sub_eq_zero.1 this
  have hlin := b66g_lattice_linear R t
  have h12 : κ₁ - κ₂ = 0 := by
    apply b3Rest2_eq_zero_of_re_lattice (E := ℂ) (C := rf8_fibre R.C t) (by simp)
    intro l
    have h := hlin l (-1) κ₂ κ₁
    have hsub : κ₁ - κ₂ = (-1 : ℂ) • κ₂ + κ₁ := by
      rw [neg_one_smul, neg_add_eq_sub]
    rw [hsub, h, hall l]
    simp
  have hκ : κ₁ = κ₂ := sub_eq_zero.1 h12
  have hz : Complex.I • κ₁ = 0 := by
    apply b3Rest2_eq_zero_of_re_lattice (E := ℂ) (C := rf8_fibre R.C t) (by simp)
    intro l
    have h := hlin l Complex.I κ₁ 0
    have h0 := hlin l 1 0 0
    simp only [add_zero, one_smul, one_mul, smul_zero] at h h0
    have hz0 : l.val 0 = 0 := by linear_combination -h0
    rw [h, hz0, add_zero]
    have hr := hall l
    rw [← hκ] at hr
    have him : (l.val κ₁).im = 0 := by
      have := congrArg Complex.im hr
      simp only [Complex.conj_im] at this
      linarith
    simp [Complex.mul_re, him]
  have hκ0 : κ₁ = 0 := by
    have := congrArg (fun x => (-Complex.I) • x) hz
    simpa [smul_smul] using this
  rw [hκ0, map_zero]
  exact (Submodule.mem_bot ℂ).2 rfl

/-- Conjugation identifies the two period subspaces over `ℝ`. -/
def b66g_conjEquiv : b66g_conjPer R s t B ≃ₗ[ℝ] LinearMap.range (b66g_perMap R s t B) where
  toFun v := ⟨fun i => conj (v.1 i), v.2⟩
  invFun w := ⟨fun i => conj (w.1 i), by
    change (fun i => conj (conj (w.1 i))) ∈ LinearMap.range (b66g_perMap R s t B)
    simpa using w.2⟩
  map_add' v w := by
    apply Subtype.ext; funext i
    simp [map_add]
  map_smul' r v := by
    apply Subtype.ext; funext i
    simp [Complex.real_smul, map_mul]
  left_inv v := by
    apply Subtype.ext; funext i
    simp
  right_inv w := by
    apply Subtype.ext; funext i
    simp

theorem b66g_conjPer_finrank :
    Module.finrank ℂ (b66g_conjPer R s t B) =
      Module.finrank ℂ (LinearMap.range (b66g_perMap R s t B)) := by
  have h := (b66g_conjEquiv R s t B).finrank_eq
  rw [finrank_real_of_complex, finrank_real_of_complex] at h
  omega

/-- Holomorphic and conjugate holomorphic period vectors span. -/
theorem b66g_hodge_decomp (v : Fin n → ℂ) :
    ∃ κ₁ κ₂ : b3_HolForm ℂ (rf8_fibre R.C t),
      v = b66g_perMap R s t B κ₁ + fun i => conj (b66g_perMap R s t B κ₂ i) := by
  have := b3A_holForm_finiteDimensional (E := ℂ) (C := rf8_fibre R.C t) (by simp)
  have hr := LinearMap.finrank_range_of_inj (b66g_perMap_injective R s t B)
  have hc := b66g_conjPer_finrank R s t B
  have hn := b66g_n_eq R t B
  have hsi := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (b66g_perMap R s t B))
    (b66g_conjPer R s t B)
  rw [b66g_perMap_inf, finrank_bot] at hsi
  have htop : LinearMap.range (b66g_perMap R s t B) ⊔ b66g_conjPer R s t B = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    omega
  have hv : v ∈ LinearMap.range (b66g_perMap R s t B) ⊔ b66g_conjPer R s t B := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨y, ⟨κ₁, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨κ₂, hκ₂⟩ := (hz : (fun i => conj (z i)) ∈ LinearMap.range (b66g_perMap R s t B))
  refine ⟨κ₁, κ₂, ?_⟩
  congr 1
  funext i
  have := congrFun hκ₂ i
  change b66g_perMap R s t B κ₂ i = conj (z i) at this
  rw [this]
  simp

end B66gHodge

section B66gSurjective

variable {R : rf8_SharedFamily} {s t : b6t_polydisc mr_base} {n : ℕ}
  {B : Module.Basis (Fin n) ℤ (b66g_Homology R s)}

theorem b66g_perMap_eq_sum (P : b66g_Rep R s t B) (φ : b3_HolForm ℂ (rf8_fibre R.C t)) (i : Fin n) :
    b66g_perMap R s t B φ i =
      ∑ j, (P.f i j : ℂ) * b3_period ℂ (rf8_fibre R.C t) ((P.D i j).smoothLoop (P.hv i j)) φ := by
  have h := congrFun (b66g_cdrVec_form P ((b66g_formEquiv R t).symm φ)) i
  rw [LinearEquiv.apply_symm_apply] at h
  rw [show b66g_perMap R s t B φ i =
    (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i))).val φ from rfl, ← h]
  unfold b66g_cdrVec
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [b66g_cdr_form R _ (P.hv i j), LinearEquiv.apply_symm_apply]

theorem b66g_ML.cdrVec_eq (P : b66g_Rep R s t B) {φ : b3_HolForm ℂ (rf8_fibre R.C t)}
    (M : b66g_ML R t φ) :
    b66g_cdrVec P M.β M.s = fun i => -conj (b66g_perMap R s t B φ i) := by
  funext i
  rw [b66g_perMap_eq_sum P φ i, map_sum, ← Finset.sum_neg_distrib]
  unfold b66g_cdrVec
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [M.cdr_eq (P.hv i j), map_mul, map_intCast]
  ring

/-- The comparison is surjective on liftable classes. -/
theorem b66g_E0_surjective (P : b66g_Rep R s t B) : Function.Surjective (b66g_E0 P) := by
  intro y
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨κ₁, κ₂, rfl⟩ := b66g_hodge_decomp R s t B v
  obtain ⟨M⟩ := b66g_ML_exists (R := R) (t := t) κ₂
  have hmem : ((M.s, M.β) : b66k_Cochain R × (b66k_Index R → ℂ → ℂ)) ∈ b66g_L R t :=
    ⟨M.s_mem, M.isLift⟩
  let p : b66g_L R t := ⟨(-1 : ℂ) • (M.s, M.β), (b66g_L R t).smul_mem _ hmem⟩
  refine ⟨⟨b66g_psi R t p, LinearMap.mem_range_self _ p⟩, ?_⟩
  rw [b66g_E0_apply]
  change (b66g_periodSubspace R s t B).mkQ (b66g_cdrVec P ((-1 : ℂ) • M.β) ((-1 : ℂ) • M.s)) = _
  rw [b66g_cdrVec_smul, M.cdrVec_eq P, map_add]
  have h0 : (b66g_periodSubspace R s t B).mkQ (b66g_perMap R s t B κ₁) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, b66g_periodSubspace_eq]
    exact LinearMap.mem_range_self _ κ₁
  rw [h0, zero_add]
  congr 1
  funext i
  simp

end B66gSurjective

end HodgeLean.Foundations.Program

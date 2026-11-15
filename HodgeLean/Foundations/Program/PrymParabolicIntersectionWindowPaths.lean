import HodgeLean.Foundations.Program.PrymParabolicIntersectionWindows

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter Complex
open scoped Topology ContDiff Manifold
namespace HodgeLean.Foundations.Program

theorem hga_step_le_half {τ : ℝ} (h : τ ≤ 1 / 2) : hga_step τ ≤ 1 / 2 := by
  rw [← hga_step_half]
  exact Real.smoothTransition.monotone (by linarith)

theorem hga_step_gt_half {τ : ℝ} (h : 1 / 2 < τ) : 1 / 2 < hga_step τ := by
  rcases le_or_gt (2 / 3) τ with h2 | h2
  · rw [hga_step, Real.smoothTransition.one_of_one_le (by linarith)]; norm_num
  · rw [← hga_step_half]
    exact hga_smoothTransition_strictMonoOn ⟨by norm_num, by norm_num⟩
      ⟨by linarith, by linarith⟩ (by linarith)

theorem hga_projIcc_val {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ((Set.projIcc (0 : ℝ) 1 zero_le_one x : unitInterval) : ℝ) = x := by
  rw [Set.projIcc_of_mem _ hx]

section Generic

variable {G : Type} [Group G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
variable (W : hga_WindowSpec) (D : hg8_DeltaMap g T) (ε : hg2_Edge G 13)
  (τo τi : hg2_Tri G 13)

/-- **The dual window**: the ray of `τo` traversed towards the edge, then the ray of `τi` away
from it, parametrized by the smooth step.
Source: barycentric dual cells (Hatcher, §3.3); `hga_WindowSpec`. -/
def hga_dualWin (τ : ℝ) : T :=
  if hga_step τ ≤ 1 / 2 then D.tri τo (W.Mo (Set.projIcc 0 1 zero_le_one (1 - 2 * hga_step τ)))
  else D.tri τi (W.Mi (Set.projIcc 0 1 zero_le_one (2 * hga_step τ - 1)))

/-- **The primal window**: the edge between the parameters `s ∓ δ`, at the speed of the smooth
step. Source: `hga_WindowSpec.primParam`. -/
def hga_primWin (τ : ℝ) : T := D.edge ε (Set.projIcc 0 1 zero_le_one (W.primParam τ))

variable {W D ε τo τi}

theorem hga_dualWin_meet (hfo : hg5_face (D.tri τo) W.ko = D.edge ε)
    (hfi : hg5_face (D.tri τi) W.ki = D.edge ε) :
    D.tri τo (W.Mo 0) = D.edge ε (Set.projIcc 0 1 zero_le_one W.s) ∧
      D.tri τi (W.Mi 0) = D.edge ε (Set.projIcc 0 1 zero_le_one W.s) := by
  rw [W.Mo0, W.Mi0, hga_face_facePt, hga_face_facePt, hfo, hfi]
  exact ⟨rfl, rfl⟩

theorem hga_dualWin_continuous (hfo : hg5_face (D.tri τo) W.ko = D.edge ε)
    (hfi : hg5_face (D.tri τi) W.ki = D.edge ε) :
    Continuous (hga_dualWin W D τo τi) := by
  have hs : Continuous hga_step := hga_step_contDiff.continuous
  apply Continuous.if_le
  · exact (D.tri τo).continuous.comp (W.Mo.continuous.comp
      (continuous_projIcc.comp (continuous_const.sub (continuous_const.mul hs))))
  · exact (D.tri τi).continuous.comp (W.Mi.continuous.comp
      (continuous_projIcc.comp ((continuous_const.mul hs).sub continuous_const)))
  · exact hs
  · exact continuous_const
  · intro τ hτ
    have h1 : Set.projIcc (0 : ℝ) 1 zero_le_one (1 - 2 * hga_step τ) = 0 := by
      rw [hτ]; apply Subtype.ext; simp
    have h2 : Set.projIcc (0 : ℝ) 1 zero_le_one (2 * hga_step τ - 1) = 0 := by
      rw [hτ]; apply Subtype.ext; simp
    rw [h1, h2, (hga_dualWin_meet hfo hfi).1, (hga_dualWin_meet hfo hfi).2]

theorem hga_primWin_continuous : Continuous (hga_primWin W D ε) := by
  unfold hga_primWin hga_WindowSpec.primParam
  have hs : Continuous hga_step := hga_step_contDiff.continuous
  exact (D.edge ε).continuous.comp (continuous_projIcc.comp
    (continuous_const.add (continuous_const.mul ((continuous_const.mul hs).sub continuous_const))))

variable (pr : T → OnePoint ℂ) (hD : ∀ τ a, pr (D.tri τ a) = hg5_tri (hg5_triBase τ) a)
include hD

theorem hga_dualWin_proj (hbo : hg5_triBase τo = W.τo) (hbi : hg5_triBase τi = W.τi) (τ : ℝ) :
    pr (hga_dualWin W D τo τi τ) = (W.dualCurve τ : OnePoint ℂ) := by
  obtain ⟨h0, h1⟩ := hga_step_mem τ
  unfold hga_dualWin hga_WindowSpec.dualCurve
  split_ifs with h
  · rw [hD, hbo, W.Mo_img, hga_projIcc_val ⟨by linarith, by linarith⟩]
  · rw [hD, hbi, W.Mi_img, hga_projIcc_val ⟨by linarith, by linarith⟩]
    congr 1
    push_cast
    ring

theorem hga_primWin_proj (τe : hg2_Tri G 13) (hbe : hg5_triBase τe = W.τe)
    (hfe : hg5_face (D.tri τe) W.ke = D.edge ε) (τ : ℝ) :
    pr (hga_primWin W D ε τ) = (W.primCurve τ : OnePoint ℂ) := by
  unfold hga_primWin
  rw [← hfe, ← hga_face_facePt, hD, hbe, W.E_img _ (W.primParam_mem τ)]
  rfl

omit hD in
theorem hga_dualWin_near_zero :
    hga_dualWin W D τo τi =ᶠ[𝓝 0] fun _ ↦ D.tri τo (W.Mo 1) := by
  filter_upwards [hga_step_eventually_zero] with τ hτ
  unfold hga_dualWin
  rw [if_pos (by rw [hτ]; norm_num), hτ, show (1 : ℝ) - 2 * 0 = 1 by norm_num, Set.projIcc_right]
  rfl

omit hD in
theorem hga_dualWin_near_one :
    hga_dualWin W D τo τi =ᶠ[𝓝 1] fun _ ↦ D.tri τi (W.Mi 1) := by
  filter_upwards [hga_step_eventually_one] with τ hτ
  unfold hga_dualWin
  rw [if_neg (by rw [hτ]; norm_num), hτ, show (2 : ℝ) * 1 - 1 = 1 by norm_num, Set.projIcc_right]
  rfl

omit hD in
theorem hga_primWin_near_zero :
    hga_primWin W D ε =ᶠ[𝓝 0] fun _ ↦ D.edge ε (Set.projIcc 0 1 zero_le_one (W.s - W.δ)) := by
  filter_upwards [hga_step_eventually_zero] with τ hτ
  unfold hga_primWin hga_WindowSpec.primParam
  rw [hτ]
  congr 3
  ring

omit hD in
theorem hga_primWin_near_one :
    hga_primWin W D ε =ᶠ[𝓝 1] fun _ ↦ D.edge ε (Set.projIcc 0 1 zero_le_one (W.s + W.δ)) := by
  filter_upwards [hga_step_eventually_one] with τ hτ
  unfold hga_primWin hga_WindowSpec.primParam
  rw [hτ]
  congr 3
  ring

/-- **The windows cross once**, at the middle of both. -/
theorem hga_windows_cross (hbo : hg5_triBase τo = W.τo) (hbi : hg5_triBase τi = W.τi)
    (τe : hg2_Tri G 13) (hbe : hg5_triBase τe = W.τe)
    (hfe : hg5_face (D.tri τe) W.ke = D.edge ε) (τ₁ τ₂ : ℝ)
    (h : hga_dualWin W D τo τi τ₁ = hga_primWin W D ε τ₂) : τ₁ = 1 / 2 ∧ τ₂ = 1 / 2 := by
  have hp := congrArg pr h
  rw [hga_dualWin_proj pr hD hbo hbi, hga_primWin_proj pr hD τe hbe hfe] at hp
  have hc := OnePoint.coe_injective hp
  unfold hga_WindowSpec.dualCurve hga_WindowSpec.primCurve at hc
  have hc' : (((1 - 2 * hga_step τ₁) * W.η : ℝ) : ℂ) * I = ((W.φ (W.primParam τ₂) : ℝ) : ℂ) := by
    have := add_left_cancel hc
    rw [← mul_assoc] at this
    exact mul_right_cancel₀ W.hv this
  have hre := congrArg Complex.re hc'
  have him := congrArg Complex.im hc'
  simp at hre him
  have hη := W.hη
  have h1 : hga_step τ₁ = 1 / 2 := by
    rcases him with h | h
    · linarith
    · linarith
  have h2 : W.primParam τ₂ = W.s :=
    W.φ_inj (W.primParam_mem τ₂) ⟨by linarith [W.hδ], by linarith [W.hδ]⟩ (by rw [← hre, W.φ_s])
  have h3 : hga_step τ₂ = 1 / 2 := by
    unfold hga_WindowSpec.primParam at h2
    have := W.hδ
    have : W.δ * (2 * hga_step τ₂ - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  exact ⟨(hga_step_eq_half_iff τ₁).mp h1, (hga_step_eq_half_iff τ₂).mp h3⟩

omit hD in
theorem hga_windows_meet (hfo : hg5_face (D.tri τo) W.ko = D.edge ε)
    (hfi : hg5_face (D.tri τi) W.ki = D.edge ε) :
    hga_dualWin W D τo τi (1 / 2) = D.edge ε (Set.projIcc 0 1 zero_le_one W.s) ∧
      hga_primWin W D ε (1 / 2) = D.edge ε (Set.projIcc 0 1 zero_le_one W.s) := by
  constructor
  · unfold hga_dualWin
    rw [hga_step_half, if_pos le_rfl]
    have : Set.projIcc (0 : ℝ) 1 zero_le_one (1 - 2 * (1 / 2)) = 0 := by
      apply Subtype.ext; simp
    rw [this]
    exact (hga_dualWin_meet hfo hfi).1
  · unfold hga_primWin hga_WindowSpec.primParam
    rw [hga_step_half]
    congr 3
    ring

omit hD in
/-- The dual window meets the closed cells only at its middle; elsewhere it is interior to one of
the two realized triangles. -/
theorem hga_dualWin_cases (hfo : hg5_face (D.tri τo) W.ko = D.edge ε)
    (hfi : hg5_face (D.tri τi) W.ki = D.edge ε) (τ : ℝ) :
    hga_dualWin W D τo τi τ = D.edge ε (Set.projIcc 0 1 zero_le_one W.s) ∨
      (∃ a, (∀ j, 0 < Convexity.StdSimplex.weights a j) ∧ hga_dualWin W D τo τi τ = D.tri τo a) ∨
      (∃ a, (∀ j, 0 < Convexity.StdSimplex.weights a j) ∧ hga_dualWin W D τo τi τ = D.tri τi a) := by
  obtain ⟨h0, h1⟩ := hga_step_mem τ
  unfold hga_dualWin
  split_ifs with h
  · rcases eq_or_lt_of_le h with he | hlt
    · left
      have : Set.projIcc (0 : ℝ) 1 zero_le_one (1 - 2 * hga_step τ) = 0 := by
        rw [he]; apply Subtype.ext; simp
      rw [this]
      exact (hga_dualWin_meet hfo hfi).1
    · right; left
      refine ⟨_, W.Mo_pos _ ?_, rfl⟩
      rw [hga_projIcc_val ⟨by linarith, by linarith⟩]
      linarith
  · right; right
    refine ⟨_, W.Mi_pos _ ?_, rfl⟩
    push Not at h
    rw [hga_projIcc_val ⟨by linarith, by linarith⟩]
    linarith

end Generic

section Chains

variable {G : Type} [Group G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
variable {W : hga_WindowSpec} {D : hg8_DeltaMap g T} {ε : hg2_Edge G 13} {τo τi : hg2_Tri G 13}

/-- The half point of `[0, 1]`. -/
def hga_halfI : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

theorem hga_dualWin_pathChain (hfo : hg5_face (D.tri τo) W.ko = D.edge ε)
    (hfi : hg5_face (D.tri τi) W.ki = D.edge ε) :
    b6m_pathChain (hga_unitPath (hga_dualWin W D τo τi) (hga_dualWin_continuous hfo hfi)) =
      hga_TL (D.tri τo) (W.Mo 1) (W.Mo 0) + hga_TL (D.tri τi) (W.Mi 0) (W.Mi 1) := by
  have hs : Continuous hga_step := hga_step_contDiff.continuous
  set γ := hga_unitPath (hga_dualWin W D τo τi) (hga_dualWin_continuous hfo hfi)
  have hsub := b6m_pathChain_subdiv γ 0 hga_halfI 1
  rw [b3Rest2_restr_zero_one] at hsub
  rw [hsub]
  let g₁ : C(unitInterval, Convexity.StdSimplex ℝ (Fin 3)) :=
    W.Mo.comp ⟨fun t ↦ Set.projIcc 0 1 zero_le_one (1 - 2 * hga_step ((t : ℝ) * (1 / 2))),
      continuous_projIcc.comp (continuous_const.sub (continuous_const.mul
        (hs.comp (continuous_subtype_val.mul continuous_const))))⟩
  let g₂ : C(unitInterval, Convexity.StdSimplex ℝ (Fin 3)) :=
    W.Mi.comp ⟨fun t ↦ Set.projIcc 0 1 zero_le_one
        (2 * hga_step (1 / 2 + (t : ℝ) * (1 - 1 / 2)) - 1),
      continuous_projIcc.comp ((continuous_const.mul (hs.comp (continuous_const.add
        (continuous_subtype_val.mul continuous_const)))).sub continuous_const)⟩
  have e₁ : b3Rest2_restr γ 0 hga_halfI = (D.tri τo).comp g₁ := by
    ext t
    change hga_dualWin W D τo τi ((0 : ℝ) + (t : ℝ) * (1 / 2 - 0)) = _
    unfold hga_dualWin
    rw [if_pos (hga_step_le_half (by nlinarith [t.2.1, t.2.2]))]
    simp [g₁]
  have e₂ : b3Rest2_restr γ hga_halfI 1 = (D.tri τi).comp g₂ := by
    ext t
    change hga_dualWin W D τo τi (1 / 2 + (t : ℝ) * (1 - 1 / 2)) = _
    unfold hga_dualWin
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have ht : (t : ℝ) = 0 := h0.symm
      rw [if_pos (by rw [ht, zero_mul, add_zero, hga_step_half])]
      simp only [g₂, ContinuousMap.comp_apply, ContinuousMap.coe_mk, ht, zero_mul, add_zero,
        hga_step_half]
      rw [show (1 : ℝ) - 2 * (1 / 2) = 0 by norm_num, show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num]
      rw [show Set.projIcc (0 : ℝ) 1 zero_le_one 0 = 0 from Set.projIcc_left _]
      rw [(hga_dualWin_meet hfo hfi).1, (hga_dualWin_meet hfo hfi).2]
    · rw [if_neg (not_le.mpr (hga_step_gt_half (by nlinarith)))]
      rfl
  rw [e₁, e₂, hga_TL_eq, hga_TL_eq]
  have h1 : g₁ 0 = W.Mo 1 := by
    simp only [g₁, ContinuousMap.comp_apply, ContinuousMap.coe_mk, Set.Icc.coe_zero, zero_mul]
    rw [show hga_step 0 = 0 from Real.smoothTransition.zero_of_nonpos (by norm_num)]
    rw [show (1 : ℝ) - 2 * 0 = 1 by norm_num, Set.projIcc_right]
    rfl
  have h2 : g₁ 1 = W.Mo 0 := by
    simp only [g₁, ContinuousMap.comp_apply, ContinuousMap.coe_mk, Set.Icc.coe_one, one_mul,
      hga_step_half]
    rw [show (1 : ℝ) - 2 * (1 / 2) = 0 by norm_num, Set.projIcc_left]
    rfl
  have h3 : g₂ 0 = W.Mi 0 := by
    simp only [g₂, ContinuousMap.comp_apply, ContinuousMap.coe_mk, Set.Icc.coe_zero, zero_mul,
      add_zero, hga_step_half]
    rw [show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num, Set.projIcc_left]
    rfl
  have h4 : g₂ 1 = W.Mi 1 := by
    simp only [g₂, ContinuousMap.comp_apply, ContinuousMap.coe_mk, Set.Icc.coe_one, one_mul]
    rw [show (1 : ℝ) / 2 + (1 - 1 / 2) = 1 by norm_num,
      show hga_step 1 = 1 from Real.smoothTransition.one_of_one_le (by norm_num)]
    rw [show (2 : ℝ) * 1 - 1 = 1 by norm_num, Set.projIcc_right]
    rfl
  rw [h1, h2, h3, h4]

theorem hga_primWin_pathChain :
    b6m_pathChain (hga_unitPath (hga_primWin W D ε) hga_primWin_continuous) =
      b6m_pathChain (b3Rest2_restr (D.edge ε) (Set.projIcc 0 1 zero_le_one (W.s - W.δ))
        (Set.projIcc 0 1 zero_le_one (W.s + W.δ))) := by
  have hs : Continuous hga_step := hga_step_contDiff.continuous
  let φ : C(unitInterval, unitInterval) := ⟨fun t ↦ ⟨hga_step t, hga_step_mem t⟩,
    (hs.comp continuous_subtype_val).subtype_mk _⟩
  have hδ := W.hδ
  have h0 := W.hs0
  have h1 := W.hs1
  have e : hga_unitPath (hga_primWin W D ε) hga_primWin_continuous =
      (b3Rest2_restr (D.edge ε) (Set.projIcc 0 1 zero_le_one (W.s - W.δ))
        (Set.projIcc 0 1 zero_le_one (W.s + W.δ))).comp φ := by
    ext t
    change D.edge ε _ = D.edge ε _
    congr 1
    apply Subtype.ext
    obtain ⟨hm0, hm1⟩ := hga_step_mem t
    have hp := W.primParam_mem t
    rw [hga_projIcc_val ⟨by linarith [hp.1], by linarith [hp.2]⟩]
    change _ = ((Set.projIcc 0 1 zero_le_one (W.s - W.δ) : unitInterval) : ℝ) + hga_step t *
      (((Set.projIcc 0 1 zero_le_one (W.s + W.δ) : unitInterval) : ℝ) -
        ((Set.projIcc 0 1 zero_le_one (W.s - W.δ) : unitInterval) : ℝ))
    rw [hga_projIcc_val ⟨by linarith, by linarith⟩, hga_projIcc_val ⟨by linarith, by linarith⟩]
    unfold hga_WindowSpec.primParam
    ring
  rw [e, hga_pathChain_reparam]
  · exact Subtype.ext (Real.smoothTransition.zero_of_nonpos (by norm_num))
  · exact Subtype.ext (Real.smoothTransition.one_of_one_le (by norm_num))

end Chains

section Derivs

variable (W : hga_WindowSpec)

theorem hga_dualCurve_hasDerivAt :
    HasDerivAt W.dualCurve ((((-2 * deriv hga_step (1 / 2)) * W.η : ℝ) : ℂ) * (I * W.v)) (1 / 2) := by
  have hst : HasDerivAt hga_step (deriv hga_step (1 / 2)) (1 / 2) :=
    (hga_step_contDiff.differentiable one_ne_zero (1 / 2)).hasDerivAt
  have hr : HasDerivAt (fun τ ↦ (1 - 2 * hga_step τ) * W.η) ((-2 * deriv hga_step (1 / 2)) * W.η)
      (1 / 2) := by
    have := ((hst.const_mul 2).const_sub 1).mul_const W.η
    simpa using this
  have := (hr.ofReal_comp).mul_const (I * W.v)
  exact this.const_add W.P

theorem hga_primCurve_hasDerivAt :
    HasDerivAt W.primCurve (((deriv W.φ W.s * (W.δ * (2 * deriv hga_step (1 / 2))) : ℝ) : ℂ) * W.v)
      (1 / 2) := by
  have hst : HasDerivAt hga_step (deriv hga_step (1 / 2)) (1 / 2) :=
    (hga_step_contDiff.differentiable one_ne_zero (1 / 2)).hasDerivAt
  have hθ : HasDerivAt W.primParam (W.δ * (2 * deriv hga_step (1 / 2))) (1 / 2) := by
    exact (((hst.const_mul 2).sub_const 1).const_mul W.δ).const_add W.s
  have hθs : W.primParam (1 / 2) = W.s := by
    unfold hga_WindowSpec.primParam; rw [hga_step_half]; ring
  have hφ : HasDerivAt W.φ (deriv W.φ W.s) W.s := by
    have hδ := W.hδ
    have hmem : Ioo (W.s - 2 * W.δ) (W.s + 2 * W.δ) ∈ 𝓝 W.s :=
      Ioo_mem_nhds (by linarith) (by linarith)
    exact ((W.φ_diff.differentiableOn one_ne_zero) W.s
      (mem_of_mem_nhds hmem)).differentiableAt hmem |>.hasDerivAt
  have hcomp : HasDerivAt (W.φ ∘ W.primParam) (deriv W.φ W.s * (W.δ * (2 * deriv hga_step (1 / 2))))
      (1 / 2) := by
    have hφ' : HasDerivAt W.φ (deriv W.φ W.s) (W.primParam (1 / 2)) := by rw [hθs]; exact hφ
    exact hφ'.comp (1 / 2) hθ
  have := (hcomp.ofReal_comp).mul_const W.v
  exact this.const_add W.P

theorem hga_orient_I_mul (v : ℂ) (hv : v ≠ 0) : b3_orient ℂ (I * v) v < 0 := by
  obtain ⟨κ, hκ, hκ'⟩ := b6m_orient_complex_coordinates
  rw [hκ']
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub]
  have : 0 < v.re * v.re + v.im * v.im := by
    have := Complex.normSq_pos.mpr hv
    rwa [Complex.normSq_apply] at this
  nlinarith

theorem hga_windows_plane_sign :
    SignType.sign (b3_orient ℂ (deriv W.dualCurve (1 / 2)) (deriv W.primCurve (1 / 2))) = 1 := by
  rw [(hga_dualCurve_hasDerivAt W).deriv, (hga_primCurve_hasDerivAt W).deriv]
  have hd := hga_step_deriv_half
  have hδ := W.hδ
  have hη := W.hη
  have hφ := W.φ_deriv
  rw [← Complex.real_smul, ← Complex.real_smul, hga_orient_smul_real]
  apply sign_pos
  have h1 : -2 * deriv hga_step (1 / 2) * W.η < 0 := by nlinarith
  have h2 : 0 < deriv W.φ W.s * (W.δ * (2 * deriv hga_step (1 / 2))) := by positivity
  have h3 := hga_orient_I_mul W.v W.hv
  have : 0 < -(-2 * deriv hga_step (1 / 2) * W.η) * (deriv W.φ W.s * (W.δ * (2 * deriv hga_step
      (1 / 2)))) := by nlinarith
  nlinarith

end Derivs

section Fibre

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

variable {G : Type} [Group G] (U : Type) [TopologicalSpace U] [MulAction G U]
  (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
  (C : Type) [TopologicalSpace C] (f : C → OnePoint ℂ)
  (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
  (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
  (hfι : ∀ u, f (ι u) = π u)
  (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
  [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
  [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
  [CompactSpace (b63l_parameterFibre mr_base C V hV t)]
  [ConnectedSpace (b63l_parameterFibre mr_base C V hV t)]
  [T2Space (b63l_parameterFibre mr_base C V hV t)]
  (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
  {G' : Type} [Group G'] {g : Fin 13 → G'}
  {W : hga_WindowSpec} {D : hg8_DeltaMap g (b63l_parameterFibre mr_base C V hV t)}
  {ε : hg2_Edge G' 13} {τo τi τe : hg2_Tri G' 13}
  (hD : ∀ τ a, f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ (D.tri τ a)) =
    hg5_tri (hg5_triBase τ) a)

include hπ hι hιr hfι hk hD

theorem hga_dualWin_good (hbo : hg5_triBase τo = W.τo) (hbi : hg5_triBase τi = W.τi)
    (hfo : hg5_face (D.tri τo) W.ko = D.edge ε) (hfi : hg5_face (D.tri τi) W.ki = D.edge ε) :
    b3A_IsGoodPath (E := ℂ) (hga_dualWin W D τo τi) (D.tri τo (W.Mo 1)) (D.tri τi (W.Mi 1)) :=
  ⟨hga_lift_contMDiff U π hπ C f ι hι hιr hfι V hV t hk _ (hga_dualWin_continuous hfo hfi)
      W.dualCurve W.dualCurve_contDiff
      (hga_dualWin_proj (fun x ↦ f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ x)) hD hbo hbi)
      W.dualCurve_im,
    hga_dualWin_near_zero, hga_dualWin_near_one⟩

theorem hga_primWin_good (hbe : hg5_triBase τe = W.τe)
    (hfe : hg5_face (D.tri τe) W.ke = D.edge ε) :
    b3A_IsGoodPath (E := ℂ) (hga_primWin W D ε)
      (D.edge ε (Set.projIcc 0 1 zero_le_one (W.s - W.δ)))
      (D.edge ε (Set.projIcc 0 1 zero_le_one (W.s + W.δ))) :=
  ⟨hga_lift_contMDiff U π hπ C f ι hι hιr hfι V hV t hk _ hga_primWin_continuous
      W.primCurve W.primCurve_contDiff
      (hga_primWin_proj (fun x ↦ f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ x)) hD τe hbe hfe)
      W.primCurve_im,
    hga_primWin_near_zero, hga_primWin_near_one⟩

/-- **The crossing of the windows is positive** (dual first). -/
theorem hga_windows_sign (hbo : hg5_triBase τo = W.τo) (hbi : hg5_triBase τi = W.τi)
    (hfo : hg5_face (D.tri τo) W.ko = D.edge ε) (hfi : hg5_face (D.tri τi) W.ki = D.edge ε)
    (hbe : hg5_triBase τe = W.τe) (hfe : hg5_face (D.tri τe) W.ke = D.edge ε) :
    SignType.sign (b3_orient ℂ (b3_velocity ℂ _ (hga_dualWin W D τo τi) (1 / 2))
      (b3_velocity ℂ _ (hga_primWin W D ε) (1 / 2))) = 1 := by
  rw [hga_lift_crossing_sign U π hπ C f ι hι hιr hfι V hV t hk _ _
    (hga_dualWin_continuous hfo hfi) hga_primWin_continuous W.dualCurve W.primCurve
    W.dualCurve_contDiff W.primCurve_contDiff
    (hga_dualWin_proj (fun x ↦ f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ x)) hD hbo hbi)
    (hga_primWin_proj (fun x ↦ f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ x)) hD τe hbe hfe)
    W.dualCurve_im W.primCurve_im _ _
    ((hga_windows_meet hfo hfi).1.trans (hga_windows_meet hfo hfi).2.symm)]
  exact hga_windows_plane_sign W

end Fibre

end HodgeLean.Foundations.Program

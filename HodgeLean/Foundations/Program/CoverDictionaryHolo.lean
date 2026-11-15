import HodgeLean.Foundations.Program.CoverDictionaryLocal

/-! # B6-5 stage 5d, stage four: holomorphy of the forms on the regular locus

A function on a surface whose chart expression is analytic is holomorphic
(`caf_contMDiffAt_of_chart_analytic`); the differential of a holomorphic function is holomorphic
on the tangent bundle (`caf_contMDiffAt_mfderiv`). Hence the `s`-function is holomorphic over a
finite `s`, the pulled-back solutions are holomorphic at the regular points, and the r- and
q-forms of rational vectors regular off the poles are holomorphic over the regular locus
(`b65g_rForm_contMDiffAt`, `b65g_qForm_contMDiffAt`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Matrix Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

local notation "𝔼" => (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)

section General

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Analytic in a chart is holomorphic.** -/
theorem caf_contMDiffAt_of_chart_analytic [CompleteSpace F] (f : M → F) (x : M)
    (h : AnalyticAt ℂ (fun z ↦ f ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x)) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, F) ω f x := by
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · have hc : ContinuousAt (fun y ↦ (fun z ↦ f ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
        (extChartAt 𝓘(ℂ, ℂ) x y)) x :=
      h.continuousAt.comp (continuousAt_extChartAt x)
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) x] with y hy
    simp only [(extChartAt 𝓘(ℂ, ℂ) x).left_inv hy]
  · simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, modelWithCornersSelf_coe,
      range_id, contDiffWithinAt_univ, Function.id_comp]
    exact h.contDiffAt

variable [IsManifold 𝓘(ℂ, ℂ) ω M]

/-- **The differential of a holomorphic function is holomorphic on the tangent bundle.** -/
theorem caf_contMDiffAt_mfderiv (f : M → ℂ) (s : Set M) (hs : IsOpen s)
    (hf : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f s) (u : TangentBundle 𝓘(ℂ, ℂ) M) (hu : u.1 ∈ s) :
    ContMDiffAt 𝓘(ℂ, ℂ).tangent 𝓘(ℂ, ℂ) ω
      (fun u : TangentBundle 𝓘(ℂ, ℂ) M ↦ mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f u.1 u.2) u := by
  have hT := hf.contMDiffOn_tangentMapWithin (m := ω) (by simp) hs.uniqueMDiffOn
  have hU : Bundle.TotalSpace.proj ⁻¹' s ∈ 𝓝 u :=
    (hs.preimage (FiberBundle.continuous_proj ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := M)))).mem_nhds hu
  have h1 := ((contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℂ, ℂ)).contMDiffAt).comp u
    (hT.contMDiffAt hU)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  change _ = (mfderivWithin 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f s q.1) q.2
  rw [mfderivWithin_of_isOpen hs hq]

end General

section Fibre

variable {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
  (t : b6t_polydisc c) {a b : ℂ}

/-- The points over a finite `s` form an open set. -/
theorem b65g_finite_isOpen (a b : ℂ) :
    IsOpen {x : b65z_fibre c D.C t | b63d_projection c D.C D.atlas.f (b6t_polydisc c)
      (Subset.refl _) t x ≠ ((b / (b - a) : ℂ) : OnePoint ℂ)} :=
  isOpen_ne_fun (D.hk t).continuous continuous_const

/-- **The `s`-function is holomorphic over a finite `s`.** -/
theorem b65g_sFun_contMDiffOn (hba : b - a ≠ 0) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b65g_sFun D t a b)
      {x : b65z_fibre c D.C t | b63d_projection c D.C D.atlas.f (b6t_polydisc c)
        (Subset.refl _) t x ≠ ((b / (b - a) : ℂ) : OnePoint ℂ)} := fun x hx ↦
  (caf_contMDiffAt_of_chart_analytic _ x (b65g_sFun_chart_analytic D t hba x hx)).contMDiffWithinAt

/-- **`ds` is holomorphic on the tangent bundle over a finite `s`.** -/
theorem b65g_ds_contMDiffAt (hba : b - a ≠ 0) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t))
    (hu : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t u.1 ≠
      ((b / (b - a) : ℂ) : OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ, ℂ).tangent 𝓘(ℂ, ℂ) ω (b65g_ds D t a b) u :=
  caf_contMDiffAt_mfderiv _ _ (b65g_finite_isOpen D t a b) (b65g_sFun_contMDiffOn D t hba) u hu

/-- A regular point is over a finite `s`. -/
theorem b65g_good_finite {poles : Fin 4 ⊕ Fin 12 → ℂ} (hba : b - a ≠ 0)
    {x : b65z_fibre c D.C t} (hx : x ∈ b65g_good D t a b poles) :
    b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x ≠
      ((b / (b - a) : ℂ) : OnePoint ℂ) := by
  obtain ⟨z, hz, hz', -⟩ := hx
  rw [hz]
  intro h
  apply hz'
  have h' : z = b / (b - a) := OnePoint.coe_injective h
  rw [h', div_mul_cancel₀ _ hba, sub_self]

end Fibre

variable {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
  {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)

/-- **The pulled-back solution is analytic in charts at regular points.** -/
theorem b65g_Y_chart_analytic (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)) :
    AnalyticAt ℂ (fun z ↦ S.Y θ ((extChartAt 𝓘(ℂ, ℂ) x).symm z).val)
      (extChartAt 𝓘(ℂ, ℂ) x x) := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hgo := b65g_good_isOpen D t hab' hba (b65p_poles p θ)
  have hev : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x x), z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target ∧
      (extChartAt 𝓘(ℂ, ℂ) x).symm z ∈
        b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) := by
    have h1 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x x), z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target :=
      (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
    have h2 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x x), (extChartAt 𝓘(ℂ, ℂ) x).symm z ∈
        b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) :=
      (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) x).preimage_mem_nhds
        (by rw [extChartAt_to_inv]; exact hgo.mem_nhds hx)
    exact h1.and h2
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine DifferentiableOn.analyticAt (s := ball (extChartAt 𝓘(ℂ, ℂ) x x) r) (fun z hz ↦ ?_)
    (ball_mem_nhds _ hr)
  obtain ⟨h1, -, -⟩ := b65g_chart_ode S θ hθ t ht x z (hball z hz).1 (hball z hz).2
  exact h1.differentiableAt.differentiableWithinAt


/-- The entries of the inverse of the pulled-back solution are analytic in charts at regular
points, and so are the entries of the solution. -/
theorem b65g_Y_entries_analytic (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ))
    (i j : Fin 4) :
    AnalyticAt ℂ (fun z ↦ (b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z))⁻¹ i j)
      (extChartAt 𝓘(ℂ, ℂ) x x) ∧
    AnalyticAt ℂ (fun z ↦ b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z) i j)
      (extChartAt 𝓘(ℂ, ℂ) x x) := by
  have hY := b65g_Y_chart_analytic S θ hθ t ht x hx
  obtain ⟨w, hw⟩ := S.unit θ hθ t ht x hx
  have hinv : AnalyticAt ℂ (fun z ↦ Ring.inverse (S.Y θ ((extChartAt 𝓘(ℂ, ℂ) x).symm z).val))
      (extChartAt 𝓘(ℂ, ℂ) x x) := by
    refine (analyticAt_inverse (𝕜 := ℂ) w).comp_of_eq hY ?_
    simp only [extChartAt_to_inv, hw]
  refine ⟨?_, ?_⟩
  · refine (((b65q_entryCLM i j).analyticAt _).comp hinv).congr (Eventually.of_forall fun z ↦ ?_)
    simp only [Function.comp_apply, b65q_entryCLM_apply, b65g_Y, caf_mat_inverse]
  · refine (((b65q_entryCLM i j).analyticAt _).comp hY).congr (Eventually.of_forall fun z ↦ ?_)
    simp only [Function.comp_apply, b65q_entryCLM_apply, b65g_Y]

/-- **The r-forms are holomorphic over the regular locus.** -/
theorem b65g_rForm_contMDiffAt (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (r : Fin 4 → RatFunc ℂ)
    (hr : ∀ i s, (r i).denom.eval s = 0 → s ∈ Set.range (b65p_poles p θ)) (v : Fin 4 → ℂ)
    (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t))
    (hu : u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)) :
    ContMDiffAt 𝓘(ℂ, ℂ).tangent 𝓘(ℂ, ℂ) ω
      (b65g_rForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) r v) u := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨-, -, hab⟩ := b65g_moving_ne p O θ hθO
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set x := u.1
  have hfin := b65g_good_finite D t hba hu
  have hs := b65g_sFun_chart_analytic D t hba x hfin
  have hR : ∀ j, AnalyticAt ℂ (fun z ↦ b65q_eval (r j)
      (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) ((extChartAt 𝓘(ℂ, ℂ) x).symm z)))
      (extChartAt 𝓘(ℂ, ℂ) x x) := by
    intro j
    have hden : (r j).denom.eval (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x) ≠ 0 :=
      fun h ↦ b65g_good_sFun hu (hr j _ h)
    refine (caf_eval_analyticAt (r j) _ ?_).comp hs
    simpa only [extChartAt_to_inv] using hden
  have hf₁ : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y ↦ v ⬝ᵥ ((b65g_Y S θ t y)⁻¹ *ᵥ
      fun j ↦ b65q_eval (r j) (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) y))) x := by
    refine caf_contMDiffAt_of_chart_analytic _ x ?_
    simp only [dotProduct, Matrix.mulVec]
    have hA := fun i j ↦ (b65g_Y_entries_analytic S θ hθ t ht x hu i j).1
    refine Finset.analyticAt_fun_sum _ fun i _ ↦ analyticAt_const.mul ?_
    exact Finset.analyticAt_fun_sum _ fun j _ ↦ (hA i j).mul (hR j)
  have hf₁' := hf₁.comp u (Bundle.contMDiff_proj (TangentSpace 𝓘(ℂ, ℂ))).contMDiffAt
  exact hf₁'.mul (b65g_ds_contMDiffAt D t hba u hfin)

/-- **The q-forms are holomorphic over the regular locus.** -/
theorem b65g_qForm_contMDiffAt (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (q : Fin 4 → RatFunc ℂ)
    (hq : ∀ i s, (q i).denom.eval s = 0 → s ∈ Set.range (b65p_poles p θ)) (v : Fin 4 → ℂ)
    (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t))
    (hu : u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)) :
    ContMDiffAt 𝓘(ℂ, ℂ).tangent 𝓘(ℂ, ℂ) ω
      (b65g_qForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) q v) u := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨-, -, hab⟩ := b65g_moving_ne p O θ hθO
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set x := u.1
  have hfin := b65g_good_finite D t hba hu
  have hs := b65g_sFun_chart_analytic D t hba x hfin
  have hR : ∀ j, AnalyticAt ℂ (fun z ↦ b65q_eval (q j)
      (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) ((extChartAt 𝓘(ℂ, ℂ) x).symm z)))
      (extChartAt 𝓘(ℂ, ℂ) x x) := by
    intro j
    have hden : (q j).denom.eval (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x) ≠ 0 :=
      fun h ↦ b65g_good_sFun hu (hq j _ h)
    refine (caf_eval_analyticAt (q j) _ ?_).comp hs
    simpa only [extChartAt_to_inv] using hden
  have hf₁ : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y ↦ v ⬝ᵥ ((b65g_Y S θ t y)ᵀ *ᵥ
      fun j ↦ b65q_eval (q j) (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) y))) x := by
    refine caf_contMDiffAt_of_chart_analytic _ x ?_
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
    have hA := fun i j ↦ (b65g_Y_entries_analytic S θ hθ t ht x hu i j).2
    refine Finset.analyticAt_fun_sum _ fun i _ ↦ analyticAt_const.mul ?_
    exact Finset.analyticAt_fun_sum _ fun j _ ↦ (hA j i).mul (hR j)
  have hf₁' := hf₁.comp u (Bundle.contMDiff_proj (TangentSpace 𝓘(ℂ, ℂ))).contMDiffAt
  exact hf₁'.mul (b65g_ds_contMDiffAt D t hba u hfin)

end HodgeLean.Foundations.Program

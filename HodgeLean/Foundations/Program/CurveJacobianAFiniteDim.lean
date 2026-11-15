import HodgeLean.Foundations.Program.CurveJacobianAPlumbing

/-! # Track B3, lane A: finite dimensionality of holomorphic forms

On a compact Riemann surface, finitely many chart discs `|z| < r_i` cover the surface. The
coefficients of a form `θ` on the coordinate frames of these charts are holomorphic on the discs
`|z| < 4 r_i`; restricting them to `|z| ≤ r_i` embeds `Ω¹` injectively into a finite product of
spaces of bounded continuous functions. On a bounded set the coefficients are uniformly bounded on
`|z| ≤ 2 r_i` (the frames differ by continuous factors on compact overlaps), hence uniformly
Lipschitz on `|z| ≤ r_i` by the Cauchy estimates, so by Arzelà–Ascoli bounded sets have compact
closure, and Riesz's lemma gives finite dimension.
-/

noncomputable section

open Manifold Filter Topology Set Bundle Metric BoundedContinuousFunction
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Analysis


/-- **Cauchy estimates give a uniform Lipschitz bound**: a function holomorphic on `|z| < 4r` and
bounded by `B` on `|z| ≤ 2r` is `B / r`-Lipschitz on `|z| ≤ r`. -/
theorem b3A_lipschitz_of_bound {f : ℂ → ℂ} {r B : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball 0 (4 * r))) (hB : ∀ z ∈ closedBall (0 : ℂ) (2 * r), ‖f z‖ ≤ B)
    {z w : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) (hw : w ∈ closedBall (0 : ℂ) r) :
    ‖f z - f w‖ ≤ B / r * ‖z - w‖ := by
  have hsub : ∀ ζ ∈ closedBall (0 : ℂ) r, closedBall ζ r ⊆ closedBall 0 (2 * r) := by
    intro ζ hζ ξ hξ
    rw [mem_closedBall, dist_zero_right] at hζ ⊢
    rw [mem_closedBall, dist_eq_norm] at hξ
    calc ‖ξ‖ = ‖(ξ - ζ) + ζ‖ := by rw [sub_add_cancel]
      _ ≤ ‖ξ - ζ‖ + ‖ζ‖ := norm_add_le _ _
      _ ≤ 2 * r := by linarith
  have hsub' : closedBall (0 : ℂ) (2 * r) ⊆ ball 0 (4 * r) :=
    closedBall_subset_ball (by linarith)
  have hdiff : ∀ ζ ∈ closedBall (0 : ℂ) r, DifferentiableAt ℂ f ζ := fun ζ hζ ↦
    hf.differentiableAt (isOpen_ball.mem_nhds (hsub' (hsub ζ hζ (mem_closedBall_self hr.le))))
  have hderiv : ∀ ζ ∈ closedBall (0 : ℂ) r, ‖deriv f ζ‖ ≤ B / r := by
    intro ζ hζ
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ fun ξ hξ ↦
      hB ξ (hsub ζ hζ (sphere_subset_closedBall hξ))
    refine (hf.mono ?_).diffContOnCl_ball subset_rfl
    exact (hsub ζ hζ).trans hsub'
  have := (convex_closedBall (0 : ℂ) r).norm_image_sub_le_of_norm_deriv_le hdiff hderiv hw hz
  exact this


/-- **Riesz's criterion through an injective linear map**: if `Φ : V → N` is injective and every
`Φ`-bounded set of `V` maps into a compact subset of the normed space `N`, then `V` is
finite-dimensional. -/
theorem b3A_finiteDimensional_of_compact {V : Type*} [AddCommGroup V] [Module ℂ V]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℂ N] (Φ : V →ₗ[ℂ] N)
    (hΦ : Function.Injective Φ)
    (hK : ∀ ρ : ℝ, ∃ K : Set N, IsCompact K ∧ ∀ v, ‖Φ v‖ ≤ ρ → Φ v ∈ K) :
    FiniteDimensional ℂ V := by
  by_contra h
  have h' : ¬ FiniteDimensional ℂ (LinearMap.range Φ) := fun hr ↦
    h (Module.Finite.equiv (LinearEquiv.ofInjective Φ hΦ).symm)
  obtain ⟨R, f, -, hfR, hf⟩ := exists_seq_norm_le_one_le_norm_sub h'
  obtain ⟨K, hKc, hKm⟩ := hK R
  have hmem : ∀ n, (f n : N) ∈ K := by
    intro n
    obtain ⟨v, hv⟩ := (f n).2
    have := hKm v (by rw [hv]; exact hfR n)
    rwa [hv] at this
  obtain ⟨a, -, φ, hφ, hlim⟩ := hKc.tendsto_subseq hmem
  have hc := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hc
  obtain ⟨n₀, hn₀⟩ := hc 1 one_pos
  have h1 := hf (hφ.injective.ne (Nat.succ_ne_self n₀))
  have h2 := hn₀ (n₀ + 1) (Nat.le_succ n₀)
  rw [dist_eq_norm] at h2
  have : ‖f (φ (n₀ + 1)) - f (φ n₀)‖ = ‖(f (φ (n₀ + 1)) : N) - f (φ n₀)‖ := rfl
  simp only [Function.comp_apply] at h2
  change 1 ≤ ‖f (φ (n₀ + 1)) - f (φ n₀)‖ at h1
  linarith


/-- **Arzelà–Ascoli for finitely many compact domains**: uniformly bounded, uniformly Lipschitz
families have compact closure in the product of the spaces of bounded continuous functions. -/
theorem b3A_isCompact_lipschitz_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MetricSpace (α i)] [∀ i, CompactSpace (α i)] (B L : ℝ) :
    IsCompact (Set.pi univ fun i ↦ closure {g : α i →ᵇ ℂ |
      (∀ x, ‖g x‖ ≤ B) ∧ ∀ x y, dist (g x) (g y) ≤ L * dist x y}) := by
  refine isCompact_univ_pi fun i ↦ ?_
  refine arzela_ascoli (closedBall (0 : ℂ) B) (isCompact_closedBall 0 B) _
    (fun g x hg ↦ by simpa using hg.1 x) ?_
  have : ∀ g : {g : α i →ᵇ ℂ | (∀ x, ‖g x‖ ≤ B) ∧ ∀ x y, dist (g x) (g y) ≤ L * dist x y},
      LipschitzWith (Real.toNNReal L) (g : α i → ℂ) := fun g ↦
    LipschitzWith.of_dist_le_mul fun x y ↦ (g.2.2 x y).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) dist_nonneg)
  exact (LipschitzWith.uniformEquicontinuous _ _ this).equicontinuous

end Analysis


section Frame

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The tangent vector at `y` with coordinate `u` in the chart at `x`. -/
def b3A_frame (x : C) (u : E) (y : C) : TangentBundle 𝓘(ℂ, E) C :=
  ⟨y, (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x).symmL ℂ y u⟩

theorem b3A_frame_eq (x : C) (u : E) {y : C} (hy : y ∈ (chartAt E x).source) :
    b3A_frame x u y =
      (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x).toOpenPartialHomeomorph.symm (y, u) := by
  have hy' : y ∈ (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  rw [← Trivialization.mk_symm _ hy', b3A_frame, Trivialization.symmL_apply _ hy']

/-- The coefficient of a function on the tangent bundle on the frame of the chart at `x`. -/
def b3A_coef (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (x : C) (u : E) (y : C) : ℂ :=
  θ (b3A_frame x u y)

/-- The coefficients of a holomorphic form are holomorphic on the chart domain. -/
theorem b3A_coef_contMDiffAt {θ : TangentBundle 𝓘(ℂ, E) C → ℂ} (hθ : θ ∈ b3_HolForm E C)
    (x : C) (u : E) {y : C} (hy : y ∈ (chartAt E x).source) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (b3A_coef θ x u) y := by
  set e := trivializationAt E (TangentSpace 𝓘(ℂ, E)) x
  have hbase : e.baseSet = (chartAt E x).source := TangentBundle.trivializationAt_baseSet x
  have htarget : (y, u) ∈ e.target := by
    rw [e.target_eq, hbase]
    exact ⟨hy, mem_univ _⟩
  have h1 := (e.contMDiffOn_symm (n := ω) (IB := 𝓘(ℂ, E)) _ htarget).contMDiffAt
    (e.open_target.mem_nhds htarget)
  have h2 : ContMDiffAt 𝓘(ℂ, E) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) ω (fun y' : C ↦ (y', u)) y :=
    contMDiffAt_id.prodMk contMDiffAt_const
  have h3 := (hθ.1 _).comp y (h1.comp y h2)
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x).open_source.mem_nhds hy] with y' hy'
  simp only [b3A_coef, Function.comp_apply, b3A_frame_eq x u hy']
  rfl

/-- A tangent vector `p` at a point of the chart domain is `κ((e p).2)` times the frame vector,
for a coordinate functional `κ` of the line `E`. -/
theorem b3A_holForm_apply_eq {θ : TangentBundle 𝓘(ℂ, E) C → ℂ} (hθ : θ ∈ b3_HolForm E C)
    (κ : E →L[ℂ] ℂ) (u : E) (hκ : ∀ w : E, w = κ w • u) (x : C) (p : TangentBundle 𝓘(ℂ, E) C)
    (hp : p.1 ∈ (chartAt E x).source) :
    θ p = κ ((trivializationAt E (TangentSpace 𝓘(ℂ, E)) x p).2) * b3A_coef θ x u p.1 := by
  set e := trivializationAt E (TangentSpace 𝓘(ℂ, E)) x
  have hp' : p.1 ∈ e.baseSet := by rwa [TangentBundle.trivializationAt_baseSet]
  set c := κ (e p).2
  have hpe : p = ⟨p.1, e.symmL ℂ p.1 (c • u)⟩ := by
    rw [← hκ, Trivialization.symmL_apply _ hp']
    exact (congrArg (TotalSpace.mk p.1) (e.symm_proj_apply p hp')).symm
  rw [hpe, map_smul]
  have h := hθ.2 p.1 c (e.symmL ℂ p.1 u) 0
  have h0 := hθ.2 p.1 1 0 0
  simp only [add_zero, one_smul, one_mul] at h h0
  have hz : θ ⟨p.1, 0⟩ = 0 := by linear_combination -h0
  rw [hz, add_zero] at h
  exact h

/-- The factor between the frames of two charts. -/
def b3A_transCoef (κ : E →L[ℂ] ℂ) (x x' : C) (u : E) (y : C) : ℂ :=
  κ ((trivializationAt E (TangentSpace 𝓘(ℂ, E)) x') (b3A_frame x u y)).2

/-- The coefficients in two charts differ by the factor between the frames. -/
theorem b3A_coef_trans {θ : TangentBundle 𝓘(ℂ, E) C → ℂ} (hθ : θ ∈ b3_HolForm E C)
    (κ : E →L[ℂ] ℂ) (u : E) (hκ : ∀ w : E, w = κ w • u) (x x' : C) {y : C}
    (hy' : y ∈ (chartAt E x').source) :
    b3A_coef θ x u y = b3A_transCoef κ x x' u y * b3A_coef θ x' u y :=
  b3A_holForm_apply_eq hθ κ u hκ x' (b3A_frame x u y) hy'

/-- The factor between two frames is continuous on the overlap. -/
theorem b3A_transCoef_continuousOn (κ : E →L[ℂ] ℂ) (x x' : C) (u : E) :
    ContinuousOn (b3A_transCoef κ x x' u) ((chartAt E x).source ∩ (chartAt E x').source) := by
  set e := trivializationAt E (TangentSpace 𝓘(ℂ, E)) x
  set e' := trivializationAt E (TangentSpace 𝓘(ℂ, E)) x'
  have h1 : ContinuousOn (b3A_frame x u) (chartAt E x).source := by
    refine (e.toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_id.prodMk continuous_const).continuousOn
      fun y hy ↦ ?_).congr fun y hy ↦ b3A_frame_eq x u hy
    rw [e.target_eq, TangentBundle.trivializationAt_baseSet]
    exact ⟨hy, mem_univ _⟩
  have h2 : ContinuousOn (fun y ↦ e' (b3A_frame x u y))
      ((chartAt E x).source ∩ (chartAt E x').source) := by
    refine e'.continuousOn.comp (h1.mono inter_subset_left) fun y hy ↦ ?_
    rw [e'.mem_source, TangentBundle.trivializationAt_baseSet]
    exact hy.2
  exact κ.continuous.comp_continuousOn (continuous_snd.comp_continuousOn h2)

end Frame


section Main

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The disc parametrization `z ↦ φ_x⁻¹ (φ_x x + z u)` of a chart. -/
def b3A_disc (x : C) (u : E) (z : ℂ) : C := (chartAt E x).symm (chartAt E x x + z • u)

/-- The coefficient of a form on the disc of a chart. -/
def b3A_discCoef (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (x : C) (u : E) (z : ℂ) : ℂ :=
  b3A_coef θ x u (b3A_disc x u z)

omit [IsManifold 𝓘(ℂ, E) ω C] in
/-- The disc parametrization lands in the chart domain. -/
theorem b3A_disc_mem_source (x : C) (u : E) {z : ℂ}
    (hz : chartAt E x x + z • u ∈ (chartAt E x).target) :
    b3A_disc x u z ∈ (chartAt E x).source :=
  (chartAt E x).map_target hz

/-- The disc parametrization is holomorphic. -/
theorem b3A_disc_contMDiffAt (x : C) (u : E) {z : ℂ}
    (hz : chartAt E x x + z • u ∈ (chartAt E x).target) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω (b3A_disc x u) z := by
  have h1 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E x).symm (chartAt E x x + z • u) :=
    (contMDiffOn_chart_symm (n := ω) _ hz).contMDiffAt ((chartAt E x).open_target.mem_nhds hz)
  have h2 : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω (fun z : ℂ ↦ chartAt E x x + z • u) z :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff z
  exact h1.comp z h2

/-- The disc coefficients of a holomorphic form are holomorphic. -/
theorem b3A_discCoef_differentiableAt {θ : TangentBundle 𝓘(ℂ, E) C → ℂ}
    (hθ : θ ∈ b3_HolForm E C) (x : C) (u : E) {z : ℂ}
    (hz : chartAt E x x + z • u ∈ (chartAt E x).target) :
    DifferentiableAt ℂ (b3A_discCoef θ x u) z := by
  have := (b3A_coef_contMDiffAt hθ x u (b3A_disc_mem_source x u hz)).comp z
    (b3A_disc_contMDiffAt x u hz)
  exact mdifferentiableAt_iff_differentiableAt.1 (this.mdifferentiableAt (by simp))

/-- Disc coefficients are additive in the form. -/
theorem b3A_discCoef_add (θ η : b3_HolForm E C) (x : C) (u : E) (z : ℂ) :
    b3A_discCoef ((θ + η : b3_HolForm E C) : TangentBundle 𝓘(ℂ, E) C → ℂ) x u z =
      b3A_discCoef θ x u z + b3A_discCoef η x u z := rfl

/-- Disc coefficients are homogeneous in the form. -/
theorem b3A_discCoef_smul (c : ℂ) (θ : b3_HolForm E C) (x : C) (u : E) (z : ℂ) :
    b3A_discCoef ((c • θ : b3_HolForm E C) : TangentBundle 𝓘(ℂ, E) C → ℂ) x u z =
      c * b3A_discCoef θ x u z := rfl

/-- **Holomorphic forms on a compact surface are finite-dimensional.** -/
theorem b3A_holForm_finiteDimensional [T2Space C] [CompactSpace C]
    (hE : Module.finrank ℂ E = 1) : FiniteDimensional ℂ (b3_HolForm E C) := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  set b := Module.finBasisOfFinrankEq ℂ E hE
  set u := b 0
  set κ : E →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (b.coord 0)
  have hκ : ∀ w : E, w = κ w • u := by
    intro w
    conv_lhs => rw [← b.sum_repr w]
    simp [κ, u]
  have hu : u ≠ 0 := b.ne_zero 0
  have hR : ∀ x : C, ∃ R > 0, ∀ z : ℂ, ‖z‖ < R → chartAt E x x + z • u ∈ (chartAt E x).target := by
    intro x
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (chartAt E x).open_target (chartAt E x x)
      ((chartAt E x).map_source (mem_chart_source E x))
    refine ⟨ε / ‖u‖, div_pos hε (norm_pos_iff.2 hu), fun z hz ↦ hball ?_⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    rwa [lt_div_iff₀ (norm_pos_iff.2 hu)] at hz
  choose R hRpos hRmem using hR
  set W : C → Set C := fun x ↦ (chartAt E x).source ∩
    chartAt E x ⁻¹' {w | ‖κ (w - chartAt E x x)‖ < R x / 4}
  have hWo : ∀ x, IsOpen (W x) := fun x ↦
    (chartAt E x).continuousOn.isOpen_inter_preimage (chartAt E x).open_source
      (isOpen_lt (κ.continuous.comp (continuous_sub_right _)).norm continuous_const)
  have hWx : ∀ x, x ∈ W x := fun x ↦ ⟨mem_chart_source E x, by
    simp only [mem_preimage, mem_ofPred_eq, sub_self, map_zero, norm_zero]
    linarith [hRpos x]⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo
    (fun y _ ↦ mem_iUnion.2 ⟨y, hWx y⟩)
  have hcov : ∀ y : C, ∃ i : t, y ∈ W i := fun y ↦ by
    have := ht (mem_univ y)
    simp only [mem_iUnion] at this
    obtain ⟨i, hi, hy⟩ := this
    exact ⟨⟨i, hi⟩, hy⟩
  set r : t → ℝ := fun i ↦ R i / 4
  have hr : ∀ i, 0 < r i := fun i ↦ by simp only [r]; linarith [hRpos i]
  have htgt : ∀ (i : t) (z : ℂ), ‖z‖ < 4 * r i →
      chartAt E (i : C) (i : C) + z • u ∈ (chartAt E (i : C)).target := fun i z hz ↦
    hRmem i z (by simp only [r] at hz; linarith)
  have hrep : ∀ (i : t) (y : C), y ∈ W i →
      b3A_disc (i : C) u (κ (chartAt E (i : C) y - chartAt E (i : C) (i : C))) = y ∧
        ‖κ (chartAt E (i : C) y - chartAt E (i : C) (i : C))‖ < r i := by
    intro i y hy
    refine ⟨?_, hy.2⟩
    rw [b3A_disc, ← hκ, add_sub_cancel]
    exact (chartAt E (i : C)).left_inv hy.1
  have hdiff : ∀ (θ : b3_HolForm E C) (i : t) (z : ℂ), ‖z‖ < 4 * r i →
      DifferentiableAt ℂ (b3A_discCoef θ (i : C) u) z := fun θ i z hz ↦
    b3A_discCoef_differentiableAt θ.2 _ u (htgt i z hz)
  have hcont : ∀ (θ : b3_HolForm E C) (i : t),
      Continuous fun z : closedBall (0 : ℂ) (r i) ↦ b3A_discCoef θ (i : C) u z := by
    intro θ i
    rw [continuous_iff_continuousAt]
    intro z
    have hz : ‖(z : ℂ)‖ < 4 * r i := by
      have := mem_closedBall_zero_iff.1 z.2
      linarith [hr i]
    exact (hdiff θ i z hz).continuousAt.comp continuous_subtype_val.continuousAt
  let Φ : b3_HolForm E C →ₗ[ℂ] (∀ i : t, closedBall (0 : ℂ) (r i) →ᵇ ℂ) :=
    { toFun := fun θ i ↦ mkOfCompact ⟨_, hcont θ i⟩
      map_add' := fun θ η ↦ by
        funext i
        ext z
        simp only [mkOfCompact_apply, ContinuousMap.coe_mk, Pi.add_apply, coe_add]
        exact b3A_discCoef_add θ η _ u z
      map_smul' := fun c θ ↦ by
        funext i
        ext z
        simp only [mkOfCompact_apply, ContinuousMap.coe_mk, Pi.smul_apply, coe_smul,
          RingHom.id_apply, smul_eq_mul]
        exact b3A_discCoef_smul c θ _ u z }
  have hΦ : ∀ (θ : b3_HolForm E C) (i : t) (z : closedBall (0 : ℂ) (r i)),
      Φ θ i z = b3A_discCoef θ (i : C) u z := fun _ _ _ ↦ rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro θ hθ
    refine Subtype.ext (funext fun p ↦ ?_)
    obtain ⟨i, hi⟩ := hcov p.1
    obtain ⟨hd, hz⟩ := hrep i p.1 hi
    rw [b3A_holForm_apply_eq θ.2 κ u hκ (i : C) p hi.1, ← hd]
    have := congrFun (congrArg DFunLike.coe (congrFun hθ i))
      ⟨κ (chartAt E (i : C) p.1 - chartAt E (i : C) (i : C)), mem_closedBall_zero_iff.2 hz.le⟩
    rw [hΦ] at this
    change _ * b3A_discCoef θ (i : C) u _ = 0
    rw [this]
    simp
  have hdisc_cont : ∀ (i : t) (ρ : ℝ), ρ < 4 * r i →
      ContinuousOn (b3A_disc (i : C) u) (closedBall 0 ρ) := fun i ρ hρ z hz ↦
    (b3A_disc_contMDiffAt _ u (htgt i z (by
      have := mem_closedBall_zero_iff.1 hz
      linarith))).continuousAt.continuousWithinAt
  have hbound : ∀ i j : t, ∃ Mij : ℝ, ∀ y ∈ b3A_disc (i : C) u '' closedBall 0 (2 * r i) ∩
      b3A_disc (j : C) u '' closedBall 0 (r j), ‖b3A_transCoef κ (i : C) (j : C) u y‖ ≤ Mij := by
    intro i j
    have hK := ((isCompact_closedBall 0 (2 * r i)).image_of_continuousOn
      (hdisc_cont i _ (by linarith [hr i]))).inter
      ((isCompact_closedBall 0 (r j)).image_of_continuousOn
      (hdisc_cont j _ (by linarith [hr j])))
    refine hK.exists_bound_of_continuousOn ((b3A_transCoef_continuousOn κ _ _ u).mono ?_)
    rintro y ⟨⟨z, hz, rfl⟩, ⟨z', hz', hy⟩⟩
    refine ⟨b3A_disc_mem_source _ u (htgt i z ?_), ?_⟩
    · have := mem_closedBall_zero_iff.1 hz
      linarith [hr i]
    · rw [← hy]
      refine b3A_disc_mem_source _ u (htgt j z' ?_)
      have := mem_closedBall_zero_iff.1 hz'
      linarith [hr j]
  choose Mij hMij using hbound
  set M : ℝ := ∑ i : t, ∑ j : t, |Mij i j|
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hMle : ∀ i j, Mij i j ≤ M := fun i j ↦
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun j ↦ |Mij i j|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i ↦ ∑ j : t, |Mij i j|)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)))
  have hB : ∀ (θ : b3_HolForm E C) (i : t) (z : ℂ), z ∈ closedBall (0 : ℂ) (2 * r i) →
      ‖b3A_discCoef θ (i : C) u z‖ ≤ M * ‖Φ θ‖ := by
    intro θ i z hz
    set y := b3A_disc (i : C) u z
    obtain ⟨j, hj⟩ := hcov y
    obtain ⟨hd, hz'⟩ := hrep j y hj
    set z' := κ (chartAt E (j : C) y - chartAt E (j : C) (j : C))
    have h1 : b3A_discCoef θ (i : C) u z =
        b3A_transCoef κ (i : C) (j : C) u y * b3A_discCoef θ (j : C) u z' := by
      rw [b3A_discCoef, b3A_coef_trans θ.2 κ u hκ (i : C) (j : C) hj.1, b3A_discCoef, hd]
    have h2 : ‖b3A_discCoef θ (j : C) u z'‖ ≤ ‖Φ θ‖ := by
      have := (Φ θ j).norm_coe_le_norm ⟨z', mem_closedBall_zero_iff.2 hz'.le⟩
      rw [hΦ] at this
      exact this.trans (norm_le_pi_norm (Φ θ) j)
    have h3 : ‖b3A_transCoef κ (i : C) (j : C) u y‖ ≤ M :=
      (hMij i j y ⟨⟨z, hz, rfl⟩, ⟨z', mem_closedBall_zero_iff.2 hz'.le, hd⟩⟩).trans (hMle i j)
    rw [h1, norm_mul]
    exact mul_le_mul h3 h2 (norm_nonneg _) hM0
  refine b3A_finiteDimensional_of_compact Φ hinj fun ρ ↦ ?_
  set L : ℝ := ∑ i : t, M * |ρ| / r i
  refine ⟨_, b3A_isCompact_lipschitz_pi (α := fun i : t ↦ closedBall (0 : ℂ) (r i)) ρ L,
    fun θ hθ i _ ↦ subset_closure ⟨fun z ↦ ?_, fun z w ↦ ?_⟩⟩
  · exact ((Φ θ i).norm_coe_le_norm z).trans ((norm_le_pi_norm (Φ θ) i).trans hθ)
  · rw [hΦ, hΦ, dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    have hlip := b3A_lipschitz_of_bound (hr i) (fun ζ hζ ↦ (hdiff θ i ζ
      (mem_ball_zero_iff.1 hζ)).differentiableWithinAt) (hB θ i) z.2 w.2
    refine hlip.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : M * ‖Φ θ‖ / r i ≤ M * |ρ| / r i :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hθ.trans (le_abs_self ρ)) hM0)
        (hr i).le
    exact this.trans (Finset.single_le_sum (f := fun i ↦ M * |ρ| / r i)
      (fun j _ ↦ div_nonneg (mul_nonneg hM0 (abs_nonneg ρ)) (hr j).le) (Finset.mem_univ i))

end Main

end HodgeLean.Foundations.Program

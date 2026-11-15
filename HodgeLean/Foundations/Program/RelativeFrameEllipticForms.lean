import HodgeLean.Foundations.Program.RelativeFrameEllipticDefs

/-! # A genus-one witness: holomorphic forms and glued forms on `rfw_E`
The chart transitions of `rfw_E` are translations, so in every tangent-bundle trivialization the
fibre coordinate of a tangent vector is the vector itself, and every chart composed with a map
that is the covering map in charts has differential the identity. From these: `dz` is a
holomorphic form, every holomorphic form is a constant multiple of `dz` (genus one), and the glued
form of the kernel element `rfw_kdz` is `dz`, on `rfw_E` and on every fibre of the constant family.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The chart transitions of `rfw_E` have derivative the identity. -/
theorem rfw_fderiv_transition (x₀ x : rfw_E) (hx : x ∈ (chartAt ℂ x₀).source) :
    fderiv ℂ (chartAt ℂ x₀ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) =
      ContinuousLinearMap.id ℂ ℂ := by
  have hp : rfw_proj (chartAt ℂ x x) = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have h := rfw_chart_proj_eventually (c := Classical.choose (rfw_proj_surjective x₀))
    (z := chartAt ℂ x x) (by rw [hp]; exact hx)
  have : (chartAt ℂ x₀ ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x x)]
      fun z ↦ z + (chartAt ℂ x₀ (rfw_proj (chartAt ℂ x x)) - chartAt ℂ x x) := h
  rw [this.fderiv_eq]
  simp

/-- In every tangent-bundle trivialization of `rfw_E` the fibre coordinate is the vector itself. -/
theorem rfw_triv_snd (x₀ : rfw_E) (p : TangentBundle 𝓘(ℂ, ℂ) rfw_E)
    (hp : p.1 ∈ (chartAt ℂ x₀).source) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) x₀ p).2 = p.2 := by
  rw [TangentBundle.trivializationAt_apply]
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, fderivWithin_univ,
    CompTriple.comp_eq]
  rw [rfw_fderiv_transition x₀ p.1 hp]
  rfl

/-- `dz` is a holomorphic form on `rfw_E`. -/
theorem rfw_dz_mem : rfw_dz ∈ b3_HolForm ℂ rfw_E := by
  refine ⟨fun p ↦ ?_, fun x a v w ↦ rfl⟩
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) p.1
  have hp : p ∈ e.source := by
    rw [TangentBundle.trivializationAt_source]
    exact mem_chart_source ℂ p.proj
  have h1 := (e.contMDiffOn (n := ω) (IB := 𝓘(ℂ, ℂ)) p hp).contMDiffAt
    (e.open_source.mem_nhds hp)
  have h2 : ContMDiff (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)) 𝓘(ℂ, ℂ) ω (fun q : rfw_E × ℂ ↦ q.2) :=
    contMDiff_snd
  refine ((h2 _).comp p h1).congr_of_eventuallyEq ?_
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  rw [TangentBundle.trivializationAt_source] at hq
  simp only [Function.comp_apply, rfw_dz, e, rfw_triv_snd p.1 q hq]
  rfl

/-- The constant section `x ↦ (x, c)` of the tangent bundle of `rfw_E` is holomorphic. -/
theorem rfw_constSection_contMDiff (c : ℂ) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ).tangent ω
      (fun x : rfw_E ↦ (⟨x, c⟩ : TangentBundle 𝓘(ℂ, ℂ) rfw_E)) := by
  intro x₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_id, (contMDiffAt_const (c := c)).congr_of_eventuallyEq ?_⟩
  filter_upwards [(chartAt ℂ x₀).open_source.mem_nhds (mem_chart_source _ x₀)] with x hx
  exact rfw_triv_snd x₀ ⟨x, c⟩ hx

/-- Every holomorphic form on `rfw_E` is `θ(0, 1) dz`: `x ↦ θ (x, v)` is holomorphic on a compact
connected surface, hence constant, and `θ` is linear on the fibres. -/
theorem rfw_form_apply (θ : TangentBundle 𝓘(ℂ, ℂ) rfw_E → ℂ) (hθ : θ ∈ b3_HolForm ℂ rfw_E)
    (x : rfw_E) (v : ℂ) : θ ⟨x, v⟩ = θ ⟨0, (1 : ℂ)⟩ * v := by
  have hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y : rfw_E ↦ θ ⟨y, v⟩) :=
    hθ.1.comp (rfw_constSection_contMDiff v)
  have hc : θ ⟨x, v⟩ = θ ⟨0, v⟩ :=
    (hf.mdifferentiable (by simp)).apply_eq_of_compactSpace x 0
  let f : ℂ → ℂ := fun w ↦ θ ⟨0, w⟩
  have h0 : f ((1 : ℂ) • (0 : ℂ) + 0) = 1 * f 0 + f 0 := hθ.2 0 1 (0 : ℂ) (0 : ℂ)
  have h1 : f (v • (1 : ℂ) + 0) = v * f 1 + f 0 := hθ.2 0 v (1 : ℂ) (0 : ℂ)
  simp only [add_zero, one_mul, smul_eq_mul, mul_one] at h0 h1
  have hz : f 0 = 0 := left_eq_add.mp h0
  refine hc.trans ?_
  change f v = f 1 * v
  rw [h1, hz, add_zero, mul_comm]

/-- `dz` as an element of `b3_HolForm ℂ rfw_E`. -/
def rfw_dzHol : b3_HolForm ℂ rfw_E := ⟨rfw_dz, rfw_dz_mem⟩

theorem rfw_dzHol_ne_zero : rfw_dzHol ≠ 0 := by
  intro h
  have := congrArg (fun θ : b3_HolForm ℂ rfw_E ↦
    (θ : TangentBundle 𝓘(ℂ, ℂ) rfw_E → ℂ) ⟨0, (1 : ℂ)⟩) h
  exact one_ne_zero this

/-- Genus one: the holomorphic forms of `rfw_E` are the multiples of `dz`. -/
theorem rfw_finrank_holForm : Module.finrank ℂ (b3_HolForm ℂ rfw_E) = 1 := by
  refine (finrank_eq_one_iff_of_nonzero' rfw_dzHol rfw_dzHol_ne_zero).mpr fun θ ↦
    ⟨(θ : TangentBundle 𝓘(ℂ, ℂ) rfw_E → ℂ) ⟨0, (1 : ℂ)⟩, ?_⟩
  apply Subtype.ext
  funext q
  exact (rfw_form_apply θ θ.2 q.1 q.2).symm

/-- A chart of `rfw_E` composed with a map that is the covering map in the charts of `X` has
differential the identity: in charts it is a translation. -/
theorem rfw_hasMFDerivAt_chart {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : X → rfw_E) (hg : Continuous g)
    (hgc : ∀ (x : X) (z : ℂ), g ((chartAt ℂ x).symm z) = rfw_proj z)
    (c : ℂ) (x : X) (hx : g x ∈ (rfw_chart c).source) :
    HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun p ↦ rfw_chart c (g p)) x (ContinuousLinearMap.id ℂ ℂ) := by
  refine ⟨((rfw_chart c).continuousAt hx).comp hg.continuousAt, ?_⟩
  have hp : rfw_proj (chartAt ℂ x x) = g x := by
    rw [← hgc x, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have h := rfw_chart_proj_eventually (c := c) (z := chartAt ℂ x x) (by rw [hp]; exact hx)
  have heq : writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x (fun p ↦ rfw_chart c (g p)) =ᶠ[𝓝 (chartAt ℂ x x)]
      fun z ↦ z + (rfw_chart c (rfw_proj (chartAt ℂ x x)) - chartAt ℂ x x) := by
    filter_upwards [h] with z hz
    simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_apply, chartAt_self_eq,
      OpenPartialHomeomorph.refl_apply, id_eq, CompTriple.comp_eq, hgc]
    exact hz
  have hd : HasFDerivAt (fun z ↦ z + (rfw_chart c (rfw_proj (chartAt ℂ x x)) - chartAt ℂ x x))
      (ContinuousLinearMap.id ℂ ℂ) (chartAt ℂ x x) :=
    (hasFDerivAt_id _).add_const _
  have := (hd.congr_of_eventuallyEq heq).hasFDerivWithinAt (s := range 𝓘(ℂ, ℂ))
  convert this using 1
  · ext
    rfl
  · rfl

/-- The differential of a chart of `rfw_E` composed with a map that is the covering map in the
charts of `X` is the identity. -/
theorem rfw_mfderiv_chart {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : X → rfw_E) (hg : Continuous g)
    (hgc : ∀ (x : X) (z : ℂ), g ((chartAt ℂ x).symm z) = rfw_proj z)
    (c : ℂ) (x : X) (hx : g x ∈ (rfw_chart c).source) (v : TangentSpace 𝓘(ℂ, ℂ) x) :
    (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun p ↦ rfw_chart c (g p)) x v) = v := by
  rw [(rfw_hasMFDerivAt_chart g hg hgc c x hx).mfderiv]
  rfl

/-- A point of the outer region lies in some piece of the outer cover, in its chart. -/
theorem rfw_mem_piece_of_mem_O {p : rfw_E} (hp : p ∈ rfw_O) :
    ∃ i, p ∈ (rfw_outer.P.chart i).source ∧ rfw_outer.P.chart i p ∈ rfw_outer.P.piece i := by
  rw [rfw_outer.P.covers] at hp
  obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hp
  have ht : z ∈ (rfw_outer.P.chart i).target := rfw_outer.P.contained i (subset_closure hz)
  exact ⟨i, (rfw_outer.P.chart i).map_target ht, by rwa [(rfw_outer.P.chart i).right_inv ht]⟩

/-- **The glued form of `rfw_kdz` is the tangent coordinate** on every plumbed surface over
`rfw_outer` with `ε = 0` whose identification is the covering map in charts and whose disc chart is
`rfw_chart 0` through the identification: on a piece the coefficient is `1` and the chart
differential is the identity, and on the inner piece the sector coefficient is `1 · g₀ = 1`. -/
theorem rfw_glue_kdz_eq {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (S : rf4_Plumbing rfw_outer (fun _ ↦ 0) X)
    (hgc : ∀ (x : X) (z : ℂ), S.h.symm ((chartAt ℂ x).symm z) = rfw_proj z)
    (hw : ∀ i, (S.w i : X → ℂ) = fun p ↦ rfw_chart 0 (S.h.symm p))
    (hws : ∀ i p, p ∈ (S.w i).source → S.h.symm p ∈ (rfw_chart 0).source) :
    rf4_glue S rfw_kdz = fun q ↦ (q.2 : ℂ) := by
  funext q
  unfold rf4_glue
  split_ifs with hO hD
  · have hspec := Classical.choose_spec hO
    generalize Classical.choose hO = i at hspec ⊢
    have h1 : rf4_extendBdd (rfw_kdz.1.val i) (rfw_outer.P.chart i (S.h.symm q.1)) = 1 := by
      simp only [rf4_extendBdd, hspec.2, ↓reduceDIte]
      rfl
    rw [h1, one_mul]
    exact rfw_mfderiv_chart S.h.symm S.h.symm.continuous hgc (rfw_cen i) q.1 hspec.1 q.2
  · have hspec := Classical.choose_spec hD
    generalize Classical.choose hD = x at hspec ⊢
    have hb : rfw_outer.c x + 0 + S.w x q.1 ^ 1 ∈ Metric.ball (0 : ℂ) (2 * (1 / 5)) := by
      have := hspec.2
      change ‖S.w x q.1 ^ 1 + 0‖ < 2 * (1 / 5) at this
      rw [mem_ball_zero_iff]
      change ‖0 + 0 + S.w x q.1 ^ 1‖ < 2 * (1 / 5)
      simpa using this
    have h1 : rf4_sectorCoeff (rfw_outer.deg x) (fun j ↦ rf4_extendBdd (rfw_kdz.2 x j))
        (rfw_outer.c x + 0) (S.w x q.1) = 1 := by
      change ((1 : ℕ) : ℂ) * ∑ j : Fin 1, S.w x q.1 ^ (j : ℕ) *
        rf4_extendBdd (rfw_one (Metric.ball (0 : ℂ) (2 * (1 / 5))))
          (rfw_outer.c x + 0 + S.w x q.1 ^ 1) = 1
      simp only [Nat.cast_one, Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul, rf4_extendBdd,
        hb, ↓reduceDIte]
      rfl
    rw [h1, one_mul, hw x]
    exact rfw_mfderiv_chart S.h.symm S.h.symm.continuous hgc 0 q.1 (hws x q.1 hspec.1) q.2
  · exfalso
    rcases S.cover q.1 with h | ⟨x, v, hv, hve⟩
    · exact hO (rfw_mem_piece_of_mem_O h)
    · have hs : q.1 ∈ (S.w x).source := hve ▸ (S.w x).map_target (S.w_target x (subset_closure hv))
      refine hD ⟨x, hs, ?_⟩
      rw [← hve, (S.w x).right_inv (S.w_target x (subset_closure hv))]
      exact hv

/-- The glued form of `rfw_kdz` on `rfw_E` is `dz`. -/
theorem rfw_glue_kdz_rfw : rf4_glue rfw_plumbing rfw_kdz = rfw_dz :=
  rfw_glue_kdz_eq rfw_plumbing (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ h ↦ h)

/-- The glued form of `rfw_kdz` on the fibre at `t` is the fibre's `dz`. -/
theorem rfw_fibre_glue_kdz_rfw (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    rf4_glue (rfw_plumbingAt b t) rfw_kdz = rfw_fibreDz b t := by
  refine rfw_glue_kdz_eq (rfw_plumbingAt b t) (fun y z ↦ ?_) (fun _ ↦ rfl) (fun _ p hp ↦ hp.2)
  exact (b6m_coordinate b rfw_E t).apply_symm_apply (rfw_proj z)

end HodgeLean.Foundations.Program

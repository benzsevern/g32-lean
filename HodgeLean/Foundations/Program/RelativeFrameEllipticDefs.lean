import HodgeLean.Foundations.Program.RelativeFrameCharts
import HodgeLean.Foundations.Program.CurveJacobianAElliptic

/-! # A genus-one witness for relative-frame stages C and C12: definitions
The elliptic curve `ℂ ⧸ (ℤ + iℤ)` of track B3 (`b3_Elliptic`, modelled on `Fin 1 → ℂ`) recharted
on `ℂ` itself: the covering map `z ↦ [z e₀]`, its local inverses on discs of radius `1/2` as
charts, translation transitions. On it: outer data with one disc of degree one around `[0]`, an
annulus piece and a finite cover of the outer region; the constant plumbing datum with `ε = 0`;
the kernel element of `dz`; the form `dz`; and the constant family over the polydisc with the
product total space.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction TensorProduct
namespace HodgeLean.Foundations.Program

/-! ## The elliptic curve charted on `ℂ` -/

/-- The elliptic curve `ℂ ⧸ (ℤ + iℤ)` of track B3, as a type to be charted on `ℂ`.
Source: `b3_Elliptic` (`CurveJacobianDefs.lean`); Forster, *Lectures on Riemann Surfaces*, §21. -/
def rfw_E : Type := b3_Elliptic

/-- The quotient topology of `b3_Elliptic`. Source: `b2_torus`. -/
instance rfw_E_top : TopologicalSpace rfw_E := inferInstanceAs (TopologicalSpace b3_Elliptic)
/-- The group law of `b3_Elliptic`. Source: `b2_torus`. -/
instance rfw_E_group : AddCommGroup rfw_E := inferInstanceAs (AddCommGroup b3_Elliptic)
/-- `rfw_E` is compact. Source: `b3_elliptic_compactSpace`. -/
instance rfw_E_compact : CompactSpace rfw_E := inferInstanceAs (CompactSpace b3_Elliptic)
/-- `rfw_E` is Hausdorff. Source: `b3_elliptic_t2Space`. -/
instance rfw_E_t2 : T2Space rfw_E := inferInstanceAs (T2Space b3_Elliptic)
/-- `rfw_E` is connected. Source: `b3A_elliptic_connected`. -/
instance rfw_E_connected : ConnectedSpace rfw_E := inferInstanceAs (ConnectedSpace b3_Elliptic)

example : rfw_E = b3_Elliptic := rfl

/-- Every class of `(ℂ ⊗ ℤ²) ⧸ F` is `φ(v) e₀`: the quotient is a complex line. -/
theorem rfw_eq_smul_e0 (v : (ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) : v = b3A_φ v • b3A_e 0 := by
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (b3A_e 0) b3A_e0_ne_zero).mp
    b3A_finrank_quot v
  rw [← ha, map_smul, b3A_φ_e0, smul_eq_mul, mul_one]

/-- `z ↦ z e₀` is a homeomorphism onto `(ℂ ⊗ ℤ²) ⧸ F`, with inverse `b3A_φ`.
Source: Bourbaki, *Espaces vectoriels topologiques*, ch. I, §2.3; `b3A_φ`, `b3A_finrank_quot`. -/
def rfw_lineHomeo : ℂ ≃ₜ ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) where
  toFun z := z • b3A_e 0
  invFun := b3A_φ
  left_inv z := by simp [b3A_φ_e0]
  right_inv v := (rfw_eq_smul_e0 v).symm
  continuous_toFun := by fun_prop
  continuous_invFun := IsModuleTopology.continuous_of_linearMap b3A_φ

example : rfw_lineHomeo 1 = b3A_e 0 := one_smul ℂ (b3A_e 0)

/-- The covering map `z ↦ [z e₀]`, in the coordinate `z` of `b3A_φ`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §1.1; `b3A_e`, `b3A_φ`. -/
def rfw_proj : ℂ →+ rfw_E where
  toFun z := (QuotientAddGroup.mk (z • b3A_e 0) : b3_Elliptic)
  map_zero' := by simp; rfl
  map_add' z z' := by rw [add_smul]; rfl

example : rfw_proj 0 = 0 := map_zero _

theorem rfw_proj_apply (z : ℂ) :
    rfw_proj z = (QuotientAddGroup.mk (z • b3A_e 0) : b3_Elliptic) := rfl

/-- The fibres of the covering map are the cosets of `ℤ + iℤ`. -/
theorem rfw_proj_eq_iff (z z' : ℂ) :
    rfw_proj z = rfw_proj z' ↔ ∃ m n : ℤ, z' - z = m + n * Complex.I := by
  change (QuotientAddGroup.mk (z • b3A_e 0) : b3_Elliptic) = QuotientAddGroup.mk (z' • b3A_e 0) ↔ _
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x 0, x 1, ?_⟩
    have h := congrArg b3A_φ hx
    rw [b3A_φ_latticeMap] at h
    simp only [map_add, map_neg, map_smul, b3A_φ_e0, smul_eq_mul, mul_one] at h
    rw [mul_comm]
    linear_combination -h
  · rintro ⟨m, n, h⟩
    refine ⟨![m, n], ?_⟩
    rw [rfw_eq_smul_e0 (b2_latticeMap _ b2_stdF ![m, n]), b3A_φ_latticeMap, ← neg_smul, ← add_smul]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination -h

/-- Nonzero points of `ℤ + iℤ` have norm at least one. -/
theorem rfw_lattice_norm {m n : ℤ} (h : (m : ℂ) + n * Complex.I ≠ 0) :
    1 ≤ ‖(m : ℂ) + n * Complex.I‖ := by
  have hmn : m ≠ 0 ∨ n ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (by simp [hc.1, hc.2])
  have hsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
    rcases hmn with hm | hn
    · have : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
        have h0 : (0 : ℤ) < m ^ 2 := by positivity
        exact_mod_cast (show (1 : ℤ) ≤ m ^ 2 by omega)
      nlinarith
    · have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have h0 : (0 : ℤ) < n ^ 2 := by positivity
        exact_mod_cast (show (1 : ℤ) ≤ n ^ 2 by omega)
      nlinarith
  have hn2 : ‖(m : ℂ) + n * Complex.I‖ ^ 2 = (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  nlinarith [norm_nonneg ((m : ℂ) + n * Complex.I)]

/-- The covering map is injective on discs of radius `1/2`. -/
theorem rfw_proj_injOn (c : ℂ) : InjOn rfw_proj (Metric.ball c (1 / 2)) := by
  intro z hz z' hz' h
  obtain ⟨m, n, hmn⟩ := (rfw_proj_eq_iff z z').mp h
  by_contra hne
  have h0 : (m : ℂ) + n * Complex.I ≠ 0 := by
    rw [← hmn]; exact sub_ne_zero.mpr (Ne.symm hne)
  have h1 := rfw_lattice_norm h0
  rw [← hmn] at h1
  have : ‖z' - z‖ < 1 := by
    calc ‖z' - z‖ ≤ ‖z' - c‖ + ‖z - c‖ := by
          rw [show z' - z = (z' - c) - (z - c) by ring]; exact norm_sub_le _ _
      _ < 1 / 2 + 1 / 2 := add_lt_add (mem_ball_iff_norm.mp hz') (mem_ball_iff_norm.mp hz)
      _ = 1 := by norm_num
  linarith

/-- The covering map is continuous. -/
theorem rfw_proj_continuous : Continuous rfw_proj :=
  show Continuous ((QuotientAddGroup.mk : _ → b3_Elliptic) ∘ rfw_lineHomeo) from
    continuous_quot_mk.comp rfw_lineHomeo.continuous

/-- The covering map is open. -/
theorem rfw_proj_isOpenMap : IsOpenMap rfw_proj :=
  show IsOpenMap ((QuotientAddGroup.mk : _ → b3_Elliptic) ∘ rfw_lineHomeo) from
    (QuotientAddGroup.isOpenMap_coe).comp rfw_lineHomeo.isOpenMap

/-- The covering map is surjective. -/
theorem rfw_proj_surjective : Function.Surjective rfw_proj := by
  intro p
  induction p using QuotientAddGroup.induction_on with
  | H v => exact ⟨b3A_φ v, by rw [rfw_proj_apply, ← rfw_eq_smul_e0]⟩

/-- The covering map restricted to the disc `D(c, 1/2)`, as a partial homeomorphism.
Source: Mathlib `Set.InjOn.toPartialEquiv`, `OpenPartialHomeomorph.ofContinuousOpen`. -/
def rfw_projLocal (c : ℂ) : OpenPartialHomeomorph ℂ rfw_E :=
  OpenPartialHomeomorph.ofContinuousOpen
    ((rfw_proj_injOn c).toPartialEquiv rfw_proj (Metric.ball c (1 / 2)))
    rfw_proj_continuous.continuousOn rfw_proj_isOpenMap Metric.isOpen_ball

example (c z : ℂ) : rfw_projLocal c z = rfw_proj z := rfl

/-- **The chart of `rfw_E` centred at `c`**: the inverse of the covering map on `D(c, 1/2)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §1.1 (charts of `V ⧸ Λ` from `V`). -/
def rfw_chart (c : ℂ) : OpenPartialHomeomorph rfw_E ℂ := (rfw_projLocal c).symm

@[simp] theorem rfw_chart_symm_apply (c z : ℂ) : (rfw_chart c).symm z = rfw_proj z := rfl

@[simp] theorem rfw_chart_target (c : ℂ) : (rfw_chart c).target = Metric.ball c (1 / 2) := rfl

theorem rfw_chart_source (c : ℂ) : (rfw_chart c).source = rfw_proj '' Metric.ball c (1 / 2) :=
  rfl

theorem rfw_chart_proj {c z : ℂ} (hz : z ∈ Metric.ball c (1 / 2)) : rfw_chart c (rfw_proj z) = z :=
  (rfw_chart c).right_inv (x := z) hz

example : rfw_chart 0 (rfw_proj 0) = 0 := rfw_chart_proj (by simp)

theorem rfw_proj_mem_source {c z : ℂ} (hz : z ∈ Metric.ball c (1 / 2)) :
    rfw_proj z ∈ (rfw_chart c).source := ⟨z, hz, rfl⟩

/-- Near a point of an overlap, a chart composed with the covering map is a translation. -/
theorem rfw_chart_proj_eventually {c z : ℂ} (hz : rfw_proj z ∈ (rfw_chart c).source) :
    ∀ᶠ z' in 𝓝 z, rfw_chart c (rfw_proj z') = z' + (rfw_chart c (rfw_proj z) - z) := by
  set w := rfw_chart c (rfw_proj z)
  have hw : w ∈ Metric.ball c (1 / 2) := (rfw_chart c).map_source hz
  have hpw : rfw_proj w = rfw_proj z := (rfw_chart c).left_inv hz
  have hcont : Continuous fun z' : ℂ ↦ z' + (w - z) := continuous_id.add continuous_const
  have hmem : (fun z' : ℂ ↦ z' + (w - z)) ⁻¹' Metric.ball c (1 / 2) ∈ 𝓝 z :=
    hcont.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by simpa using hw))
  filter_upwards [hmem] with z' hz'
  have hp : rfw_proj (z' + (w - z)) = rfw_proj z' := by
    rw [map_add, map_sub, hpw, sub_self, add_zero]
  rw [← hp, rfw_chart_proj hz']

/-- The charted space of `rfw_E` over `ℂ`: the charts `rfw_chart c`, `c ∈ ℂ`; the chart at a point
is centred at a chosen preimage.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §1.1; Mathlib `ChartedSpace`. -/
instance rfw_charted : ChartedSpace ℂ rfw_E where
  atlas := range rfw_chart
  chartAt p := rfw_chart (Classical.choose (rfw_proj_surjective p))
  mem_chart_source p := by
    have h := Classical.choose_spec (rfw_proj_surjective p)
    exact ⟨_, Metric.mem_ball_self (by norm_num), h⟩
  chart_mem_atlas p := mem_range_self _

example (c : ℂ) : rfw_chart c ∈ atlas ℂ rfw_E := mem_range_self c

/-- The chart transitions are holomorphic, being translations near each point. -/
theorem rfw_transition_contDiffOn (c c' : ℂ) :
    ContDiffOn ℂ ω (rfw_chart c' ∘ (rfw_chart c).symm)
      ((rfw_chart c).symm ≫ₕ rfw_chart c').source := by
  intro z hz
  have hz' : rfw_proj z ∈ (rfw_chart c').source := hz.2
  refine ContDiffAt.contDiffWithinAt ?_
  refine (contDiff_id.add (contDiff_const (c := rfw_chart c' (rfw_proj z) - z))).contDiffAt
    |>.congr_of_eventuallyEq ?_
  filter_upwards [rfw_chart_proj_eventually hz'] with z' h
  simpa using h

/-- `rfw_E` is a Riemann surface.
Source: the transitions are translations, `rfw_transition_contDiffOn`. -/
instance rfw_isManifold : IsManifold 𝓘(ℂ, ℂ) ω rfw_E := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
  simpa using rfw_transition_contDiffOn c c'

theorem rfw_chart_mem (c : ℂ) : rfw_chart c ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω rfw_E :=
  IsManifold.subset_maximalAtlas (mem_range_self c)

/-- The derivative of every transition at an overlap point is one. -/
theorem rfw_deriv_transition {c c' z : ℂ} (hz : rfw_proj z ∈ (rfw_chart c').source) :
    deriv (rfw_chart c' ∘ (rfw_chart c).symm) z = 1 := by
  have : (rfw_chart c' ∘ (rfw_chart c).symm) =ᶠ[𝓝 z]
      fun z' ↦ z' + (rfw_chart c' (rfw_proj z) - z) := by
    filter_upwards [rfw_chart_proj_eventually hz] with z' h
    simpa using h
  rw [this.deriv_eq]
  simp

/-! ## Outer data, the plumbing datum and the kernel element of `dz` -/

/-- The outer region `O = rfw_E ∖ [D̄(0, 1/5)]`, the complement of the image of the compact
coordinate disc around `[0]`.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 (outer piece). -/
def rfw_O : Set rfw_E := (rfw_proj '' Metric.closedBall 0 (1 / 5))ᶜ

example : rfw_O = (rfw_proj '' Metric.closedBall 0 (1 / 5))ᶜ := rfl

theorem rfw_proj_zero_not_mem_O : rfw_proj 0 ∉ rfw_O :=
  fun h ↦ h ⟨0, by simp, rfl⟩

theorem rfw_O_isOpen : IsOpen rfw_O :=
  ((isCompact_closedBall (0 : ℂ) (1 / 5)).image rfw_proj_continuous).isClosed.isOpen_compl

/-- The annulus `{1/5 < |u| < 2/5}` lies in the outer region. -/
theorem rfw_annulus_mem_O {u : ℂ} (hu : u ∈ b63r_annulus 1 (1 / 5)) : rfw_proj u ∈ rfw_O := by
  rintro ⟨z, hz, hzu⟩
  have hu1 : 1 / 5 < ‖u‖ := by simpa using hu.1
  have hu2 : ‖u‖ < 2 / 5 := by have := hu.2; norm_num at this; linarith
  have hz' : ‖z‖ ≤ 1 / 5 := by simpa using hz
  have := rfw_proj_injOn 0 (show z ∈ Metric.ball (0 : ℂ) (1 / 2) by
    rw [mem_ball_zero_iff]; linarith) (show u ∈ Metric.ball (0 : ℂ) (1 / 2) by
    rw [mem_ball_zero_iff]; linarith) hzu
  subst this
  linarith

/-- The discs `D(c, 2/5)`, `c ∈ ℂ`, cover `rfw_E` by finitely many of their images. -/
theorem rfw_finite_cover :
    ∃ t : Finset ℂ, univ ⊆ ⋃ c ∈ t, rfw_proj '' Metric.ball c (2 / 5) :=
  isCompact_univ.elim_finite_subcover (fun c : ℂ ↦ rfw_proj '' Metric.ball c (2 / 5))
    (fun _ ↦ rfw_proj_isOpenMap _ Metric.isOpen_ball)
    (fun p _ ↦ mem_iUnion.2 ⟨Classical.choose (rfw_proj_surjective p),
      ⟨_, Metric.mem_ball_self (by norm_num), Classical.choose_spec (rfw_proj_surjective p)⟩⟩)

/-- A finite set of centres whose discs of radius `2/5` cover `rfw_E`.
Source: compactness of `rfw_E`; Mathlib `IsCompact.elim_finite_subcover`. -/
def rfw_centres : Finset ℂ := Classical.choose rfw_finite_cover

example : univ ⊆ ⋃ c ∈ rfw_centres, rfw_proj '' Metric.ball c (2 / 5) :=
  Classical.choose_spec rfw_finite_cover

/-- The `k`-th centre.
Source: `rfw_centres`; Mathlib `Finset.equivFin`. -/
def rfw_centre (k : Fin rfw_centres.card) : ℂ := (rfw_centres.equivFin.symm k : ℂ)

example (k : Fin rfw_centres.card) : rfw_centre k ∈ rfw_centres := (rfw_centres.equivFin.symm k).2

theorem rfw_centre_cover (p : rfw_E) :
    ∃ k z, z ∈ Metric.ball (rfw_centre k) (2 / 5) ∧ rfw_proj z = p := by
  have h := Classical.choose_spec rfw_finite_cover (mem_univ p)
  obtain ⟨c, hc, z, hz, rfl⟩ := mem_iUnion₂.mp h
  refine ⟨rfw_centres.equivFin ⟨c, hc⟩, z, ?_, rfl⟩
  simpa [rfw_centre] using hz

/-- The chart centres of the pieces: `0` for the annulus piece, then the covering centres.
Source: `rfw_centre`. -/
def rfw_cen : Fin (rfw_centres.card + 1) → ℂ := Fin.cases 0 rfw_centre

example : rfw_cen 0 = 0 := rfl

/-- The pieces of the outer cover: the annulus `A₁ = {1/5 < |u| < 2/5}` in the chart at `0`, and in
the chart at each covering centre `c` the part of `D(c, 2/5)` over the outer region.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 and §5, A13. -/
def rfw_piece : Fin (rfw_centres.card + 1) → Set ℂ :=
  Fin.cases (b63r_annulus 1 (1 / 5))
    (fun k ↦ Metric.ball (rfw_centre k) (2 / 5) ∩ rfw_proj ⁻¹' rfw_O)

example : rfw_piece 0 = b63r_annulus 1 (1 / 5) := rfl

theorem rfw_closedAnnulus_subset : rf4_closedAnnulus 1 (1 / 5) ⊆ Metric.ball 0 (1 / 2) := by
  intro u hu
  have := hu.2
  rw [mem_ball_zero_iff]
  norm_num at this ⊢
  linarith

theorem rfw_piece_closure (i : Fin (rfw_centres.card + 1)) :
    IsCompact (closure (rfw_piece i)) ∧
      closure (rfw_piece i) ⊆ Metric.ball (rfw_cen i) (1 / 2) := by
  induction i using Fin.cases with
  | zero =>
    refine ⟨(rf4_closedAnnulus_isCompact le_rfl _).closure_of_subset
      (rf4_annulus_subset_closed 1 _), ?_⟩
    exact (closure_minimal (rf4_annulus_subset_closed 1 _)
      (rf4_closedAnnulus_isCompact le_rfl _).isClosed).trans rfw_closedAnnulus_subset
  | succ k =>
    have hs : rfw_piece k.succ ⊆ Metric.closedBall (rfw_centre k) (2 / 5) :=
      inter_subset_left.trans Metric.ball_subset_closedBall
    refine ⟨(isCompact_closedBall _ _).closure_of_subset hs, ?_⟩
    refine (closure_minimal hs Metric.isClosed_closedBall).trans ?_
    exact Metric.closedBall_subset_ball (by norm_num)

theorem rfw_piece_subset (i : Fin (rfw_centres.card + 1)) :
    rfw_piece i ⊆ Metric.ball (rfw_cen i) (1 / 2) :=
  subset_closure.trans (rfw_piece_closure i).2

/-- The finite piece cover of the outer region: the annulus piece and one piece per covering
centre, all in charts `rfw_chart c`.
Source: Forster, *Lectures on Riemann Surfaces*, §2; RelativeFrame §5, A13; `rf2_PieceCover`. -/
def rfw_cover : rf2_PieceCover rfw_E rfw_O where
  n := rfw_centres.card + 1
  chart i := rfw_chart (rfw_cen i)
  analytic i := rfw_chart_mem _
  piece := rfw_piece
  isOpen i := by
    induction i using Fin.cases with
    | zero => exact rf4_annulus_isOpen 1 _
    | succ k => exact Metric.isOpen_ball.inter (rfw_O_isOpen.preimage rfw_proj_continuous)
  compact i := (rfw_piece_closure i).1
  contained i := (rfw_piece_closure i).2
  covers := by
    ext p
    simp only [mem_iUnion, rfw_chart_symm_apply]
    constructor
    · intro hp
      obtain ⟨k, z, hz, rfl⟩ := rfw_centre_cover p
      exact ⟨k.succ, z, ⟨hz, hp⟩, rfl⟩
    · rintro ⟨i, z, hz, rfl⟩
      induction i using Fin.cases with
      | zero => exact rfw_annulus_mem_O hz
      | succ k => exact hz.2

example : rfw_cover.chart (0 : Fin (rfw_centres.card + 1)) = rfw_chart 0 := rfl

/-- Outer data on `rfw_E`: the piece cover above, radius `1/5`, one disc of degree one with base
value `0`, whose annulus piece is the piece `0`.
Source: RelativeFrame §4.1–4.2; `rf4_OuterData`. -/
def rfw_outer : rf4_OuterData rfw_E rfw_O where
  P := rfw_cover
  r := 1 / 5
  hr := by norm_num
  m := 1
  deg := fun _ ↦ 1
  hdeg := fun _ ↦ le_rfl
  c := fun _ ↦ 0
  ann := fun _ ↦ (0 : Fin (rfw_centres.card + 1))
  hann := fun _ ↦ rfl

example : rfw_outer.m = 1 ∧ rfw_outer.r = 1 / 5 := ⟨rfl, rfl⟩

theorem rfw_innerDisc_eq : rf4_innerDisc 1 (1 / 5) 0 = Metric.ball 0 (2 / 5) := by
  ext w
  simp only [rf4_innerDisc, pow_one, add_zero, mem_ofPred_eq, mem_ball_zero_iff]
  norm_num

/-- **The constant plumbing datum** of `rfw_E` over `rfw_outer` with `ε = 0`: the identification
is the identity, the disc chart is `rfw_chart 0`, the inner piece is `[D(0, 2/5)]`, and the gluing
`Φ₀(u) = u` is the identity on the annulus.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 (B5–B10 at `ε = 0`); `rf4_Plumbing`. -/
def rfw_plumbing : rf4_Plumbing rfw_outer (fun _ ↦ 0) rfw_E where
  h := Homeomorph.refl _
  stationary i := by
    change (OpenPartialHomeomorph.refl _).trans _ ∈ _
    rw [OpenPartialHomeomorph.refl_trans]
    exact rfw_cover.analytic i
  small _ := by change ‖(0 : ℂ)‖ < 1 / 5; norm_num
  w _ := rfw_chart 0
  w_mem _ := rfw_chart_mem 0
  w_target _ := by
    change closure (rf4_innerDisc 1 (1 / 5) 0) ⊆ (rfw_chart 0).target
    rw [rfw_innerDisc_eq, closure_ball _ (by norm_num), rfw_chart_target]
    exact Metric.closedBall_subset_ball (by norm_num)
  cover p := by
    by_cases hp : p ∈ rfw_O
    · exact Or.inl hp
    · right
      refine ⟨⟨0, Nat.one_pos⟩, ?_⟩
      change p ∈ (rfw_chart 0).symm '' rf4_innerDisc 1 (1 / 5) 0
      obtain ⟨z, hz, rfl⟩ := not_not.mp hp
      refine ⟨z, ?_, rfl⟩
      rw [rfw_innerDisc_eq, mem_ball_zero_iff]
      have : ‖z‖ ≤ 1 / 5 := by simpa using hz
      linarith
  disjoint x y hxy := (hxy (Subsingleton.elim (α := Fin 1) x y)).elim
  overlap _ := by
    change (Homeomorph.refl rfw_E) '' rfw_O ∩ (rfw_chart 0).symm '' rf4_innerDisc 1 (1 / 5) 0 =
      (Homeomorph.refl rfw_E) '' ((rfw_chart 0).symm '' b63r_annulus 1 (1 / 5))
    have e1 : ∀ s : Set rfw_E, (Homeomorph.refl rfw_E) '' s = s := image_id
    rw [e1, e1, rfw_innerDisc_eq]
    ext p
    simp only [rfw_chart_symm_apply, mem_inter_iff, mem_image]
    constructor
    · rintro ⟨hp, z, hz, rfl⟩
      refine ⟨z, ⟨?_, ?_⟩, rfl⟩
      · by_contra hc
        exact hp ⟨z, by simpa using hc, rfl⟩
      · have h2 : ‖z‖ < 2 / 5 := by simpa using hz
        norm_num; linarith
    · rintro ⟨u, hu, rfl⟩
      refine ⟨rfw_annulus_mem_O hu, u, ?_, rfl⟩
      have := hu.2
      rw [mem_ball_zero_iff]
      norm_num at this ⊢
      linarith
  glue _ u hu := by
    have hu' : u ∈ Metric.ball (0 : ℂ) (1 / 2) :=
      rfw_closedAnnulus_subset (rf4_annulus_subset_closed 1 _ hu)
    change rfw_proj u ∈ (rfw_chart 0).source ∧ rfw_chart 0 (rfw_proj u) = rf4_rootMap 1 0 u
    exact ⟨rfw_proj_mem_source hu', by rw [rfw_chart_proj hu']; simp [rf4_rootMap]⟩

example : rfw_plumbing.w ⟨0, Nat.one_pos⟩ = rfw_chart 0 := rfl

/-- The constant function `1` as a bounded holomorphic function on `U`.
Source: `b63r_bddHol`. -/
def rfw_one (U : Set ℂ) : b63r_bddHol U :=
  ⟨BoundedContinuousFunction.const _ 1, ⟨fun _ ↦ 1, differentiableOn_const 1, fun _ ↦ rfl⟩⟩

example (U : Set ℂ) (z : U) : ((rfw_one U : b63r_bddHol U) : U →ᵇ ℂ) z = 1 := rfl

/-- The form `dz` on the outer region as a bounded chart form: coefficient `1` on every piece; the
transitions are translations, with derivative `1`.
Source: Forster, *Lectures on Riemann Surfaces*, §9; RelativeFrame §5, A14. -/
def rfw_dzForm : rf2_bddForm rfw_cover :=
  ⟨fun i ↦ rfw_one _, by
    intro i j z w h
    change (1 : ℂ) = 1 * deriv (rfw_chart (rfw_cen j) ∘ (rfw_chart (rfw_cen i)).symm) z
    have hw : rfw_proj (w : ℂ) ∈ (rfw_chart (rfw_cen j)).source :=
      rfw_proj_mem_source (rfw_piece_subset j w.2)
    have h' : rfw_proj (z : ℂ) = rfw_proj (w : ℂ) := h
    rw [rfw_deriv_transition (h' ▸ hw), one_mul]⟩

example (i : Fin rfw_cover.n) : rfw_dzForm.val i = rfw_one _ := rfl

/-- The disc data of `dz`: `g₀ = 1` on `D(0, 2/5)`, so the sector coefficient is `1 · g₀ = 1`.
Source: RelativeFrame §4.2 (sector map). -/
def rfw_dzDisc : rf4_Disc rfw_outer := fun _ _ ↦ rfw_one _

example (x : Fin rfw_outer.m) (j : Fin (rfw_outer.deg x)) : rfw_dzDisc x j = rfw_one _ := rfl

/-- **The kernel element of `dz`**: coefficient `1` on every outer piece and `g₀ = 1` on the disc.
Source: RelativeFrame §4.2 (kernel); Forster, *Lectures on Riemann Surfaces*, §9. -/
def rfw_kdz : rf4_Src rfw_outer := (rfw_dzForm, rfw_dzDisc)

example : rfw_kdz.2 ⟨0, Nat.one_pos⟩ ⟨0, Nat.one_pos⟩ = rfw_one _ := rfl

/-- **The form `dz`** of `rfw_E`: the tangent coordinate in the chart at the base point. All chart
transitions are translations, so in every chart `rfw_chart c` this form is `1 · dz`.
Source: Forster, *Lectures on Riemann Surfaces*, §9 and §21 (the invariant differential of a
torus); Mathlib `TangentBundle` (tangent spaces modelled on `ℂ` through `chartAt`). -/
def rfw_dz : TangentBundle 𝓘(ℂ, ℂ) rfw_E → ℂ := fun q ↦ (q.2 : ℂ)

example (p : rfw_E) : rfw_dz ⟨p, (1 : ℂ)⟩ = 1 := rfl

/-! ## The constant family over the polydisc -/

section Family

attribute [local instance] rf5_polydiscCharted rf5_polydisc_isManifold

/-- Product charts of the total space `b6t_polydisc b × rfw_E`.
Source: Mathlib `prodChartedSpace`; `rf5_polydiscCharted`, `rfw_charted`. -/
instance rfw_totalCharted (b : Fin 10 → ℂ) :
    ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × rfw_E) :=
  prodChartedSpace (Fin 10 → ℂ) (b6t_polydisc b) ℂ rfw_E

example (b : Fin 10 → ℂ) (q : b6t_polydisc b × rfw_E) :
    chartAt ((Fin 10 → ℂ) × ℂ) q =
      (chartAt (Fin 10 → ℂ) q.1).prod (chartAt ℂ q.2) := rfl

/-- The total space is an analytic manifold.
Source: Mathlib `IsManifold.prod`; `rf5_polydisc_isManifold`, `rfw_isManifold`. -/
instance rfw_total_isManifold (b : Fin 10 → ℂ) :
    IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × rfw_E) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℂ, Fin 10 → ℂ)) (I' := 𝓘(ℂ, ℂ)) (b6t_polydisc b) rfw_E

/-- The product coordinate of a fibre, as a single chart onto `rfw_E`.
Source: `b6m_coordinate`. -/
def rfw_fibreChart (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    OpenPartialHomeomorph (b6m_Fibre b rfw_E t) rfw_E :=
  (b6m_coordinate b rfw_E t).toOpenPartialHomeomorph

example (b : Fin 10 → ℂ) (t : b6t_polydisc b) (p : rfw_E) :
    rfw_fibreChart b t ⟨(t, p), rfl⟩ = p := rfl

/-- The fibre charted over `rfw_E` by its coordinate.
Source: Mathlib `OpenPartialHomeomorph.singletonChartedSpace`. -/
@[instance_reducible] def rfw_fibreE (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    ChartedSpace rfw_E (b6m_Fibre b rfw_E t) :=
  (rfw_fibreChart b t).singletonChartedSpace (by simp [rfw_fibreChart])

example (b : Fin 10 → ℂ) (t : b6t_polydisc b) (y : b6m_Fibre b rfw_E t) :
    @chartAt _ _ _ _ (rfw_fibreE b t) y = rfw_fibreChart b t := rfl

/-- The fibre charted over `ℂ`: the charts of `rfw_E` composed with the coordinate.
Source: Mathlib `ChartedSpace.comp`; `rfw_charted`. -/
instance rfw_fibreCharted (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    ChartedSpace ℂ (b6m_Fibre b rfw_E t) :=
  @ChartedSpace.comp ℂ _ rfw_E _ (b6m_Fibre b rfw_E t) _ _ (rfw_fibreE b t)

example (b : Fin 10 → ℂ) (t : b6t_polydisc b) (y : b6m_Fibre b rfw_E t) :
    chartAt ℂ y = rfw_fibreChart b t ≫ₕ chartAt ℂ (rfw_fibreChart b t y) := rfl

/-- Each fibre is a Riemann surface.
Source: the transitions are those of `rfw_E`, `rf5_comp_transition`. -/
instance rfw_fibre_isManifold (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    IsManifold 𝓘(ℂ, ℂ) ω (b6m_Fibre b rfw_E t) := by
  refine { compatible := ?_ }
  rintro _ _ ⟨c, hc, f, hf, rfl⟩ ⟨c', hc', f', hf', rfl⟩
  have hc1 : c = rfw_fibreChart b t := hc
  have hc2 : c' = rfw_fibreChart b t := hc'
  subst hc1 hc2
  exact (contDiffGroupoid ω 𝓘(ℂ, ℂ)).mem_of_eqOnSource
    (HasGroupoid.compatible hf hf') (rf5_comp_transition _ f f')

/-- A chart of `rfw_E` composed with the coordinate is a chart of the fibre. -/
theorem rfw_fibre_mem_maximalAtlas (b : Fin 10 → ℂ) (t : b6t_polydisc b)
    {f : OpenPartialHomeomorph rfw_E ℂ} (hf : f ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω rfw_E) :
    rfw_fibreChart b t ≫ₕ f ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (b6m_Fibre b rfw_E t) := by
  rintro _ ⟨c, hc, f', hf', rfl⟩
  have hc1 : c = rfw_fibreChart b t := hc
  subst hc1
  exact ⟨(contDiffGroupoid ω 𝓘(ℂ, ℂ)).mem_of_eqOnSource (hf f' hf').1
      (rf5_comp_transition _ f f'),
    (contDiffGroupoid ω 𝓘(ℂ, ℂ)).mem_of_eqOnSource (hf f' hf').2
      (rf5_comp_transition _ f' f)⟩

/-- Fibres are Hausdorff. Source: `b6m_coordinate`. -/
instance rfw_fibre_t2 (b : Fin 10 → ℂ) (t : b6t_polydisc b) : T2Space (b6m_Fibre b rfw_E t) :=
  (b6m_coordinate b rfw_E t).isEmbedding.t2Space

/-- Fibres are compact. Source: `b6m_coordinate`. -/
instance rfw_fibre_compact (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    CompactSpace (b6m_Fibre b rfw_E t) :=
  (b6m_coordinate b rfw_E t).symm.compactSpace

/-- Fibres are connected. Source: `b6m_coordinate`. -/
instance rfw_fibre_connected (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    ConnectedSpace (b6m_Fibre b rfw_E t) :=
  (b6m_coordinate b rfw_E t).symm.surjective.connectedSpace
    (b6m_coordinate b rfw_E t).symm.continuous

/-- The plumbing datum of the fibre at `t`, transported from `rfw_plumbing` along the coordinate.
Source: `rf5_transportPlumbing`, `rfw_plumbing`. -/
def rfw_plumbingAt (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    rf4_Plumbing rfw_outer (fun _ ↦ 0) (b6m_Fibre b rfw_E t) :=
  rf5_transportPlumbing (b6m_coordinate b rfw_E t) (fun _ hf ↦ rfw_fibre_mem_maximalAtlas b t hf)
    rfw_plumbing

example (b : Fin 10 → ℂ) (t : b6t_polydisc b) (x : Fin rfw_outer.m) :
    (rfw_plumbingAt b t).w x = rfw_fibreChart b t ≫ₕ rfw_chart 0 := rfl

/-- **The constant family** over the whole polydisc: base surface `rfw_E`, outer data `rfw_outer`,
`ε = 0`, the plumbing datum of each fibre transported along the product coordinate, stationary
outer charts and the disc coordinate `wTot(t, p) = rfw_chart 0 p`.
Source: `rf5_FamilyPlumbing`; `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 and §4.4. -/
def rfw_family (b : Fin 10 → ℂ) :
    rf5_FamilyPlumbing b rfw_E rfw_outer (b6t_polydisc b) subset_rfl where
  ε := fun _ _ ↦ 0
  ε_analytic := analyticOnNhd_const
  S t := rfw_plumbingAt b t
  h_eq t := by ext; rfl
  outer_analytic i := by
    rw [modelWithCornersSelf_prod]
    exact (contMDiffOn_of_mem_maximalAtlas (rfw_cover.analytic i)).comp
      contMDiff_snd.contMDiffOn (fun q hq ↦ hq)
  wTot _ q := rfw_chart 0 q.2
  wSrc _ := {q | q.2 ∈ (rfw_chart 0).source}
  wSrc_open _ := (rfw_chart 0).open_source.preimage continuous_snd
  w_analytic _ := by
    rw [modelWithCornersSelf_prod]
    exact (contMDiffOn_of_mem_maximalAtlas (rfw_chart_mem 0)).comp
      contMDiff_snd.contMDiffOn (fun q hq ↦ hq)
  w_source t _ y := by
    simp [rfw_plumbingAt, rf5_transportPlumbing, rfw_plumbing, b6m_coordinate]
    exact Iff.rfl
  w_eq t _ y _ := rfl

example (b : Fin 10 → ℂ) (t : b6t_polydisc b) : (rfw_family b).ε t = 0 := rfl

/-- The fibre coordinate is holomorphic. -/
theorem rfw_coordinate_contMDiff (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b6m_coordinate b rfw_E t) := by
  intro y
  let f := chartAt ℂ (b6m_coordinate b rfw_E t y)
  have hf : f ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω rfw_E :=
    IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ _)
  have hg := rfw_fibre_mem_maximalAtlas b t hf
  have hy : y ∈ (rfw_fibreChart b t ≫ₕ f).source := by
    simp [rfw_fibreChart, f, mem_chart_source]
  have h := ((contMDiffOn_symm_of_mem_maximalAtlas hf).comp
    (contMDiffOn_of_mem_maximalAtlas hg) (fun z hz ↦ ((rfw_fibreChart b t ≫ₕ f).map_source hz).1)
    ).contMDiffAt ((rfw_fibreChart b t ≫ₕ f).open_source.mem_nhds hy)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [(rfw_fibreChart b t ≫ₕ f).open_source.mem_nhds hy] with z hz
  have hz' : b6m_coordinate b rfw_E t z ∈ f.source := by
    simpa [rfw_fibreChart] using hz.2
  simp [rfw_fibreChart, f.left_inv hz']

/-- The fibre inclusions are holomorphic. -/
theorem rfw_incl (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (fun x : b6m_Fibre b rfw_E t ↦ x.val) := by
  have he : (fun x : b6m_Fibre b rfw_E t ↦ x.val) =
      fun x ↦ (t, b6m_coordinate b rfw_E t x) := by
    funext x
    exact Prod.ext x.property rfl
  rw [he, modelWithCornersSelf_prod]
  exact contMDiff_const.prodMk (rfw_coordinate_contMDiff b t)

/-- Every point of the total space lies in a fibre-preserving product chart. -/
theorem rfw_fibreCharts (b : Fin 10 → ℂ) (q : b6t_polydisc b × rfw_E) :
    ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × rfw_E),
      q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val :=
  ⟨chartAt _ q, chart_mem_atlas _ q, mem_chart_source _ q, fun _ _ ↦ rfl⟩

/-- **The form `dz` on the fibre at `t`**: the tangent coordinate in the chart at the base point.
Source: as `rfw_dz`; Forster, *Lectures on Riemann Surfaces*, §21. -/
def rfw_fibreDz (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    TangentBundle 𝓘(ℂ, ℂ) (b6m_Fibre b rfw_E t) → ℂ := fun q ↦ (q.2 : ℂ)

example (b : Fin 10 → ℂ) (t : b6t_polydisc b) (y : b6m_Fibre b rfw_E t) :
    rfw_fibreDz b t ⟨y, (1 : ℂ)⟩ = 1 := rfl

end Family

end HodgeLean.Foundations.Program

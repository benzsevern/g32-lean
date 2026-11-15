import HodgeLean.Foundations.Program.RelativeFrameEllipticProofs

/-! # A genus-one witness for relative-frame stages C and C12: statement draft
Implications and identities on one explicit surface of genus one, the elliptic curve
`rfw_E = ℂ ⧸ (ℤ + iℤ)` of track B3 recharted on `ℂ` (charts: local inverses of `z ↦ [z e₀]` on
discs of radius `1/2`), with outer data of one disc of degree one around `[0]` (radius `1/5`, an
annulus piece and a finite cover of the outer region), the constant plumbing datum with `ε = 0`,
and the constant family over the polydisc with the product total space. Claimed: the genus of
`rfw_E` is one; the invariant form `dz` is a holomorphic form; the glued form of the explicit
kernel element `rfw_kdz` is `dz`, on `rfw_E` and on every fibre of the family; and the range of
`δ_0` has codimension one. Checked with bodies from definitions and proved results: the plumbing
and family data, `rfw_kdz ∈ ker δ_0`, `ker δ_0 ≠ 0`, and the glued form and the glued relative form
are nonzero at every parameter. The chain checks run the frozen stage C and C12 statements at
positive rank: the kernel has dimension one and is spanned by `rfw_kdz`, the glued family is a
relative form, D1 extends a nonzero fibre form, and the fibre values span every fibre.

Not claimed: anything about the B6-2b family or its fibres, whose plumbing data are stage B; a
moving plumbing (`ε ≠ 0`) on a surface of positive genus; any statement of stage D beyond the chain
checks. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

/-- Genus one: the holomorphic forms of `rfw_E` form a complex line. The charts of `rfw_E` are
those of `b3_Elliptic` composed with the linear isomorphism `Fin 1 → ℂ ≃ ℂ` of `b3A_φ`, so
holomorphic forms correspond, and `b3A_elliptic_finrank_holForm` gives dimension one.
Source: `b3A_elliptic_finrank_holForm`; Forster, *Lectures on Riemann Surfaces*, §21 (a torus
has genus one); Birkenhake–Lange, *Complex Abelian Varieties*, §1.1. -/
theorem rfw_holForm_finrank : Module.finrank ℂ (b3_HolForm ℂ rfw_E) = 1 :=
  rfw_holForm_finrank_aux

example := @rfw_holForm_finrank

/-- The invariant form `dz` is a holomorphic form on `rfw_E`. In the bundle chart of the tangent
bundle over a chart `rfw_chart c`, a tangent vector `(p, v)` has coordinates `(z, v)`, because every
chart transition is a translation with derivative one (`rfw_deriv_transition`); so `rfw_dz` is the
second coordinate there, analytic and linear on fibres.
Source: Forster, *Lectures on Riemann Surfaces*, §9 and §21; Mathlib `TangentBundle` (bundle charts
from `tangentBundleCore`). -/
theorem rfw_dz_mem_holForm : rfw_dz ∈ b3_HolForm ℂ rfw_E :=
  rfw_dz_mem_holForm_aux

example := @rfw_dz_mem_holForm

/-- The glued form of the kernel element `rfw_kdz` is `dz`. Every point is in the outer region or
in the inner piece (`cover`). On a piece of the outer cover the glued form is the coefficient `1`
times the differential of the piece chart, which is the identity in the chart at the point (the
transition is a translation); on the inner piece it is the sector coefficient `1 · g₀ = 1` times
the differential of `rfw_chart 0`, again the identity.
Source: the definitions `rf4_glue`, `rfw_kdz`, `rfw_dz`; Forster, *Lectures on Riemann Surfaces*,
§9; Mathlib `mfderiv` (manifold derivative in charts). -/
theorem rfw_glue_kdz : rf4_glue rfw_plumbing rfw_kdz = rfw_dz :=
  rfw_glue_kdz_aux

example := @rfw_glue_kdz

/-- The glued form of `rfw_kdz` on the fibre at `t` of the constant family is the fibre's `dz`.
The fibre charts are the charts of `rfw_E` composed with the coordinate, so the computation of
`rfw_glue_kdz` applies in them.
Source: the definitions `rf4_glue`, `rf5_transportPlumbing`, `rfw_fibreCharted`, `rfw_fibreDz`;
Forster, *Lectures on Riemann Surfaces*, §9. -/
theorem rfw_fibre_glue_kdz (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    rf4_glue (rfw_plumbingAt b t) rfw_kdz = rfw_fibreDz b t :=
  rfw_fibre_glue_kdz_aux b t

example := @rfw_fibre_glue_kdz

/-- The range of `δ_0` on `rfw_E` has codimension exactly one, so the index of `δ_0` is
`1 − 1 = 0 = g − 1`. At most one: the cutoff map of `rf4_cutoff_obstruction` has kernel inside the
range and lands in the `(1,1)` Dolbeault quotient, of dimension `dim H¹(X, Ω¹) = 1` on a compact
connected Riemann surface. At least one: `rf4_delta_not_surjective` with one disc.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.3; `rf4_cutoff_obstruction`,
`rf4_delta_not_surjective`; Forster, *Lectures on Riemann Surfaces*, §15 (Dolbeault) and §17
(Serre duality, `dim H¹(X, Ω) = 1`). -/
theorem rfw_delta_coker_finrank :
    Module.finrank ℂ (rf4_Tgt rfw_outer ⧸ (rf4_delta rfw_outer (fun _ ↦ 0)).range) = 1 :=
  rfw_delta_coker_finrank_aux

example := @rfw_delta_coker_finrank

/-! ## Satisfiable instances, non-degenerate

Every check below uses definitions and proved results only, never a statement of this file or an
open statement of stage C or C12. -/

/-- The surface is compact, connected and Hausdorff, so the compact statements of stage C apply. -/
example : T2Space rfw_E ∧ CompactSpace rfw_E ∧ ConnectedSpace rfw_E ∧
    IsManifold 𝓘(ℂ, ℂ) ω rfw_E :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The plumbing premise is satisfiable on the genus-one surface, with one disc. -/
example : Nonempty (rf4_Plumbing rfw_outer (fun _ ↦ 0) rfw_E) ∧ rfw_outer.m = 1 :=
  ⟨⟨rfw_plumbing⟩, rfl⟩

/-- The point `[0]` is not in the outer region, and the cover has an annulus piece. -/
example : rfw_proj 0 ∉ rfw_O ∧ rfw_outer.P.piece (rfw_outer.ann ⟨0, Nat.one_pos⟩) =
    b63r_annulus 1 (1 / 5) :=
  ⟨rfw_proj_zero_not_mem_O, rfl⟩

/-- A point `3/10` of the annulus `{1/5 < |u| < 2/5}`. -/
theorem rfw_test_mem : (3 / 10 : ℂ) ∈ b63r_annulus 1 (1 / 5) := by
  constructor <;> norm_num [Complex.norm_div]

/-- **`rfw_kdz` is in the kernel of `δ_0`**: on the annulus, the outer coefficient `1` equals the
sector value `1 · (1 − 0)^0 · g₀(u) = 1`. -/
theorem rfw_kdz_mem_ker : rfw_kdz ∈ (rf4_delta rfw_outer (fun _ ↦ 0)).ker := by
  rw [LinearMap.mem_ker]
  funext x
  apply Subtype.ext
  ext u
  have hu : (u : ℂ) ∈ Metric.ball (0 : ℂ) (2 * (1 / 5)) := by
    have := u.2.2
    change ‖(u : ℂ)‖ ^ 1 < 2 * (1 / 5) at this
    rw [mem_ball_zero_iff]
    simpa using this
  have hs := rf4_sectorOp_apply (rfw_outer.deg x) (rfw_outer.hdeg x) rfw_outer.r rfw_outer.hr
    (rfw_outer.c x) 0 (by change ‖(0 : ℂ)‖ < 1 / 5; norm_num) (rfw_dzDisc x) u
  change _ = ((1 : ℕ) : ℂ) * ∑ j : Fin 1, rf4_multiplierFun 1 0 j u *
    rf4_extendBdd (rfw_one (Metric.ball (0 : ℂ) (2 * (1 / 5)))) (0 + (u : ℂ) ^ 1) at hs
  simp only [Fin.sum_univ_one, rf4_multiplierFun, rf4_sectorExp, rf4_extendBdd, zero_add, pow_one,
    hu, ↓reduceDIte, Nat.cast_one, one_mul, zero_mul, sub_zero, Complex.one_cpow] at hs
  have key : ((rf4_delta rfw_outer (fun _ ↦ 0) rfw_kdz x : b63r_bddHol _) : _ →ᵇ ℂ) u =
      (1 : ℂ) - ((rf4_sectorOp (rfw_outer.deg x) (rfw_outer.hdeg x) rfw_outer.r rfw_outer.hr
        (rfw_outer.c x) 0 (rfw_dzDisc x) : b63r_bddHol _) : _ →ᵇ ℂ) u := rfl
  refine key.trans ?_
  rw [hs]
  change (1 : ℂ) - _ * 1 * 1 = 0
  simp

/-- `rfw_kdz` is not zero: its disc part is `g₀ = 1`. -/
theorem rfw_kdz_ne_zero : rfw_kdz ≠ 0 := by
  intro h
  have h1 := congrArg (fun k : rf4_Src rfw_outer ↦ (k.2 ⟨0, Nat.one_pos⟩ ⟨0, Nat.one_pos⟩).val
    ⟨0, by change (0 : ℂ) ∈ Metric.ball (0 : ℂ) (2 * (1 / 5)); norm_num⟩) h
  exact one_ne_zero h1

/-- **Positive rank, from definitions**: `ker δ_0 ≠ 0` on the genus-one surface. -/
theorem rfw_ker_ne_bot : (rf4_delta rfw_outer (fun _ ↦ 0)).ker ≠ ⊥ := by
  intro h
  have := rfw_kdz_mem_ker
  rw [h, Submodule.mem_bot] at this
  exact rfw_kdz_ne_zero this

/-- The operator `δ_0` is not zero: its outer part at `(dz, 0)` has value `1` at `u = 3/10`. -/
example : rf4_delta rfw_outer (fun _ ↦ 0) (rfw_dzForm, 0) ≠ 0 := by
  intro h
  have := congrArg (fun f : rf4_Tgt rfw_outer ↦
    ((f ⟨0, Nat.one_pos⟩ : b63r_bddHol (b63r_annulus 1 (1 / 5))).val :
      b63r_annulus 1 (1 / 5) →ᵇ ℂ) ⟨3 / 10, rfw_test_mem⟩) h
  simp [rf4_delta, b63r_bddHol_restrict, b63r_bddHol_comp, rf2_bddForm_coeff,
    b63r_restrictMap] at this
  exact one_ne_zero this

/-- The glued form of `rfw_kdz` is nonzero at a point of an inner piece outside the outer region,
for every plumbing datum over `rfw_outer`: the sector coefficient there is `1` and the differential
of a chart does not vanish. -/
theorem rfw_glue_ne_zero {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {ε : Fin rfw_outer.m → ℂ} (S : rf4_Plumbing rfw_outer ε X) (y : X)
    (hyO : S.h.symm y ∉ rfw_O) (hy : y ∈ (S.w ⟨0, Nat.one_pos⟩).source)
    (hyD : S.w ⟨0, Nat.one_pos⟩ y ∈ rf4_innerDisc 1 (1 / 5) (ε ⟨0, Nat.one_pos⟩)) :
    rf4_glue S rfw_kdz ⟨y, (1 : ℂ)⟩ ≠ 0 := by
  have hO : ¬ ∃ i, S.h.symm y ∈ (rfw_outer.P.chart i).source ∧
      rfw_outer.P.chart i (S.h.symm y) ∈ rfw_outer.P.piece i := by
    rintro ⟨i, h1, h2⟩
    exact hyO ((Set.ext_iff.mp rfw_outer.P.covers _).mpr
      (mem_iUnion.2 ⟨i, _, h2, (rfw_outer.P.chart i).left_inv h1⟩))
  have hD : ∃ x, y ∈ (S.w x).source ∧
      S.w x y ∈ rf4_innerDisc (rfw_outer.deg x) rfw_outer.r (ε x) := ⟨_, hy, hyD⟩
  unfold rf4_glue
  rw [dite_eq_right hO, dite_eq_left hD]
  have hspec := Classical.choose_spec hD
  generalize Classical.choose hD = x at hspec ⊢
  refine mul_ne_zero ?_ (rf5_mfderiv_chart_ne_zero (S.w_mem x) hspec.1)
  have hb : rfw_outer.c x + ε x + S.w x y ^ 1 ∈ Metric.ball (0 : ℂ) (2 * (1 / 5)) := by
    have := hspec.2
    change ‖S.w x y ^ 1 + ε x‖ < 2 * (1 / 5) at this
    rw [mem_ball_zero_iff]
    change ‖0 + ε x + S.w x y ^ 1‖ < 2 * (1 / 5)
    rwa [zero_add, add_comm]
  change ((1 : ℕ) : ℂ) * ∑ j : Fin 1, S.w x y ^ (j : ℕ) *
    rf4_extendBdd (rfw_one (Metric.ball (0 : ℂ) (2 * (1 / 5))))
      (rfw_outer.c x + ε x + S.w x y ^ 1) ≠ 0
  simp only [Nat.cast_one, Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul, rf4_extendBdd, hb,
    ↓reduceDIte]
  exact one_ne_zero

/-- **The glued form is nonzero** on the genus-one surface, at the point `[0]` of the inner
piece. -/
example : rf4_glue rfw_plumbing rfw_kdz ⟨rfw_proj 0, (1 : ℂ)⟩ ≠ 0 := by
  refine rfw_glue_ne_zero rfw_plumbing (rfw_proj 0) rfw_proj_zero_not_mem_O
    (rfw_proj_mem_source (by simp)) ?_
  change rfw_chart 0 (rfw_proj 0) ∈ rf4_innerDisc 1 (1 / 5) 0
  rw [rfw_chart_proj (by simp), rfw_innerDisc_eq]
  simp

/-- **The glued relative form is nonzero at every parameter**: for the constant family of
`rfw_kdz`, the fibre value at every `t` is nonzero at the point over `[0]`. -/
theorem rfw_relGlue_ne_zero (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    rf5_relGlue (rfw_family b) univ (fun _ ↦ rfw_kdz) t ≠ 0 := by
  intro h
  let y : b6m_Fibre b rfw_E t := ⟨(t, rfw_proj 0), rfl⟩
  have h1 := congrFun h ⟨y, (1 : ℂ)⟩
  simp only [rf5_relGlue, mem_univ, ↓reduceIte, Pi.zero_apply] at h1
  refine rfw_glue_ne_zero (rfw_plumbingAt b t) y rfw_proj_zero_not_mem_O ⟨trivial, ?_⟩ ?_ h1
  · exact rfw_proj_mem_source (by simp)
  · change rfw_chart 0 (rfw_proj 0) ∈ rf4_innerDisc 1 (1 / 5) 0
    rw [rfw_chart_proj (by simp), rfw_innerDisc_eq]
    simp

/-- The premises of the C12 statements hold for the constant family over `rfw_E`: the total space
is an analytic manifold, the fibre inclusions are holomorphic, the fibres are compact, connected
and Hausdorff, every point lies in a fibre-preserving atlas chart, and `V` is open. -/
example (b : Fin 10 → ℂ) :
    Nonempty (rf5_FamilyPlumbing b rfw_E rfw_outer (b6t_polydisc b) subset_rfl) ∧
    IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × rfw_E) ∧
    (∀ t : b6t_polydisc b, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b rfw_E (b6t_polydisc b) subset_rfl t ↦ x.val)) ∧
    (∀ t : b6t_polydisc b,
      T2Space (b63l_parameterFibre b rfw_E (b6t_polydisc b) subset_rfl t) ∧
      CompactSpace (b63l_parameterFibre b rfw_E (b6t_polydisc b) subset_rfl t) ∧
      ConnectedSpace (b63l_parameterFibre b rfw_E (b6t_polydisc b) subset_rfl t)) ∧
    (∀ q : b6t_polydisc b × rfw_E, ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × rfw_E),
        q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val) ∧
    IsOpen (b6t_polydisc b) :=
  ⟨⟨rfw_family b⟩, inferInstance, fun t ↦ rfw_incl b t,
    fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩, rfw_fibreCharts b,
    rf5_polydisc_isOpen b⟩

/-! ## Chain check

The stage served is the kernel frame of stage C and the relative forms of C12, the field
`b63e_relForm`. On the genus-one surface the frozen statements `rf4_ker_finrank`,
`rf4_kernel_equiv`, `rf5_relForm_of_kernel` and `rf5_relForm_extend` run at positive rank. These
are dependency chains through open statements; they do not construct a frame here. -/

/-- The kernel of `δ_0` has dimension one (`rf4_ker_finrank` and genus one). -/
example : Module.finrank ℂ (rf4_delta rfw_outer (fun _ ↦ 0)).ker = 1 :=
  (rf4_ker_finrank rfw_plumbing).2.trans rfw_holForm_finrank

/-- The kernel of `δ_0` is the line spanned by `rfw_kdz`. -/
example : (rf4_delta rfw_outer (fun _ ↦ 0)).ker = Submodule.span ℂ {rfw_kdz} := by
  obtain ⟨hfin, hrank⟩ := rf4_ker_finrank rfw_plumbing
  rw [rfw_holForm_finrank] at hrank
  symm
  refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr
    rfw_kdz_mem_ker) ?_
  rw [finrank_span_singleton rfw_kdz_ne_zero, hrank]

/-- The glued form of `rfw_kdz` is a holomorphic form (`rf4_kernel_equiv`), and it is `dz`. -/
example : rf4_glue rfw_plumbing rfw_kdz ∈ b3_HolForm ℂ rfw_E ∧
    rf4_glue rfw_plumbing rfw_kdz = rfw_dz := by
  obtain ⟨e, he⟩ := rf4_kernel_equiv rfw_plumbing
  refine ⟨?_, rfw_glue_kdz⟩
  rw [← he ⟨rfw_kdz, rfw_kdz_mem_ker⟩]
  exact (e ⟨rfw_kdz, rfw_kdz_mem_ker⟩).2

/-- C12 at positive rank: the constant family of `rfw_kdz` glues to a relative form over the whole
polydisc (`rf5_relForm_of_kernel`, with the kernel condition from `rfw_kdz_mem_ker`). -/
example (b : Fin 10 → ℂ) :
    rf5_relGlue (rfw_family b) univ (fun _ ↦ rfw_kdz) ∈
      b63e_relForm b rfw_E (b6t_polydisc b) subset_rfl univ :=
  rf5_relForm_of_kernel (fun _ ↦ rfw_incl b _) (rfw_family b) univ isOpen_univ _
    analyticOnNhd_const (fun _ _ ↦ rfw_kdz_mem_ker)

/-- Each fibre has genus one (`b63e_holForm_finrank_homeomorph` along the coordinate). -/
example (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    Module.finrank ℂ (b3_HolForm ℂ (b6m_Fibre b rfw_E t)) = 1 :=
  (b63e_holForm_finrank_homeomorph _ _ (b6m_coordinate b rfw_E t)).trans rfw_holForm_finrank

/-- The fibre values of the glued relative form span every fibre: every holomorphic form on the
fibre at `t` is a multiple of the glued form of `rfw_kdz` (rank one, nonzero, holomorphic by
`rf4_kernel_equiv`). -/
example (b : Fin 10 → ℂ) (t : b6t_polydisc b) (η : b3_HolForm ℂ (b6m_Fibre b rfw_E t)) :
    ∃ c : ℂ, (η : TangentBundle 𝓘(ℂ, ℂ) (b6m_Fibre b rfw_E t) → ℂ) =
      c • rf5_relGlue (rfw_family b) univ (fun _ ↦ rfw_kdz) t := by
  have hg : Module.finrank ℂ (b3_HolForm ℂ (b6m_Fibre b rfw_E t)) = 1 :=
    (b63e_holForm_finrank_homeomorph _ _ (b6m_coordinate b rfw_E t)).trans rfw_holForm_finrank
  obtain ⟨e, he⟩ := rf4_kernel_equiv (rfw_plumbingAt b t)
  let θ : b3_HolForm ℂ (b6m_Fibre b rfw_E t) := e ⟨rfw_kdz, rfw_kdz_mem_ker⟩
  have hθ : (θ : TangentBundle 𝓘(ℂ, ℂ) (b6m_Fibre b rfw_E t) → ℂ) =
      rf5_relGlue (rfw_family b) univ (fun _ ↦ rfw_kdz) t := by
    simp only [θ, he, rf5_relGlue, mem_univ, ↓reduceIte]
    rfl
  have hθ0 : θ ≠ 0 := fun h0 ↦ rfw_relGlue_ne_zero b t (by rw [← hθ, h0]; rfl)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' θ hθ0).mp hg η
  exact ⟨c, by rw [← hc, ← hθ]; rfl⟩

/-- D1 at positive rank: a nonzero form on the fibre at `t₀` is the fibre value of a relative form
near `t₀` (`rf5_relForm_extend`). -/
example (b : Fin 10 → ℂ) (t₀ : b6t_polydisc b) :
    ∃ η : b3_HolForm ℂ (b6m_Fibre b rfw_E t₀), η ≠ 0 ∧
      ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ b6t_polydisc b ∧
        ∃ θ : b63e_relForm b rfw_E (b6t_polydisc b) subset_rfl W,
          b63e_relFormAt b rfw_E (b6t_polydisc b) subset_rfl θ t₀ = η := by
  obtain ⟨e, he⟩ := rf4_kernel_equiv (rfw_plumbingAt b t₀)
  let η : b3_HolForm ℂ (b6m_Fibre b rfw_E t₀) := e ⟨rfw_kdz, rfw_kdz_mem_ker⟩
  have hη : η ≠ 0 := by
    intro h0
    apply rfw_relGlue_ne_zero b t₀
    have h1 : (η : TangentBundle 𝓘(ℂ, ℂ) (b6m_Fibre b rfw_E t₀) → ℂ) = 0 := by rw [h0]; rfl
    simp only [η, he] at h1
    simp only [rf5_relGlue, mem_univ, ↓reduceIte]
    exact h1
  exact ⟨η, hη, rf5_relForm_extend (rf5_polydisc_isOpen b) (fun _ ↦ rfw_incl b _)
    (rfw_family b) t₀ η⟩

#check @b63e_relForm

#print axioms rfw_plumbing
#print axioms rfw_family
#print axioms rfw_kdz
#print axioms rfw_dz
#print axioms rfw_isManifold
#print axioms rfw_kdz_mem_ker
#print axioms rfw_ker_ne_bot
#print axioms rfw_glue_ne_zero
#print axioms rfw_relGlue_ne_zero
#print axioms rfw_incl

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.RelativeFrameFamilyProofs
import HodgeLean.Foundations.Program.RelativeFrameRestated

/-! # The B6-2b family datum, first stage: statement draft
Implications from the B6-2b analytic atlas output (`rf7_HurwitzAtlas`, the conclusion of
`b6a_analytic_atlas` field for field) to the geometric inputs of the family datum
`rf5_FamilyPlumbing`: at the marked root configuration, an atlas package whose cover carries the
root marking and whose orders are the orders of the root elements; from a configuration of the
normalized chart to the outer radius `ρ = 5r/4` with disc separation and stationary bounds; from
an atlas package to a finite covering over each punctured `3r` disc, to open proper surjective
components `Δ'_x` with one point over `b_i` and degree `n x`, to a normalized base root coordinate
`f = b_i + uⁿ` on each `Δ'_x`, to a moving root `w` on the fixed total-space source
`polydisc × Δ'_x`, jointly analytic, with exact targets and the principal-root collar identity,
to disjoint components, the cover `C = O ∪ ⋃ Δ_x` and the exact overlaps `O ∩ Δ_x`, and to outer
data of radius `ρ` whose charts are stationary and analytic on each entire chart source; and from
a connected finite holomorphic covering of a disc punctured off centre to an injective
holomorphic coordinate `v` with `q = c + vᵏ` and its exact image.

Not claimed: the fibre plumbing data `S t` of `rf5_FamilyPlumbing` (stationarity for each fibre
structure, `h_eq`, `w_source`, `w_eq`), the assembly of the family datum, and the instances of
D2–D4 at positive rank; they are planned in `docs/specs/RelativeFrameFamily.md`. No statement
here concerns forms, operators, kernels or dimensions. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Manifold Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold b4b_group

/-! ## Statements -/

/-- **Statement 1 (B3–B4 on the marked root construction).** For the explicit loops at the marked
root configuration, there is a B6-2b atlas package over `mr_base` for `b4b_Group` whose cover
carries the root marking (the `i`-th loop has monodromy `op (b4b_root i)`) and whose order `n x`
at every point over a mark `j` is the order of `b4b_root j` (three, or two at `∞`). The package
is the output of `b6a_analytic_atlas` for the constructive filling of the marked root cover; the
orders are the local degrees of the branch formula, which are the orders of the local monodromy.
Source: `mr_rootCover`, `b6a_analytic_atlas`; `b64c_fill_totalSpace` on `main`
(`PeriodFunctionChecks.lean:219`); Forster, *Lectures on Riemann Surfaces*, §§4–5 and
Theorem 8.4 (ramification index and local monodromy). -/
theorem rf7_rootAtlas (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i)) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction b4b_Group C)
      (_ : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C))
      (P : rf7_HurwitzAtlas mr_base b4b_Group C),
      (∃ u₀ : P.π ⁻¹' {y₀}, ∀ i,
        P.hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i)) ∧
      ∀ x (j : Fin 13), P.f x = b6_branch mr_base j → P.n x = orderOf (b4b_root j) :=
  rf7_rootAtlas_aux y₀ γ hγ

example := @rf7_rootAtlas

/-- **Statement 2 (radius choice).** With `r = b6t_radius b` and `ρ = rf7_radius b = 5r/4`:
`r < ρ` and `2ρ < 3r`; the closed `3r` discs about the moving values are pairwise disjoint and
avoid `0` and `1`; every point of a closed annulus `ρ ≤ |z − b_i| ≤ 2ρ` lies outside every closed
tent disc; and every moving value `t_i − b_i` of the polydisc is smaller than `ρ`.
Source: `docs/specs/RelativeFrameCharts.md` (the radius discussion); the separation `8r < d`,
`4r < ‖b_i‖`, `4r < ‖b_i − 1‖` of `rf3_radius_separation` on `main` (`b6t_radius`). -/
theorem rf7_radius_bounds (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    b6t_radius b < rf7_radius b ∧ 2 * rf7_radius b < 3 * b6t_radius b ∧
      (∀ i j : Fin 10, i ≠ j → Disjoint (Metric.closedBall (b i) (3 * b6t_radius b))
        (Metric.closedBall (b j) (3 * b6t_radius b))) ∧
      (∀ i, (0 : ℂ) ∉ Metric.closedBall (b i) (3 * b6t_radius b) ∧
        (1 : ℂ) ∉ Metric.closedBall (b i) (3 * b6t_radius b)) ∧
      (∀ i (z : ℂ), rf7_radius b ≤ dist z (b i) → dist z (b i) ≤ 2 * rf7_radius b →
        ∀ j, b6t_radius b < dist z (b j)) ∧
      ∀ t ∈ b6t_polydisc b, ∀ i, ‖t i - b i‖ < rf7_radius b :=
  rf7_radius_bounds_aux b hb

example := @rf7_radius_bounds

/-- **Statement 3 (B7a).** For an atlas package, the base projection `f` is a covering over each
punctured disc `D(b_i, 3r) ∖ {b_i}`, and every fibre of `f` is finite. Over the punctured disc no
branch value occurs, so `hfree` makes `f` a local homeomorphism there; `C` is compact, so `f` is
closed and its fibres are discrete and finite.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 item 1 (B7a); Mathlib
`IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` (`Topology/Covering/Basic.lean`). -/
theorem rf7_covering {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) :
    IsCoveringMapOn P.f
        (rf7_sphereBall (b i) (3 * b6t_radius b) \ {((b i : ℂ) : OnePoint ℂ)}) ∧
      ∀ p : OnePoint ℂ, (P.f ⁻¹' {p}).Finite :=
  rf7_covering_aux P i

example := @rf7_covering

/-- **Statement 4 (B7b, B7e).** For a point `x` over `b_i`, the component `Δ'_x` of
`f⁻¹ D(b_i, 3r)` through `x` is open; `f` restricted to it is proper over the disc (preimages of
compact subsets of `D(b_i, 3r)` are compact) and onto the disc; `x` is its only point over `b_i`
and its only point with `n ≠ 1`; and every other point of the disc has exactly `n x` preimages
in `Δ'_x`.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 item 1 (B7b, B7c, B7e); Forster,
*Lectures on Riemann Surfaces*, §4 (proper holomorphic maps, multiplicity), with the local
formula `hmark` at `t = b` (`b6t_identity`). -/
theorem rf7_component_props {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C) (hx : P.f x = ((b i : ℂ) : OnePoint ℂ)) :
    IsOpen (rf7_component P.f (b i) (3 * b6t_radius b) x) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (b i) (3 * b6t_radius b) →
        IsCompact (rf7_component P.f (b i) (3 * b6t_radius b) x ∩
          P.f ⁻¹' (((↑) : ℂ → OnePoint ℂ) '' K))) ∧
      rf7_sphereBall (b i) (3 * b6t_radius b) ⊆
        P.f '' rf7_component P.f (b i) (3 * b6t_radius b) x ∧
      rf7_component P.f (b i) (3 * b6t_radius b) x ∩ P.f ⁻¹' {((b i : ℂ) : OnePoint ℂ)} = {x} ∧
      (∀ y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x, y ≠ x → P.n y = 1) ∧
      ∀ z ∈ Metric.ball (b i) (3 * b6t_radius b), z ≠ b i →
        Nat.card ↥(rf7_component P.f (b i) (3 * b6t_radius b) x ∩
          P.f ⁻¹' {((z : ℂ) : OnePoint ℂ)}) = P.n x :=
  rf7_component_props_aux P i x hx

example := @rf7_component_props

/-- **Statement 5 (B7e–B7f, base root coordinate).** For a point `x` over `b_i`, there is a chart
`u` of the base surface, in its maximal analytic atlas, with source exactly `Δ'_x`, target exactly
`{w : |w|ⁿ < 3r}`, `n = n x`, centred at `x`, and normalized so that `f = b_i + uⁿ` on `Δ'_x`.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 item 1 (B7d–B7f);
`rf3_punctured_cover_classify` on `main`; Forster, *Lectures on Riemann Surfaces*, Theorem 2.1
(local form `zⁿ`) and §5 (coverings of the punctured disc); Ahlfors, Ch. 4, Thm. 7. -/
theorem rf7_base_root {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C) (hx : P.f x = ((b i : ℂ) : OnePoint ℂ)) :
    ∃ u : OpenPartialHomeomorph C ℂ, u ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C ∧
      u.source = rf7_component P.f (b i) (3 * b6t_radius b) x ∧
      u.target = {w : ℂ | ‖w‖ ^ P.n x < 3 * b6t_radius b} ∧ u x = 0 ∧
      ∀ y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x,
        P.f y = ((b i + u y ^ P.n x : ℂ) : OnePoint ℂ) :=
  rf7_base_root_aux P i x hx

example := @rf7_base_root

/-- **Statement 6 (off-centre classifier, before B8f).** A connected Riemann surface `Y` with a
holomorphic `q : Y → D(a, ρ) ∖ {c}`, `|c − a| < ρ`, that is a covering with every fibre of
cardinality `k > 0`, has an injective holomorphic coordinate `v` with `q = c + vᵏ` and image
exactly `{w ≠ 0 : |c + wᵏ − a| < ρ}`. The punctured disc deformation retracts to a circle about
`c`, so its connected `k`-sheeted coverings are all isomorphic to `w ↦ c + wᵏ` over it.
Source: review `hlean-rev-relC` (off-centre classifier, `docs/specs/RelativeFramePlumbing.md`
on `main`); Hatcher, *Algebraic Topology*, Prop. 1.33 and Thm. 1.38; Forster, §§4–5. -/
theorem rf7_offcentre_classify {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] [ConnectedSpace Y] (a c : ℂ) (ρ : ℝ) (hc : ‖c - a‖ < ρ)
    (k : ℕ) (hk : 0 < k) (q : Y → ℂ) (hq : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) q)
    (hrange : ∀ y, q y ∈ Metric.ball a ρ \ {c})
    (hcov : IsCoveringMapOn q (Metric.ball a ρ \ {c}))
    (hdeg : ∀ z ∈ Metric.ball a ρ \ {c}, Nat.card (q ⁻¹' {z}) = k) :
    ∃ v : Y → ℂ, MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) v ∧ Function.Injective v ∧
      range v = {w : ℂ | w ≠ 0 ∧ ‖c + w ^ k - a‖ < ρ} ∧ ∀ y, q y = c + v y ^ k :=
  rf7_offcentre_classify_aux a c ρ hc k hk q hq hrange hcov hdeg

example := @rf7_offcentre_classify

/-- **Statement 7 (B8 on the total space).** For a point `x` over `b_i`, there is a function `w`
on the total space, analytic on the fixed open source `polydisc × Δ'_x`, such that for every
parameter `t`: `f_t = t_i + w_tⁿ` on `Δ'_x` (`f_t = b6a_map b f (t, ·)`); `w_t` is injective on
`Δ'_x` with image exactly `{v : |vⁿ + ε| < 3r}`, `ε = t_i − b_i`; it maps the inner piece `Δ_x`
onto the moving disc `rf4_innerDisc n ρ ε`; `w_t(x) = 0`; and on the collar `r < |f − b_i|` it is
the principal root `Φ_ε(w_b) = w_b (1 − ε w_b⁻ⁿ)^{1/n}` of the base coordinate `w_b`.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 items 2–3 (B8a–B8f, gluing);
`rf3_moving_root`, `rf3_root_differentiable` and `rf3_tent_preimage` on `main`; statement 6;
`b6a_root_transition`; Hatcher, Prop. 1.33. -/
theorem rf7_moving_root {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C) (hx : P.f x = ((b i : ℂ) : OnePoint ℂ)) :
    ∃ w : b6t_polydisc b × C → ℂ,
      ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω w
        (univ ×ˢ rf7_component P.f (b i) (3 * b6t_radius b) x) ∧
      ∀ t : b6t_polydisc b,
        (∀ y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x,
          b6a_map b P.f (t, y) = ((t.val i + w (t, y) ^ P.n x : ℂ) : OnePoint ℂ)) ∧
        InjOn (fun y ↦ w (t, y)) (rf7_component P.f (b i) (3 * b6t_radius b) x) ∧
        (fun y ↦ w (t, y)) '' rf7_component P.f (b i) (3 * b6t_radius b) x =
          {v : ℂ | ‖v ^ P.n x + (t.val i - b i)‖ < 3 * b6t_radius b} ∧
        (fun y ↦ w (t, y)) '' rf7_inner b P.f i x =
          rf4_innerDisc (P.n x) (rf7_radius b) (t.val i - b i) ∧
        w (t, x) = 0 ∧
        ∀ y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x, ∀ z : ℂ,
          P.f y = (z : OnePoint ℂ) → b6t_radius b < dist z (b i) →
            w (t, y) = rf4_rootMap (P.n x) (t.val i - b i)
              (w (⟨b, (b6t_polydisc_neighbourhood b P.hb).1⟩, y)) :=
  rf7_moving_root_aux P i x hx

example := @rf7_moving_root

/-- **Statement 8 (B7f, B10 pieces).** For an atlas package: the outer region
`O = f⁻¹(ℙ¹ ∖ ⋃ D̄(b_i, ρ))` is open and its closure stays outside the open discs `D(b_i, ρ)`;
the components `Δ'_x`, `Δ'_{x'}` of distinct marked points are disjoint; every point lies in `O`
or in an inner piece `Δ_x`; and `O ∩ Δ_x` is exactly the annulus `ρ < |f − b_i| < 2ρ` of `Δ'_x`.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 (discs, annuli) with radius `ρ`;
statements 2 and 4. -/
theorem rf7_pieces {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) :
    IsOpen (rf7_outer b P.f) ∧
      closure (rf7_outer b P.f) ⊆
        P.f ⁻¹' {p | ∀ i, p ∉ rf7_sphereBall (b i) (rf7_radius b)} ∧
      (∀ (i i' : Fin 10) (x x' : C), P.f x = ((b i : ℂ) : OnePoint ℂ) →
        P.f x' = ((b i' : ℂ) : OnePoint ℂ) → x ≠ x' →
          Disjoint (rf7_component P.f (b i) (3 * b6t_radius b) x)
            (rf7_component P.f (b i') (3 * b6t_radius b) x')) ∧
      (∀ y : C, y ∈ rf7_outer b P.f ∨
        ∃ (i : Fin 10) (x : C), P.f x = ((b i : ℂ) : OnePoint ℂ) ∧ y ∈ rf7_inner b P.f i x) ∧
      ∀ (i : Fin 10) (x : C), P.f x = ((b i : ℂ) : OnePoint ℂ) →
        rf7_outer b P.f ∩ rf7_inner b P.f i x =
          rf7_component P.f (b i) (3 * b6t_radius b) x ∩
            P.f ⁻¹' rf7_sphereAnnulus (b i) (rf7_radius b) (2 * rf7_radius b) :=
  rf7_pieces_aux P

example := @rf7_pieces

/-- **Statement 9 (B5–B6, B10 outer data).** For an atlas package, there are outer data `D` on the
base surface over the outer region `O`, of radius `ρ`, whose discs are enumerated by the points
over the moving values (`e`), with centre `b_i`, degree `n x`, and annulus chart a root coordinate
`f = b_i + uⁿ` inside `Δ'_x`; every piece chart has its source in the stationary region outside
the closed tent discs, and is analytic on the total space on its entire chart source, as
`outer_analytic` of `rf5_FamilyPlumbing` requires.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 (outer piece, stationary coordinates)
and §5, B5, B6, B10; `rf3_tent_preimage` on `main`; `b6a_root_transition`. -/
theorem rf7_outer_data {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) :
    ∃ (D : rf4_OuterData C (rf7_outer b P.f))
      (e : Fin D.m ≃ {x : C // ∃ i : Fin 10, P.f x = ((b i : ℂ) : OnePoint ℂ)})
      (idx : Fin D.m → Fin 10),
      D.r = rf7_radius b ∧
      (∀ k, P.f (e k).val = ((b (idx k) : ℂ) : OnePoint ℂ) ∧ D.c k = b (idx k) ∧
        D.deg k = P.n (e k).val) ∧
      (∀ k, (D.P.chart (D.ann k)).source ⊆
          rf7_component P.f (b (idx k)) (3 * b6t_radius b) (e k).val ∧
        ∀ y ∈ (D.P.chart (D.ann k)).source,
          P.f y = ((D.c k + D.P.chart (D.ann k) y ^ D.deg k : ℂ) : OnePoint ℂ)) ∧
      (∀ j, (D.P.chart j).source ⊆ P.f ⁻¹'
        {p | ∀ i, p ∉ ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (b i) (b6t_radius b)}) ∧
      ∀ j, ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
        (fun q : b6t_polydisc b × C ↦ D.P.chart j q.2) {q | q.2 ∈ (D.P.chart j).source} :=
  rf7_outer_data_aux P

example := @rf7_outer_data

/-! ## Satisfiable instances, non-degenerate

Every check below uses only definitions and checked repository results, never a statement of this
file, except the chain check at the end, which runs through statements 2, 4 and 7–9. The first
declarations repeat, with the prefix `rf7_`, the checked construction of
`PeriodFunctionChecks.lean:80–303` on `main` (`b64c_standard_setup`, `b64c_standard_value`,
`b64c_fillOrder`, `b64c_fill_local`, `b64c_fill_totalSpace`), which this base cannot import. -/

open HurwitzPrymRexPunct HurwitzPrymRexFill

open Set Metric Manifold Topology HurwitzPrymRexPunct HurwitzPrymRexFill

attribute [local instance] b4b_group

/-- The constructive filling can use the standard complex coordinate on the sphere.
Source: `HurwitzPrymRexFill.exists_setup`, with the identity coordinate identification. -/
private theorem rf7_standard_setup (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (u₀ : U) :
    ∃ S : Setup ℂ π, S.κ' = ContinuousLinearEquiv.refl ℂ ℂ := by
  classical
  let B := Set.range (b6_branch mr_base)
  have hB : B.Finite := Set.finite_range _
  let κ' := ContinuousLinearEquiv.refl ℂ ℂ
  obtain ⟨O, hO, hOd⟩ := hB.t2_separation
  have hex : ∀ b : B, ∃ r > 0, ball (0 : ℂ) r ⊆ Tgt κ' b.1 ∧
      ∀ z ∈ ball (0 : ℂ) r, ξY κ' b.1 z ∈ O b.1 :=
    fun b ↦ exists_radius b.1 ((hO b.1).2.mem_nhds (hO b.1).1)
  choose r hr hTgt hO' using hex
  have hmemO : ∀ b b' : B, b'.1 ∈ O b.1 → b' = b := by
    intro b b' hb'
    by_contra hne
    exact Set.disjoint_left.1 (hOd b'.2 b.2 (fun h ↦ hne (Subtype.ext h)))
      (hO b'.1).1 hb'
  have havoid : ∀ b : B, ∀ z ∈ ball (0 : ℂ) (r b), ξY κ' b.1 z ∈ B → z = 0 := by
    intro b z hz hzB
    have h1 := hmemO b ⟨_, hzB⟩ (hO' b z hz)
    have h2 : ξY κ' b.1 z = ξY κ' b.1 0 := by
      rw [ξY_zero]; exact congrArg Subtype.val h1
    exact injOn_ξY b.1 (hTgt b hz) (zero_mem_Tgt b.1) h2
  have hdisj : ∀ b b' : B, b ≠ b' → ∀ z ∈ ball (0 : ℂ) (r b),
      ∀ z' ∈ ball (0 : ℂ) (r b'), ξY κ' b.1 z ≠ ξY κ' b'.1 z' := by
    intro b b' hbb' z hz z' hz' heq
    exact Set.disjoint_left.1 (hOd b.2 b'.2 (fun h ↦ hbb' (Subtype.ext h)))
      (hO' b z hz) (heq ▸ hO' b' z' hz')
  exact ⟨⟨κ', r, hr, hTgt, havoid, hdisj, u₀, hB.isClosed⟩, rfl⟩

/-- The centred sphere coordinate is the coordinate used in the moving power model.
Source: `HurwitzPrymRexPunct.ξY`, `b6a_value`. -/
private theorem rf7_standard_value (j : Fin 13) (w : ℂ) :
    ξY (ContinuousLinearEquiv.refl ℂ ℂ) (b6_branch mr_base j) w =
      b6a_value mr_base j w := by
  fin_cases j <;>
    simp [ξY, b6_branch, Fin.append, Fin.addCases, b6a_value,
      b4cov_chartAt_coe, b4cov_chartAt_infty, b4cov_chart0_coe, b4cov_chart0_symm,
      b4cov_chartInf_apply, b4cov_chartInf_symm, b4cov_sphInv_infty]

/-- Ramification orders in the constructive filling.
Source: `HurwitzPrymRexPunct.Datum.e`. -/
private def rf7_fillOrder (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ) → ℕ :=
  Sum.elim (fun _ ↦ 1) (fun c ↦ (S.D hπ c.1).e)

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) (u : U) :
    rf7_fillOrder U π S hπ (S.ι hπ (ContinuousLinearEquiv.refl ℂ ℂ) u) = 1 := rfl

local instance rf7_fillTop (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    TopologicalSpace (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instTopologicalSpaceCC hπ _

local instance rf7_fillChart (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    ChartedSpace ℂ (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instChartedSpaceCC hπ _

local instance rf7_fillAction (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    MulAction b4b_Group (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instMulActionCC hπ _

/-- The filling charts give the branch power formulas and the stabilizer rotations.
Source: `Setup.f_eq_on_pChart`, `Setup.smul_pChart_symm`. -/
private theorem rf7_fill_local (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hκ : S.κ' = ContinuousLinearEquiv.refl ℂ ℂ)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    ∀ x (j : Fin 13), S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ) x = b6_branch mr_base j →
      ∃ P : OpenPartialHomeomorph (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) ∧ P x = 0 ∧
        (∀ y ∈ P.source, S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ) y =
          b6a_value mr_base j (P y ^ rf7_fillOrder U π S hπ x)) ∧
        ∀ g : MulAction.stabilizer b4b_Group x, ∃ ζ : ℂ,
          ζ ^ rf7_fillOrder U π S hπ x = 1 ∧
          Set.MapsTo (fun y ↦ (g : b4b_Group) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : b4b_Group) • y) = ζ * P y := by
  classical
  intro x j hx
  rcases x with u | c
  · exact False.elim ((π u).property ⟨j, hx.symm⟩)
  · let κ := ContinuousLinearEquiv.refl ℂ ℂ
    let P := chartAt ℂ (S.ofP hπ κ c)
    have hPs : P.source = (S.pChart hπ c).source := by
      change ((S.pChart hπ c).trans (κPE κ)).source = _
      simp [PartialEquiv.trans_source, κPE, κ]
    have hPt : P.target = (S.pChart hπ c).target := by
      change ((S.pChart hπ c).trans (κPE κ)).target = _
      simp [PartialEquiv.trans_target, κPE, κ]
    refine ⟨P, mem_chart_source _ _, chart_mem_atlas _ _, S.chartAt_ofP_self hπ κ c, ?_, ?_⟩
    · intro y hy
      have hy' : y ∈ (S.pChart hπ c).source := hPs ▸ hy
      have hf := S.f_eq_on_pChart hπ κ c hy'
      change c.1.val = b6_branch mr_base j at hx
      rw [hκ, hx, rf7_standard_value] at hf
      exact hf
    · intro g
      have hgc : (g : b4b_Group) • c = c := by
        have hg := g.property
        change Sum.inr ((g : b4b_Group) • c) = Sum.inr c at hg
        exact Sum.inr.inj hg
      obtain ⟨k, hk⟩ := S.exists_rot hπ (g : b4b_Group) c
      let ζ := (S.D hπ c.1).ζ ^ k
      have hζ : ζ ^ (S.D hπ c.1).e = 1 := by
        dsimp [ζ, Datum.ζ]
        rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast,
          (Complex.isPrimitiveRoot_exp _ (S.D hπ c.1).e_pos.ne').pow_eq_one, one_zpow]
      have hrot (y) (hy : y ∈ P.source) :
          (g : b4b_Group) • y = P.symm (ζ * P y) := by
        have h := S.smul_pChart_symm hπ (g : b4b_Group) c hk
          (hPt ▸ P.map_source hy)
        rw [hgc] at h
        exact (congrArg (fun z ↦ (g : b4b_Group) • z) (P.left_inv hy)).symm.trans h
      have ht (y) (hy : y ∈ P.source) : ζ * P y ∈ P.target := by
        rw [hPt]
        change ‖ζ * P y‖ ^ (S.D hπ c.1).e < S.r c.1
        rw [norm_mul, Datum.norm_ζ_pow, one_mul]
        have hyT := P.map_source hy
        rw [hPt] at hyT
        exact hyT
      refine ⟨ζ, hζ, ?_, ?_⟩
      · intro y hy
        change (g : b4b_Group) • y ∈ P.source
        rw [hrot y hy]
        exact P.map_target (ht y hy)
      · intro y hy
        rw [hrot y hy, P.right_inv (ht y hy)]


/-- The constructive filling of the marked root cover is an atlas package over `mr_base`, and
its cover carries the root marking.
Source: `mr_rootCover`, `rf7_standard_setup`, `rf7_fill_local`, `b6a_isolatedFamilyChart` and
its manifold and formula theorems (the construction of `b64c_fill_totalSpace` on `main`). -/
private theorem rf7_rootAtlas_package (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i)) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction b4b_Group C)
      (_ : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C))
      (P : rf7_HurwitzAtlas mr_base b4b_Group C),
      ∃ u₀ : P.π ⁻¹' {y₀}, ∀ i,
        P.hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i) := by
  classical
  obtain ⟨U, _, _, _, π, hπ, u₀, hmon, -⟩ := mr_rootCover y₀ γ hγ
  obtain ⟨S, hκ⟩ := rf7_standard_setup U π u₀.val
  let κ := ContinuousLinearEquiv.refl ℂ ℂ
  let C := S.CC hπ κ
  let : TopologicalSpace C := rf7_fillTop U π S hπ
  let : ChartedSpace ℂ C := rf7_fillChart U π S hπ
  let : MulAction b4b_Group C := rf7_fillAction U π S hπ
  let : IsManifold 𝓘(ℂ, ℂ) ω C := S.isManifold hπ κ
  let : T2Space C := S.instT2SpaceCC hπ κ
  let : LocallyCompactSpace (OnePoint ℂ) := ChartedSpace.locallyCompactSpace ℂ _
  let : CompactSpace C := S.instCompactSpaceCCOfLocallyCompactSpace hπ κ
  let : ConnectedSpace C := S.instConnectedSpaceCC hπ κ
  let : Nonempty U := ⟨S.u₀⟩
  let f := S.f hπ κ
  let ι := S.ι hπ κ
  let n := rf7_fillOrder U π S hπ
  have hn : ∀ x, 0 < n x := by
    rintro (u | c)
    · exact Nat.zero_lt_one
    · exact (S.D hπ c.1).e_pos
  have hunram : ∀ x, f x ∉ Set.range (b6_branch mr_base) → n x = 1 := by
    rintro (u | c) hx
    · rfl
    · exact False.elim (hx c.1.property)
  have hlocal := rf7_fill_local U π S hκ hπ
  have hf := S.contMDiff_f hπ κ
  have hgal : b4_IsGaloisCover b4b_Group f :=
    ⟨S.f_smul hπ κ, fun _ _ h ↦ S.exists_smul_of_f_eq hπ κ h⟩
  have hs : Function.Surjective f := by
    intro y
    by_cases hy : y ∈ Set.range (b6_branch mr_base)
    · exact ⟨S.ofP hπ κ ⟨⟨y, hy⟩, QuotientGroup.mk (1 : b4b_Group)⟩, rfl⟩
    · obtain ⟨u, hu⟩ := hπ.surjective ⟨y, hy⟩
      exact ⟨ι u, congrArg Subtype.val hu⟩
  have hG := S.contMDiff_smul hπ κ
  have hι := S.isOpenEmbedding_ι hπ κ
  have hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ := by
    ext x
    rcases x with u | c
    · exact ⟨fun _ ↦ (π u).property, fun _ ↦ ⟨u, rfl⟩⟩
    · exact ⟨fun ⟨u, hu⟩ ↦ False.elim (Sum.inl_ne_inr hu),
        fun h ↦ False.elim (h c.1.property)⟩
  have hproj : ∀ u, f (ι u) = π u := fun _ ↦ rfl
  have hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u := fun _ _ ↦ rfl
  let A := b6a_isolatedFamilyChart mr_base mr_base_mem_chart b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous
  have hA := b6a_mem_isolatedFamilyChart_source mr_base mr_base_mem_chart b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous
  let cs := b6a_familyChartedSpace mr_base C A hA
  let : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C) := cs
  have hm := b6a_isolatedFamilyChart_isManifold mr_base mr_base_mem_chart b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous hproj
  have hform := b6a_isolatedFamilyChart_formulas mr_base mr_base_mem_chart b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous hproj
  have hAt : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C) :=
    fun q ↦ ⟨hA q, ⟨q, rfl⟩⟩
  let P : rf7_HurwitzAtlas mr_base b4b_Group C :=
    { hb := mr_base_mem_chart, U := U, π := π, hπ := hπ, f := f, ι := ι, hf := hf,
      hgal := hgal, hsurj := hs, hact := hG, hι := hι, hrange := hrange, hproj := hproj,
      hequiv := hequiv, total_isManifold := hm, A := A, n := n, hn := hn, hA := hAt,
      hparam := hform.1, hfree := fun q hq ↦ ⟨hunram q.2 hq, hform.2.1 q hq⟩,
      hmark := hform.2.2 }
  exact ⟨C, _, _, _, _, _, _, _, cs, P, u₀, hmon⟩


/-- The branch values of a normalized configuration are distinct. -/
private theorem rf7_branch_inj {b : Fin 10 → ℂ} (hb : b ∈ b6_chart) : Function.Injective b := by
  intro i j h
  have h' : b6_branch b (Fin.castAdd 3 i) = b6_branch b (Fin.castAdd 3 j) := by
    simp [b6_branch, h]
  exact Fin.castAdd_injective _ _ (hb h')

/-- **Non-degeneracy of the package.** With the explicit loops, the marked root package exists
unconditionally; every moving value `mr_base i` has a point over it (so the premises of
statements 4, 5 and 7 are inhabited), and the cover is not trivial: every loop has nontrivial
monodromy, of order `3` or `2`. -/
example : ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction b4b_Group C)
      (_ : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C))
      (P : rf7_HurwitzAtlas mr_base b4b_Group C),
      (∀ i : Fin 10, ∃ x, P.f x = ((mr_base i : ℂ) : OnePoint ℂ)) ∧
      ∃ (y₀ : b6t_punctured mr_base) (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
        (u₀ : P.π ⁻¹' {y₀}), ∀ i, P.hπ.fundamentalGroupToMulOpposite u₀ (γ i) ≠ 1 := by
  have h0 : mr_curve 12 ((0 : unitInterval) : ℝ) = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
    simp [mr_curve, mr_outer, mr_basePoint]
  have hmem : ((mr_basePoint : ℂ) : OnePoint ℂ) ∈ b6t_punctured mr_base := by
    have h := (mr_curve_avoids mr_base (b6t_polydisc_neighbourhood mr_base
      mr_base_mem_chart).1 12 0).1
    rw [h0] at h
    exact h
  let y₀ : b6t_punctured mr_base := ⟨_, hmem⟩
  have hl := fun i ↦ (mr_loop_existsUnique mr_base (b6t_polydisc_neighbourhood mr_base
    mr_base_mem_chart).1 y₀ rfl i).exists
  obtain ⟨C, _, _, _, _, _, _, _, _, P, u₀, hmon⟩ :=
    rf7_rootAtlas_package y₀ (fun i ↦ (hl i).choose) (fun i ↦ (hl i).choose_spec)
  refine ⟨C, _, _, _, _, _, _, _, _, P, fun i ↦ P.hsurj _, y₀,
    fun i ↦ (hl i).choose, u₀, fun i h ↦ ?_⟩
  rw [hmon i] at h
  have h2 : b4b_root i = 1 := MulOpposite.op_injective (h.trans MulOpposite.op_one.symm)
  have h3 := b63_root_order i
  rw [h2, orderOf_one] at h3
  split_ifs at h3 <;> omega

/-- **Non-degeneracy of the radius bounds.** At the marked root configuration the polydisc has a
parameter whose first moving value is not zero, so `‖t_i − b_i‖ < ρ` is not the zero case. -/
example : ∃ t ∈ b6t_polydisc mr_base, t 0 - mr_base 0 ≠ 0 ∧
    ‖t 0 - mr_base 0‖ < rf7_radius mr_base := by
  have hr : 0 < b6t_radius mr_base := (b6t_discs mr_base mr_base_mem_chart).1
  refine ⟨Function.update mr_base 0 (mr_base 0 + (b6t_radius mr_base / 2 : ℝ)), ?_, ?_, ?_⟩
  · intro i
    rw [Metric.mem_ball]
    by_cases h : i = 0
    · subst h
      simp only [Function.update_self, dist_self_add_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ b6t_radius mr_base / 2)]
      linarith
    · simp [Function.update_of_ne h, hr]
  · simp only [Function.update_self, add_sub_cancel_left]
    exact_mod_cast (by positivity : (b6t_radius mr_base / 2 : ℝ) ≠ 0)
  · simp only [Function.update_self, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ b6t_radius mr_base / 2), rf7_radius]
    linarith

/-- **Chain check toward `rf5_FamilyPlumbing`.** From statements 2, 4, 7, 8 and 9, an atlas
package yields outer data `D` of radius `ρ`, disc indices and marked points, with the shapes of
the fields `ε_analytic` (moving values `t ↦ t_i − b_i`), `small`, `outer_analytic`, `wSrc_open`
and `w_analytic` (the moving root on `polydisc × Δ'_x`), the target condition `w_target`, the
image of the inner piece, and the disjointness and cover of the inner pieces over `C`. -/
example {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) :
    ∃ (D : rf4_OuterData C (rf7_outer b P.f)) (idx : Fin D.m → Fin 10) (pt : Fin D.m → C),
      AnalyticOnNhd ℂ (fun t : Fin 10 → ℂ ↦ fun k : Fin D.m ↦ t (idx k) - b (idx k))
        (b6t_polydisc b) ∧
      (∀ t ∈ b6t_polydisc b, ∀ k, ‖t (idx k) - b (idx k)‖ < D.r) ∧
      (∀ j, ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
        (fun q : b6t_polydisc b × C ↦ D.P.chart j q.2) {q | q.2 ∈ (D.P.chart j).source}) ∧
      (Pairwise fun k k' ↦ Disjoint (rf7_inner b P.f (idx k) (pt k))
        (rf7_inner b P.f (idx k') (pt k'))) ∧
      (∀ y : C, y ∈ rf7_outer b P.f ∨ ∃ k, y ∈ rf7_inner b P.f (idx k) (pt k)) ∧
      ∀ k, ∃ (wTot : b6t_polydisc b × C → ℂ) (wSrc : Set (b6t_polydisc b × C)),
        IsOpen wSrc ∧ ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω wTot wSrc ∧
        ∀ t : b6t_polydisc b,
          closure (rf4_innerDisc (D.deg k) D.r (t.val (idx k) - b (idx k))) ⊆
            (fun y ↦ wTot (t, y)) '' {y | (t, y) ∈ wSrc} ∧
          (fun y ↦ wTot (t, y)) '' rf7_inner b P.f (idx k) (pt k) =
            rf4_innerDisc (D.deg k) D.r (t.val (idx k) - b (idx k)) := by
  obtain ⟨D, e, idx, hr, hk, -, -, hout⟩ := rf7_outer_data P
  obtain ⟨-, h2ρ, -, -, -, hsmall⟩ := rf7_radius_bounds b P.hb
  obtain ⟨-, -, hdisj, hcov, -⟩ := rf7_pieces P
  refine ⟨D, idx, fun k ↦ (e k).val, ?_, ?_, hout, ?_, ?_, ?_⟩
  · intro s _
    exact AnalyticAt.pi fun k ↦ ((ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 10 ↦ ℂ) (idx k)).analyticAt s).sub analyticAt_const
  · intro t ht k
    rw [hr]
    exact hsmall t ht (idx k)
  · intro k k' hkk'
    have hne : (e k).val ≠ (e k').val := fun h ↦ hkk' (e.injective (Subtype.ext h))
    exact (hdisj _ _ _ _ (hk k).1 (hk k').1 hne).mono inter_subset_left inter_subset_left
  · intro y
    rcases hcov y with hy | ⟨i, x, hx, hy⟩
    · exact Or.inl hy
    · obtain ⟨k, hkx⟩ : ∃ k, (e k).val = x := ⟨e.symm ⟨x, i, hx⟩, by rw [e.apply_symm_apply]⟩
      refine Or.inr ⟨k, ?_⟩
      have h2 : P.f x = ((b (idx k) : ℂ) : OnePoint ℂ) := hkx ▸ (hk k).1
      have hi : idx k = i :=
        (rf7_branch_inj P.hb (OnePoint.coe_injective (hx.symm.trans h2))).symm
      change y ∈ rf7_inner b P.f (idx k) (e k).val
      rw [hi, hkx]
      exact hy
  · intro k
    obtain ⟨hfx, -, hdeg⟩ := hk k
    obtain ⟨hopen, -⟩ := rf7_component_props P (idx k) (e k).val hfx
    obtain ⟨w, hw, hwt⟩ := rf7_moving_root P (idx k) (e k).val hfx
    refine ⟨w, univ ×ˢ rf7_component P.f (b (idx k)) (3 * b6t_radius b) (e k).val,
      isOpen_univ.prod hopen, hw, fun t ↦ ⟨?_, ?_⟩⟩
    · obtain ⟨-, -, himg, -⟩ := hwt t
      have hsl : {y | (t, y) ∈ univ ×ˢ rf7_component P.f (b (idx k)) (3 * b6t_radius b)
          (e k).val} = rf7_component P.f (b (idx k)) (3 * b6t_radius b) (e k).val := by
        ext y; simp
      rw [hsl, himg, hr, hdeg]
      intro v hv
      have hle := closure_lt_subset_le (by fun_prop) continuous_const hv
      simp only [Set.mem_ofPred_eq] at hle
      change ‖v ^ P.n (e k).val + (t.val (idx k) - b (idx k))‖ < 3 * b6t_radius b
      linarith
    · obtain ⟨-, -, -, hinner, -⟩ := hwt t
      rw [hr, hdeg]
      exact hinner



/-- The preimage under squaring of the disc `D(1/2, 1)` punctured at `0`, off its centre. -/
private def rf7_offDisc : TopologicalSpace.Opens ℂ :=
  ⟨(fun v : ℂ ↦ v ^ 2) ⁻¹' (Metric.ball (1 / 2 : ℂ) 1 \ {0}),
    (Metric.isOpen_ball.sdiff isClosed_singleton).preimage (continuous_pow 2)⟩

private theorem rf7_offDisc_star : StarConvex ℝ (0 : ℂ) {v : ℂ | ‖v ^ 2 - 1 / 2‖ < 1} := by
  intro v hv a s ha hs has
  simp only [Set.mem_ofPred_eq, smul_zero, zero_add] at hv ⊢
  have hs1 : s ≤ 1 := by linarith
  have heq : (s • v) ^ 2 - 1 / 2 = ((s ^ 2 : ℝ) : ℂ) * (v ^ 2 - 1 / 2) +
      (((s ^ 2 - 1) / 2 : ℝ) : ℂ) := by
    rw [Complex.real_smul]; push_cast; ring
  rw [heq]
  have h1 := norm_add_le (((s ^ 2 : ℝ) : ℂ) * (v ^ 2 - 1 / 2)) (((s ^ 2 - 1) / 2 : ℝ) : ℂ)
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonpos (by nlinarith)] at h1
  have hN := norm_nonneg (v ^ 2 - 1 / 2)
  have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs hs1
  rcases le_or_gt ‖v ^ 2 - 1 / 2‖ (1 / 2) with h | h
  · nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg s)]
  · nlinarith [mul_le_mul_of_nonneg_right hs2 (by linarith : (0 : ℝ) ≤ ‖v ^ 2 - 1 / 2‖ - 1 / 2)]

/-- The off-centre classifier's premises hold for squaring onto the disc `D(1/2, 1)` punctured at
`0`: a connected covering of degree two, not one, with the puncture `c = 0` off the centre
`a = 1/2`. -/
example : ‖(0 : ℂ) - 1 / 2‖ < 1 ∧ ConnectedSpace rf7_offDisc ∧
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun y : rf7_offDisc ↦ (y : ℂ) ^ 2) ∧
    (∀ y : rf7_offDisc, (y : ℂ) ^ 2 ∈ Metric.ball (1 / 2 : ℂ) 1 \ {0}) ∧
    IsCoveringMapOn (fun y : rf7_offDisc ↦ (y : ℂ) ^ 2) (Metric.ball (1 / 2 : ℂ) 1 \ {0}) ∧
    ∀ z ∈ Metric.ball (1 / 2 : ℂ) 1 \ {0},
      Nat.card ((fun y : rf7_offDisc ↦ (y : ℂ) ^ 2) ⁻¹' {z}) = 2 := by
  have hS : IsOpen (Metric.ball (1 / 2 : ℂ) 1 \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
  have hmem : ∀ y : rf7_offDisc, (y : ℂ) ^ 2 ∈ Metric.ball (1 / 2 : ℂ) 1 \ {0} := fun y ↦ y.2
  refine ⟨by norm_num, ?_, ?_, hmem, ?_, ?_⟩
  · have hW : IsOpen {v : ℂ | ‖v ^ 2 - 1 / 2‖ < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    have hset : {v : ℂ | ‖v ^ 2 - 1 / 2‖ < 1} \ {0} = (rf7_offDisc : Set ℂ) := by
      ext v
      change _ ↔ v ^ 2 ∈ Metric.ball (1 / 2 : ℂ) 1 \ {0}
      simp [Metric.mem_ball, dist_eq_norm]
    have hpre : IsPreconnected ({v : ℂ | ‖v ^ 2 - 1 / 2‖ < 1} \ {0}) :=
      b4cov_isPreconnected_diff_finite hW (rf7_offDisc_star.isPathConnected (by norm_num)).isConnected.isPreconnected
        (Set.finite_singleton 0) fun s _ ↦ b4cov_goodPoint (Module.finrank_self ℂ) s
    have hne : ({v : ℂ | ‖v ^ 2 - 1 / 2‖ < 1} \ {0}).Nonempty :=
      ⟨1 / 2, by norm_num⟩
    rw [hset] at hpre hne
    exact isConnected_iff_connectedSpace.mp ⟨hne, hpre⟩
  · intro y
    have h1 : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (Subtype.val : rf7_offDisc → ℂ) y :=
      (contMDiff_subtype_val (n := ω) (I := 𝓘(ℂ, ℂ)) y).mdifferentiableAt (by simp)
    have h2 : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun v : ℂ ↦ v ^ 2) (y : ℂ) :=
      ((differentiable_pow 2) (y : ℂ)).mdifferentiableAt
    exact h2.comp y h1
  · refine IsCoveringMapOn.of_isCoveringMap_subtype hS hmem ?_
    exact ((isCoveringMapOn_npow (𝕜 := ℂ) 2 (by norm_num)).mono
      (fun z hz ↦ hz.2)).isCoveringMap_restrictPreimage
  · intro z hz
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq z two_pos
    have hz0 : z ≠ 0 := hz.2
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact hz0 hs.symm
    have hsm : ∀ v : ℂ, v ^ 2 = z → v ∈ rf7_offDisc := fun v hv ↦ by
      exact (show v ^ 2 ∈ Metric.ball (1 / 2 : ℂ) 1 \ {0} from hv ▸ hz)
    have hroots : ∀ v : ℂ, v ^ 2 = z ↔ v = s ∨ v = -s := by
      intro v; rw [← hs]; exact sq_eq_sq_iff_eq_or_eq_neg
    let f : Bool → (fun y : rf7_offDisc ↦ (y : ℂ) ^ 2) ⁻¹' {z} := fun b ↦
      ⟨⟨if b then s else -s, hsm _ (by cases b <;> simp [hs])⟩,
        by cases b <;> simp [hs]⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        have := congrArg
          (fun y : (fun y : rf7_offDisc ↦ (y : ℂ) ^ 2) ⁻¹' {z} ↦ ((y : rf7_offDisc) : ℂ)) hab
        simp only [f] at this
        cases a <;> cases b <;>
          simp only [Bool.false_eq_true, ite_true, ite_false] at this
        · rfl
        · exact absurd (by linear_combination -this / 2 : s = 0) hs0
        · exact absurd (by linear_combination this / 2 : s = 0) hs0
        · rfl
      · rintro ⟨y, hy⟩
        rcases (hroots y).mp hy with h | h
        · exact ⟨true, Subtype.ext (Subtype.ext (by simp [f, h]))⟩
        · exact ⟨false, Subtype.ext (Subtype.ext (by simp [f, h]))⟩
    rw [← Nat.card_eq_of_bijective f hf]
    simp


end HodgeLean.Foundations.Program

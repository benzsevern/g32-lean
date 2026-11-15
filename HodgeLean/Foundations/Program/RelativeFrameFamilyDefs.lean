import HodgeLean.Foundations.Program.RelativeFrameChartsDefs
import HodgeLean.Foundations.Program.HurwitzFamilyAnalytic
import HodgeLean.Foundations.Program.MarkedRootCover

/-! # The B6-2b family datum, first stage: definitions
The package of the B6-2b analytic atlas output (the conclusion of `b6a_analytic_atlas`, field
for field), the outer radius `ρ = 5r/4` of the plumbing description, discs and annuli of the
sphere, the component `Δ'_x` of the preimage of a `3r` disc through a marked point, the outer
region `O` and the inner pieces `Δ_x` over the base surface.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The B6-2b analytic atlas output over the configuration `b`, packaged with exactly the fields of
the conclusion of `b6a_analytic_atlas` (`HurwitzFamilyAnalytic.lean:121–143`): a connected Galois
`G`-cover `π` of the punctured sphere, its compact holomorphic filling `f : C → ℙ¹` with the open
embedding `ι`, an analytic manifold structure on the total space `b6t_polydisc b × C`, atlas charts
`A q` through every point preserving the parameter, positive orders `n` that are `1` off the
branch values, the unramified formula `b6a_map b f = (A q ·).2` and the branch formula
`b6a_map b f = b6a_value t j ((A q ·).2 ^ n)`. The surface `C`, its structure, the group action
and the total-space charts are parameters; nothing here is a root coordinate, a disc datum or a
form.
Source: `b6a_analytic_atlas` (Fulton, Ann. Math. 90 (1969), 542–575; Harris–Morrison,
*Moduli of Curves*, §1.G); review `hlean-rev-relC`, item B3 ("packages exactly the existing atlas
output"). -/
structure rf7_HurwitzAtlas (b : Fin 10 → ℂ) (G : Type) [Group G] [Finite G]
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)] where
  hb : b ∈ b6_chart
  U : Type
  [topU : TopologicalSpace U]
  [actU : MulAction G U]
  [connU : ConnectedSpace U]
  π : U → b6t_punctured b
  hπ : IsQuotientCoveringMap π G
  f : C → OnePoint ℂ
  ι : U → C
  hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f
  hgal : b4_IsGaloisCover G f
  hsurj : Function.Surjective f
  hact : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)
  hι : IsOpenEmbedding ι
  hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ
  hproj : ∀ u, f (ι u) = π u
  hequiv : ∀ (g : G) (u : U), ι (g • u) = g • ι u
  total_isManifold : IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)
  A : (b6t_polydisc b × C) → OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ)
  n : C → ℕ
  hn : ∀ x, 0 < n x
  hA : ∀ q, q ∈ (A q).source ∧ A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)
  hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val
  hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) → n q.2 = 1 ∧
    ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ)
  hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
    (A q q).2 = 0 ∧ ∀ y ∈ (A q).source,
      b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2)

attribute [instance] rf7_HurwitzAtlas.topU rf7_HurwitzAtlas.actU rf7_HurwitzAtlas.connU

example {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G]
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (q : b6t_polydisc b × C) :
    q ∈ (P.A q).source ∧ (P.A q q).1 = q.1.val :=
  ⟨(P.hA q).1, P.hparam q q (P.hA q).1⟩

/-- The outer radius `ρ = 5r/4`, `r = b6t_radius b`: it lies strictly between `r` and `3r/2`, so
the closed annuli `ρ ≤ |z − b_i| ≤ 2ρ` avoid the tent discs and the inner pieces of radius `2ρ`
lie in the `3r` discs.
Source: `docs/specs/RelativeFrameCharts.md`, the radius discussion (`r < ρ < 3r/2`). -/
def rf7_radius (b : Fin 10 → ℂ) : ℝ := 5 / 4 * b6t_radius b

example (b : Fin 10 → ℂ) : rf7_radius b = 5 / 4 * b6t_radius b := rfl

/-- The open disc `D(c, s)` of the plane, as a subset of the sphere.
Source: Mathlib `Metric.ball` and `OnePoint.some`. -/
def rf7_sphereBall (c : ℂ) (s : ℝ) : Set (OnePoint ℂ) :=
  ((↑) : ℂ → OnePoint ℂ) '' Metric.ball c s

example (c : ℂ) : ((c : ℂ) : OnePoint ℂ) ∈ rf7_sphereBall c 1 :=
  ⟨c, Metric.mem_ball_self one_pos, rfl⟩

/-- The open annulus `s₁ < |z − c| < s₂` of the plane, as a subset of the sphere.
Source: Mathlib `dist` and `OnePoint.some`. -/
def rf7_sphereAnnulus (c : ℂ) (s₁ s₂ : ℝ) : Set (OnePoint ℂ) :=
  ((↑) : ℂ → OnePoint ℂ) '' {z | s₁ < dist z c ∧ dist z c < s₂}

example : (((3 / 2 : ℂ)) : OnePoint ℂ) ∈ rf7_sphereAnnulus 0 1 2 :=
  ⟨3 / 2, by norm_num [Complex.dist_eq], rfl⟩

/-- The component `Δ'_x` of the preimage under `f` of the disc `D(c, s)` through `x` (for B6-2b,
`c = b_i` and `s = 3r`).
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 (discs, B7b); Mathlib
`connectedComponentIn`. -/
def rf7_component {C : Type} [TopologicalSpace C] (f : C → OnePoint ℂ) (c : ℂ) (s : ℝ) (x : C) :
    Set C :=
  connectedComponentIn (f ⁻¹' rf7_sphereBall c s) x

example {C : Type} [TopologicalSpace C] (f : C → OnePoint ℂ) (c : ℂ) (s : ℝ) (x : C) :
    rf7_component f c s x ⊆ f ⁻¹' rf7_sphereBall c s :=
  connectedComponentIn_subset _ _

/-- The outer region `O = f⁻¹(ℙ¹ ∖ ⋃ᵢ D̄(b_i, ρ))` of the plumbing description, `ρ = rf7_radius b`.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 (outer piece), with the radius `ρ` of
`docs/specs/RelativeFrameCharts.md`. -/
def rf7_outer (b : Fin 10 → ℂ) {C : Type} (f : C → OnePoint ℂ) : Set C :=
  f ⁻¹' {p | ∀ i, p ∉ ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (b i) (rf7_radius b)}

example (b : Fin 10 → ℂ) {C : Type} (f : C → OnePoint ℂ) (x : C)
    (hx : f x = OnePoint.infty) : x ∈ rf7_outer b f := by
  intro i ⟨z, _, hz⟩
  rw [hx] at hz
  exact OnePoint.coe_ne_infty z hz

/-- The inner piece `Δ_x = Δ'_x ∩ f⁻¹ D(b_i, 2ρ)` of a point `x` over `b_i`.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 (discs), with inner pieces of radius
`2ρ` (`docs/specs/RelativeFrameCharts.md`). -/
def rf7_inner (b : Fin 10 → ℂ) {C : Type} [TopologicalSpace C] (f : C → OnePoint ℂ) (i : Fin 10)
    (x : C) : Set C :=
  rf7_component f (b i) (3 * b6t_radius b) x ∩ f ⁻¹' rf7_sphereBall (b i) (2 * rf7_radius b)

example (b : Fin 10 → ℂ) {C : Type} [TopologicalSpace C] (f : C → OnePoint ℂ) (i : Fin 10)
    (x : C) : rf7_inner b f i x ⊆ rf7_component f (b i) (3 * b6t_radius b) x :=
  inter_subset_left

end HodgeLean.Foundations.Program

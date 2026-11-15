import HodgeLean.Foundations.AnalyticDivisorAlgebraic3Proofs

/-! # Regular points, transverse orders and chart independence: frozen specification
(Chow/GAGA, third stage)

Toward `LefschetzOneOneHyp` for abelian `X` through the Appell--Humbert line bundle `L(H, χ)`:
(a) the line bundle with theta-function sections, (b) the analytic divisor of a section,
(c) Chow/GAGA, (d) the cycle class of that divisor is `c₁`. The second stage
(`HodgeLean.Foundations.AnalyticDivisorAlgebraic2`) proved Osgood's lemma and closed analyticity
of `{θ = 0}` in `V`, and recommended this stage (b3): the regular part of a hypersurface, the
order of vanishing along a transverse line, and chart independence of `IsClosedAnalytic`.

Claimed:
* the analytic implicit function theorem for one equation in one unknown: near a zero `u` of
  `f : E₁ × ℂ → ℂ` analytic at `u` with `∂f/∂t (u) ≠ 0`, the zero set is the graph of a function
  analytic at `u.1`; falsification: `t² - s` has no such graph at the origin;
* on a finite-dimensional `V`: `ker φ × ℂ ≃ V`, `(k, s) ↦ k + s • v`, for `φ v ≠ 0`; near a
  regular zero `x` of `f`, in these coordinates with `φ = df(x)`, `{f = 0}` is the graph of a
  function on `ker df(x)` analytic at `0`; the singular locus `{f = 0, df = 0}` of an entire `f`
  is closed analytic;
* orders along lines `t ↦ f (x + t • v)`, with Mathlib's one-variable `analyticOrderAt`: at a zero
  `x`, the order is `1` exactly when `df(x) v ≠ 0`, and every direction has order `≥ 2` exactly
  when `df(x) = 0`; the order is unchanged by multiplying `f` with a function nonvanishing at `x`;
  falsification: at the singular point of `{z w = 0}` the order depends on the direction;
* for a theta function `θ ∈ sections D`: orders along lines are invariant under lattice
  translation, and so is the singular locus;
* on analytic manifolds (`IsManifold 𝓘(ℂ, E) ω M`): `IsClosedAnalytic` is chart independent (any
  chart of the maximal atlas gives a local description); preimages of closed analytic sets under
  holomorphic maps are closed analytic; closed analyticity descends along a map that has
  holomorphic local inverses at the points of the set (the implication from local biholomorphy);
  hence a closed set whose preimage under such a map `V → M` is the zero set of a theta function
  is closed analytic (the implication from local biholomorphy of the map); falsification: a
  real-linear homeomorphism of `ℂ²` does not preserve closed analyticity.

Not claimed: any analytic structure on `V ⧸ Λ`; that `exp : ℂ^d → X(ℂ)` satisfies the local
biholomorphy hypothesis (that is lane `unif`, not on this base); closed analyticity of the theta
divisor in `X(ℂ)` outright; Weierstrass preparation; irreducible components, multiplicities along
components, or the divisor of a theta function with multiplicities; Chow's theorem or GAGA;
algebraicity of any divisor; or any cycle class. The route and stage estimates are in
`docs/specs/AnalyticDivisorAlgebraic3.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology

open scoped Manifold ContDiff

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic3

open AppellHumbert

section Regular

/-- **Analytic implicit function theorem, one equation.**  Let `f : E₁ × ℂ → ℂ` be analytic at
`u`, with `f u = 0` and `∂f/∂t (u) = df(u)(0, 1) ≠ 0`. Then near `u` the zero set of `f` is the
graph `t = ψ s` of a function `ψ : E₁ → ℂ` analytic at `u.1`, with `ψ u.1 = u.2`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §B, Theorem 4
(implicit function theorem); Mathlib's `ContDiffAt.implicitFunction`,
`ContDiffAt.contDiffAt_implicitFunction` (smoothness class `ω`) and `ContDiffAt.analyticAt`. -/
theorem spec_exists_analytic_implicit {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [CompleteSpace E₁] {f : E₁ × ℂ → ℂ} {u : E₁ × ℂ} (hf : AnalyticAt ℂ f u) (hfu : f u = 0)
    (hreg : fderiv ℂ f u (0, 1) ≠ 0) :
    ∃ ψ : E₁ → ℂ, AnalyticAt ℂ ψ u.1 ∧ ψ u.1 = u.2 ∧
      ∀ᶠ p in 𝓝 u, (f p = 0 ↔ ψ p.1 = p.2) :=
  spec_exists_analytic_implicit_aux hf hfu hreg

example {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    {f : E₁ × ℂ → ℂ} {u : E₁ × ℂ} (hf : AnalyticAt ℂ f u) (hfu : f u = 0)
    (hreg : fderiv ℂ f u (0, 1) ≠ 0) :
    ∃ ψ : E₁ → ℂ, ContinuousAt ψ u.1 ∧ ψ u.1 = u.2 := by
  obtain ⟨ψ, hψ, hψu, -⟩ := spec_exists_analytic_implicit hf hfu hreg
  exact ⟨ψ, hψ.continuousAt, hψu⟩

/-- **Falsification for the regularity hypothesis.**  At the origin, where `∂/∂t (t² - s) = 0`,
the zero set of `t² - s` is not a graph `t = ψ s` near `(0, 0)`, for any function `ψ`: the points
`(ε², ε)` and `(ε², -ε)` are both zeros.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §B (the
implicit function theorem needs the nonvanishing partial derivative); elementary. -/
theorem spec_not_exists_implicit_sq_sub :
    ¬ ∃ ψ : ℂ → ℂ, ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), (p.2 ^ 2 - p.1 = 0 ↔ ψ p.1 = p.2) :=
  spec_not_exists_implicit_sq_sub_aux

example : ¬ ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧
    ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), (p.2 ^ 2 - p.1 = 0 ↔ ψ p.1 = p.2) :=
  fun ⟨ψ, _, h⟩ => spec_not_exists_implicit_sq_sub ⟨ψ, h⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- **Linear coordinates adapted to a hyperplane.**  On a finite-dimensional complex normed space,
for a continuous linear form `φ` and a vector `v` with `φ v ≠ 0`, the map `(k, s) ↦ k + s • v` is
a continuous linear equivalence `ker φ × ℂ ≃ V`.

Source: Halmos, *Finite-Dimensional Vector Spaces*, §19 (direct sums) and §50 (linear
functionals); Mathlib's `LinearMap.ker` and `LinearEquiv.toContinuousLinearEquiv`. -/
theorem spec_exists_prodKerEquiv (φ : V →L[ℂ] ℂ) {v : V} (hv : φ v ≠ 0) :
    ∃ e : (LinearMap.ker (φ : V →ₗ[ℂ] ℂ) × ℂ) ≃L[ℂ] V, ∀ p, e p = (p.1 : V) + p.2 • v :=
  spec_exists_prodKerEquiv_aux φ hv

example (φ : V →L[ℂ] ℂ) {v : V} (hv : φ v ≠ 0) :
    ∃ e : (LinearMap.ker (φ : V →ₗ[ℂ] ℂ) × ℂ) ≃L[ℂ] V, e (0, 1) = v := by
  obtain ⟨e, he⟩ := spec_exists_prodKerEquiv φ hv
  exact ⟨e, by simp [he]⟩

/-- **The regular part of a hypersurface is a graph.**  Let `f : V → ℂ` be analytic at a zero
`x`, and `v` a direction with `df(x) v ≠ 0`. In the coordinates `(k, s) ↦ x + k + s • v` on
`ker df(x) × ℂ`, the zero set of `f` near `x` is the graph `s = ψ k` of a function `ψ` analytic at
`0` with `ψ 0 = 0`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §B, Theorem 4
(implicit function theorem); Chirka, *Complex Analytic Sets*, §2.1 (regular points of a
hypersurface). -/
theorem spec_exists_analytic_graph {f : V → ℂ} {x v : V} (hf : AnalyticAt ℂ f x)
    (hfx : f x = 0) (hv : fderiv ℂ f x v ≠ 0) :
    ∃ ψ : LinearMap.ker (fderiv ℂ f x : V →ₗ[ℂ] ℂ) → ℂ, AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      ∀ᶠ p in 𝓝 (0 : LinearMap.ker (fderiv ℂ f x : V →ₗ[ℂ] ℂ) × ℂ),
        (f (x + (p.1 : V) + p.2 • v) = 0 ↔ ψ p.1 = p.2) :=
  spec_exists_analytic_graph_aux hf hfx hv

example {f : V → ℂ} {x v : V} (hf : AnalyticAt ℂ f x) (hfx : f x = 0)
    (hv : fderiv ℂ f x v ≠ 0) :
    ∃ ψ : LinearMap.ker (fderiv ℂ f x : V →ₗ[ℂ] ℂ) → ℂ, ContinuousAt ψ 0 ∧ ψ 0 = 0 := by
  obtain ⟨ψ, hψ, hψ0, -⟩ := spec_exists_analytic_graph hf hfx hv
  exact ⟨ψ, hψ.continuousAt, hψ0⟩

/-- **The singular locus is closed analytic.**  For an entire function `f` on a finite-dimensional
complex normed space `V`, the set `{x | f x = 0 ∧ df(x) = 0}` of singular points of its zero set
is closed analytic in `V`: it is cut out by `f` and the partial derivatives of `f`, which are
entire.

Source: Chirka, *Complex Analytic Sets*, §2.3 (singular points of a hypersurface); Gunning--Rossi,
*Analytic Functions of Several Complex Variables*, Ch. I, §A, Theorem 2 (Osgood's lemma);
with `HodgeLean.Foundations.AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn`. -/
theorem spec_isClosedAnalytic_singularLocus {f : V → ℂ} (hf : Differentiable ℂ f) :
    IsClosedAnalytic V {x | f x = 0 ∧ fderiv ℂ f x = 0} :=
  spec_isClosedAnalytic_singularLocus_aux hf

example {f : V → ℂ} (hf : Differentiable ℂ f) :
    IsClosed {x | f x = 0 ∧ fderiv ℂ f x = 0} :=
  (spec_isClosedAnalytic_singularLocus hf).isClosed

end Regular

section Order

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Transverse order one.**  Let `f : E → ℂ` be analytic at a zero `x`. Along the line
`t ↦ x + t • v`, `f` vanishes to order exactly `1` at `t = 0` if and only if `df(x) v ≠ 0`. In
particular, at a regular point every transverse direction gives order `1`.

Source: Chirka, *Complex Analytic Sets*, §2.1 (multiplicity of a hypersurface at a point, along a
line); Mathlib's `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero` and
`AnalyticAt.analyticOrderAt_deriv_add_one`. -/
theorem spec_analyticOrderAt_line_eq_one_iff {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x)
    (hfx : f x = 0) (v : E) :
    analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 = 1 ↔ fderiv ℂ f x v ≠ 0 :=
  spec_analyticOrderAt_line_eq_one_iff_aux hf hfx v

example {f : E → ℂ} {x v w : E} (hf : AnalyticAt ℂ f x) (hfx : f x = 0)
    (hv : fderiv ℂ f x v ≠ 0) (hw : fderiv ℂ f x w ≠ 0) :
    analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 =
      analyticOrderAt (fun t : ℂ => f (x + t • w)) 0 := by
  rw [(spec_analyticOrderAt_line_eq_one_iff hf hfx v).2 hv,
    (spec_analyticOrderAt_line_eq_one_iff hf hfx w).2 hw]

/-- **Singular points by orders.**  Let `f : E → ℂ` be analytic at a zero `x`. Then `f` vanishes
to order at least `2` along every line through `x` if and only if `df(x) = 0`.

Source: Chirka, *Complex Analytic Sets*, §2.1 (a point of a hypersurface is singular for the
equation exactly when its multiplicity is at least `2`); Mathlib's `analyticOrderAt_eq_zero` and
`AnalyticAt.analyticOrderAt_deriv_add_one`. -/
theorem spec_two_le_analyticOrderAt_line_iff {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x)
    (hfx : f x = 0) :
    (∀ v : E, 2 ≤ analyticOrderAt (fun t : ℂ => f (x + t • v)) 0) ↔ fderiv ℂ f x = 0 :=
  spec_two_le_analyticOrderAt_line_iff_aux hf hfx

example {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) (hfx : f x = 0) (hdf : fderiv ℂ f x = 0)
    (v : E) : 2 ≤ analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 :=
  (spec_two_le_analyticOrderAt_line_iff hf hfx).2 hdf v

/-- **Orders along lines do not see units.**  If `g` is analytic at `x` with `g x ≠ 0`, then
along any line through `x`, `g * f` and `f` vanish to the same order at `x`. So the order along a
line is a property of the hypersurface germ `{f = 0}` with its local equation up to a unit.

Source: Chirka, *Complex Analytic Sets*, §2.1; Mathlib's `analyticOrderAt_mul` and
`analyticOrderAt_eq_zero`. -/
theorem spec_analyticOrderAt_line_mul {f g : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x)
    (hg : AnalyticAt ℂ g x) (hgx : g x ≠ 0) (v : E) :
    analyticOrderAt (fun t : ℂ => g (x + t • v) * f (x + t • v)) 0 =
      analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 :=
  spec_analyticOrderAt_line_mul_aux hf hg hgx v

example {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) (v : E) :
    analyticOrderAt (fun t : ℂ => 2 * f (x + t • v)) 0 =
      analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 :=
  spec_analyticOrderAt_line_mul hf (g := fun _ => 2) analyticAt_const two_ne_zero v

/-- **Falsification: at a singular point the order depends on the direction.**  For
`f (z, w) = z w` at the origin, the order along the direction `(1, 0)` is `⊤` (the line lies in
`{f = 0}`), and along `(1, 1)` it is `2`. So direction independence of the order needs the
regular point of `spec_analyticOrderAt_line_eq_one_iff`.

Source: Chirka, *Complex Analytic Sets*, §2.1 (the multiplicity is the order along a generic
line, not along every line); elementary. -/
theorem spec_analyticOrderAt_line_depends_on_direction :
    analyticOrderAt (fun t : ℂ => (t • ((1 : ℂ), (0 : ℂ))).1 * (t • ((1 : ℂ), (0 : ℂ))).2) 0
        = ⊤ ∧
      analyticOrderAt (fun t : ℂ => (t • ((1 : ℂ), (1 : ℂ))).1 * (t • ((1 : ℂ), (1 : ℂ))).2) 0
        = 2 :=
  spec_analyticOrderAt_line_depends_on_direction_aux

example :
    analyticOrderAt (fun t : ℂ => (t • ((1 : ℂ), (0 : ℂ))).1 * (t • ((1 : ℂ), (0 : ℂ))).2) 0 ≠
      analyticOrderAt (fun t : ℂ => (t • ((1 : ℂ), (1 : ℂ))).1 * (t • ((1 : ℂ), (1 : ℂ))).2) 0 := by
  rw [spec_analyticOrderAt_line_depends_on_direction.1,
    spec_analyticOrderAt_line_depends_on_direction.2]
  exact ENat.top_ne_ofNat 2

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- **Orders of theta functions are lattice invariant.**  For a theta function `θ ∈ sections D`,
a lattice vector `l`, a point `x` and a direction `w`, the orders at `t = 0` of `θ` along the
lines `t ↦ x + l + t • w` and `t ↦ x + t • w` agree: `θ (· + l)` is `θ` times the nowhere
vanishing holomorphic factor `holFactor D l`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §3.1 and §4.1 (the divisor of a
theta function is invariant under the lattice); Mathlib's `analyticOrderAt_mul`. -/
theorem spec_analyticOrderAt_theta_line_add (D : Datum (V := V)) {θ : V → ℂ}
    (hθ : θ ∈ sections D) (l : D.lattice) (x w : V) :
    analyticOrderAt (fun t : ℂ => θ (x + l + t • w)) 0 =
      analyticOrderAt (fun t : ℂ => θ (x + t • w)) 0 :=
  spec_analyticOrderAt_theta_line_add_aux D hθ l x w

example (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D) (l : D.lattice) (w : V) :
    analyticOrderAt (fun t : ℂ => θ ((l : V) + t • w)) 0 =
      analyticOrderAt (fun t : ℂ => θ (t • w)) 0 := by
  simpa using spec_analyticOrderAt_theta_line_add D hθ l 0 w

/-- **The singular locus of a theta divisor is lattice invariant.**  For a theta function
`θ ∈ sections D` and a zero `v` of `θ`, `dθ` vanishes at `v + l` if and only if it vanishes at
`v`: differentiating `θ (w + l) = a(l, w) θ w` at `w = v` gives `dθ(v + l) = a(l, v) dθ(v)`, and
`a(l, v) ≠ 0`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §3.1 and §4.1; with
`holFactor D l` holomorphic and nowhere zero. -/
theorem spec_fderiv_theta_add_eq_zero_iff (D : Datum (V := V)) {θ : V → ℂ}
    (hθ : θ ∈ sections D) (l : D.lattice) {v : V} (hv : θ v = 0) :
    fderiv ℂ θ (v + l) = 0 ↔ fderiv ℂ θ v = 0 :=
  spec_fderiv_theta_add_eq_zero_iff_aux D hθ l hv

example (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D) (l : D.lattice) {v : V}
    (hv : θ v = 0) (hreg : fderiv ℂ θ v ≠ 0) : fderiv ℂ θ (v + l) ≠ 0 :=
  fun h => hreg ((spec_fderiv_theta_add_eq_zero_iff D hθ l hv).1 h)

end Order

section Charts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {N : Type*} [TopologicalSpace N] [ChartedSpace E' N]

/-- **Chart independence of `IsClosedAnalytic`.**  On an analytic complex manifold
(`IsManifold 𝓘(ℂ, E) ω M`), a subset `Z` is closed analytic (a definition that uses the preferred
charts) if and only if it is closed and, for every chart `e` of the maximal analytic atlas and
every `x ∈ Z ∩ e.source`, `Z` is near `x`, in the chart `e`, the common zero set of finitely many
functions analytic on an open neighbourhood of `e x`.

Source: Chirka, *Complex Analytic Sets*, §2.1 (analytic sets of a complex manifold);
Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §E, Definition 1 and
Ch. I, §A (chart transitions of an analytic manifold are holomorphic, and holomorphic maps
compose); Mathlib's `IsManifold.compatible_of_mem_maximalAtlas` and `ContDiffAt.analyticAt`. -/
theorem spec_isClosedAnalytic_iff_maximalAtlas [IsManifold 𝓘(ℂ, E) ω M] {Z : Set M} :
    IsClosedAnalytic E Z ↔ IsClosed Z ∧
      ∀ e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω M, ∀ x ∈ Z, x ∈ e.source →
        ∃ U : Set E, IsOpen U ∧ e x ∈ U ∧ U ⊆ e.target ∧
          ∃ (n : ℕ) (f : Fin n → E → ℂ), (∀ i, AnalyticOnNhd ℂ (f i) U) ∧
            ∀ z ∈ U, (e.symm z ∈ Z ↔ ∀ i, f i z = 0) :=
  spec_isClosedAnalytic_iff_maximalAtlas_aux

example [IsManifold 𝓘(ℂ, E) ω M] {Z : Set M} (hZ : IsClosedAnalytic E Z)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω M) {x : M}
    (hx : x ∈ Z) (hxe : x ∈ e.source) : ∃ U : Set E, IsOpen U ∧ e x ∈ U := by
  obtain ⟨U, hU, hxU, -⟩ := (spec_isClosedAnalytic_iff_maximalAtlas.1 hZ).2 e he x hx hxe
  exact ⟨U, hU, hxU⟩

/-- **Preimages under holomorphic maps.**  For a holomorphic map `φ : N → M` of analytic complex
manifolds (`ContMDiff … ω`) and a closed analytic `Z ⊆ M`, the preimage `φ ⁻¹' Z` is closed
analytic in `N`: near each of its points it is cut out by the local equations of `Z` composed
with `φ` in charts.

Source: Chirka, *Complex Analytic Sets*, §2.1 (inverse images of analytic sets under holomorphic
maps); Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §E. -/
theorem spec_isClosedAnalytic_preimage [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, E') ω N]
    {φ : N → M} (hφ : ContMDiff 𝓘(ℂ, E') 𝓘(ℂ, E) ω φ) {Z : Set M}
    (hZ : IsClosedAnalytic E Z) : IsClosedAnalytic E' (φ ⁻¹' Z) :=
  spec_isClosedAnalytic_preimage_aux hφ hZ

example : IsClosedAnalytic (ℂ × ℂ) ((fun p : ℂ × ℂ => p.1) ⁻¹' {0}) :=
  spec_isClosedAnalytic_preimage (ContinuousLinearMap.fst ℂ ℂ ℂ).contMDiff
    (isClosedAnalytic_singleton 0)

/-- **Descent along local biholomorphisms.**  Let `π : N → M` be a map of analytic complex
manifolds and `Z ⊆ M` closed. Suppose every point `x ∈ Z` lies in the target of an open partial
homeomorphism `e : N → M` that agrees with `π` on its source and has a holomorphic inverse on its
target. If `π ⁻¹' Z` is closed analytic in `N`, then `Z` is closed analytic in `M`: on
`e.target`, `Z` is the preimage of `π ⁻¹' Z` under the holomorphic map `e.symm`. This is the
implication from local biholomorphy of `π`; the hypothesis has the shape of lane `unif`'s
`spec_complexExponential_localBiholomorph`.

Source: Chirka, *Complex Analytic Sets*, §2.1 (analyticity is a local property, invariant under
biholomorphisms); Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §E. -/
theorem spec_isClosedAnalytic_of_localBiholomorph [IsManifold 𝓘(ℂ, E) ω M]
    [IsManifold 𝓘(ℂ, E') ω N] {π : N → M} {Z : Set M} (hZc : IsClosed Z)
    (hloc : ∀ x ∈ Z, ∃ e : OpenPartialHomeomorph N M, x ∈ e.target ∧ EqOn π e e.source ∧
      ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E') ω e.symm e.target)
    (hZ : IsClosedAnalytic E' (π ⁻¹' Z)) : IsClosedAnalytic E Z :=
  spec_isClosedAnalytic_of_localBiholomorph_aux hZc hloc hZ

example {Z : Set E} (hZ : IsClosedAnalytic E (id ⁻¹' Z)) : IsClosedAnalytic E Z :=
  spec_isClosedAnalytic_of_localBiholomorph (π := id) hZ.isClosed
    (fun _ _ => ⟨OpenPartialHomeomorph.refl E, mem_univ _, fun _ _ => rfl,
      contMDiffOn_id⟩) hZ

/-- **Theta divisors descend along local biholomorphisms.**  Let `θ ∈ sections D` be a theta
function on `V`, and `π : V → M` a map to an analytic complex manifold with holomorphic local
inverses at the points of a closed set `Z ⊆ M` (as in
`spec_isClosedAnalytic_of_localBiholomorph`). If `π ⁻¹' Z = {θ = 0}`, then `Z` is closed analytic
in `M`. This is the implication from local biholomorphy of `π`; for `π = exp : ℂ^d → X(ℂ)` the
hypothesis is lane `unif`'s, which is not on this base.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 (the divisor of a theta
function on `V ⧸ Λ`); with `HodgeLean.Foundations.AnalyticDivisorAlgebraic2.spec_isClosedAnalytic_theta`
and `spec_isClosedAnalytic_of_localBiholomorph`. -/
theorem spec_isClosedAnalytic_of_theta_preimage {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] [IsManifold 𝓘(ℂ, E) ω M] (D : Datum (V := V))
    {θ : V → ℂ} (hθ : θ ∈ sections D) {π : V → M} {Z : Set M} (hZc : IsClosed Z)
    (hloc : ∀ x ∈ Z, ∃ e : OpenPartialHomeomorph V M, x ∈ e.target ∧ EqOn π e e.source ∧
      ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, V) ω e.symm e.target)
    (hZ : π ⁻¹' Z = {v | θ v = 0}) : IsClosedAnalytic E Z :=
  spec_isClosedAnalytic_of_theta_preimage_aux D hθ hZc hloc hZ

example {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D)
    (hZc : IsClosed {v | θ v = 0}) : IsClosedAnalytic V {v | θ v = 0} :=
  spec_isClosedAnalytic_of_theta_preimage D hθ (π := id) hZc
    (fun _ _ => ⟨OpenPartialHomeomorph.refl V, mem_univ _, fun _ _ => rfl,
      contMDiffOn_id⟩) rfl

/-- **Falsification: chart independence needs analytic transitions.**  The real surface
`{w ∈ ℂ² | w₁ = Re w₂}` is not closed analytic in `ℂ²`. It is the image of the closed analytic
line `{z₁ = 0}` under the real-linear homeomorphism `(z₁, z₂) ↦ (z₁ + Re z₂, z₂)`, so closed
analyticity is not invariant under homeomorphisms, and the predicate can change when a chart is
replaced by one with a non-holomorphic transition. Its slice `w₁ = 0` is the imaginary axis of
`ℂ`, which is not analytic (`not_isClosedAnalytic_re_eq_zero`).

Source: Chirka, *Complex Analytic Sets*, §2.1; `HodgeLean.Foundations.not_isClosedAnalytic_re_eq_zero`
(`AnalyticSubset.lean`). -/
theorem spec_not_isClosedAnalytic_graph_re :
    ¬ IsClosedAnalytic (ℂ × ℂ) {w : ℂ × ℂ | w.1 = (w.2.re : ℂ)} :=
  spec_not_isClosedAnalytic_graph_re_aux

example : IsClosed {w : ℂ × ℂ | w.1 = (w.2.re : ℂ)} ∧
    ¬ IsClosedAnalytic (ℂ × ℂ) {w : ℂ × ℂ | w.1 = (w.2.re : ℂ)} :=
  ⟨isClosed_eq continuous_fst (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp continuous_snd)), spec_not_isClosedAnalytic_graph_re⟩

end Charts

end HodgeLean.Foundations.AnalyticDivisorAlgebraic3

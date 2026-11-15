import HodgeLean.Foundations.Program.HurwitzTransportProofs

/-! # B6-2a: topological transport of Hurwitz covers

Implication from a normalized configuration and, for covering statements, an existing
finite-group quotient covering to local topological transport. Analytic family charts,
ramification filling, and comparison to selected compact fibres are later tasks.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.Program

/-- The ten finite branch discs have positive radius, avoid zero and one, and are disjoint.
Source: Reciprocal-distance bound in `b6t_radius`; triangle inequality. -/
theorem b6t_discs (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    0 < b6t_radius b ∧
      (∀ i : Fin 10, (0 : ℂ) ∉ Metric.closedBall (b i) (b6t_radius b) ∧
        (1 : ℂ) ∉ Metric.closedBall (b i) (b6t_radius b)) ∧
      Pairwise (fun i j : Fin 10 ↦ Disjoint
        (Metric.closedBall (b i) (b6t_radius b))
        (Metric.closedBall (b j) (b6t_radius b))) :=
  b6t_discs_aux b hb

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    0 < b6t_radius b ∧
      (∀ i : Fin 10, (0 : ℂ) ∉ Metric.closedBall (b i) (b6t_radius b) ∧
        (1 : ℂ) ∉ Metric.closedBall (b i) (b6t_radius b)) ∧
      Pairwise (fun i j : Fin 10 ↦ Disjoint
        (Metric.closedBall (b i) (b6t_radius b))
        (Metric.closedBall (b j) (b6t_radius b))) :=
  b6t_discs b hb

/-- The product of disc interiors is an open neighbourhood in the normalized chart.
Source: Mathlib finite product topology and `b6_chart_coordinates`. -/
theorem b6t_polydisc_neighbourhood (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    b ∈ b6t_polydisc b ∧ (b6t_polydisc b).Nonempty ∧
      IsOpen (b6t_polydisc b) ∧ b6t_polydisc b ⊆ b6_chart :=
  b6t_polydisc_neighbourhood_aux b hb

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    b ∈ b6t_polydisc b ∧ (b6t_polydisc b).Nonempty ∧
      IsOpen (b6t_polydisc b) ∧ b6t_polydisc b ⊆ b6_chart :=
  b6t_polydisc_neighbourhood b hb

/-- The explicit radial push is the underlying map of a sphere homeomorphism.
Source: Tent displacement with Lipschitz constant less than one on each disc; contraction inverse. -/
theorem b6t_homeomorph (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    ∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ, ∀ x, e x = b6t_sphere b t x :=
  b6t_homeomorph_aux b hb t ht

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    ∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ, ∀ x, e x = b6t_sphere b t x :=
  b6t_homeomorph b hb t ht

/-- The radial push fixes the normalized marks and the exterior of all branch discs.
Source: The zero set of the tent function in `b6t_plane`; `OnePoint.map`. -/
theorem b6t_fixed (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    b6t_sphere b t ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) ∧
      b6t_sphere b t ((1 : ℂ) : OnePoint ℂ) = ((1 : ℂ) : OnePoint ℂ) ∧
      b6t_sphere b t OnePoint.infty = OnePoint.infty ∧
      ∀ x : OnePoint ℂ,
        x ∉ ⋃ i : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
          Metric.closedBall (b i) (b6t_radius b) → b6t_sphere b t x = x :=
  b6t_fixed_aux b hb t ht

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    b6t_sphere b t ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) ∧
      b6t_sphere b t ((1 : ℂ) : OnePoint ℂ) = ((1 : ℂ) : OnePoint ℂ) ∧
      b6t_sphere b t OnePoint.infty = OnePoint.infty ∧
      ∀ x : OnePoint ℂ,
        x ∉ ⋃ i : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
          Metric.closedBall (b i) (b6t_radius b) → b6t_sphere b t x = x :=
  b6t_fixed b hb t ht

/-- Each ordered mark is carried to its corresponding target mark.
Source: The tent value at its centre is one and all other supports are disjoint. -/
theorem b6t_marks (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    ∀ j : Fin 13, b6t_sphere b t (b6_branch b j) = b6_branch t j :=
  b6t_marks_aux b hb t ht

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    ∀ j : Fin 13, b6t_sphere b t (b6_branch b j) = b6_branch t j :=
  b6t_marks b hb t ht

/-- The explicit sphere map is jointly continuous in the parameter and the sphere point.
Source: Continuity of finite sums and tents; the map is the identity off a fixed compact set. -/
theorem b6t_continuous (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    Continuous (fun p : b6t_polydisc b × OnePoint ℂ ↦
      b6t_sphere b p.1.val p.2) :=
  b6t_continuous_aux b hb

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    Continuous (fun p : b6t_polydisc b × OnePoint ℂ ↦
      b6t_sphere b p.1.val p.2) :=
  b6t_continuous b hb

/-- At the central parameter the radial displacement is the identity.
Source: Vanishing displacement vectors in `b6t_plane`. -/
theorem b6t_identity (b : Fin 10 → ℂ) :
    b6t_sphere b b = id :=
  b6t_identity_aux b

example (b : Fin 10 → ℂ) :
    b6t_sphere b b = id :=
  b6t_identity b

/-- The same formula restricts to a homeomorphism of the punctured spheres.
Source: Restriction of a homeomorphism carrying the ordered marks bijectively. -/
theorem b6t_punctured_homeomorph (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    ∃ e : b6t_punctured b ≃ₜ b6t_punctured t,
      ∀ x, (e x : OnePoint ℂ) = b6t_sphere b t x :=
  b6t_punctured_homeomorph_aux b hb t ht

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    ∃ e : b6t_punctured b ≃ₜ b6t_punctured t,
      ∀ x, (e x : OnePoint ℂ) = b6t_sphere b t x :=
  b6t_punctured_homeomorph b hb t ht

/-- Transport keeps the total space and action, with an equivariant identity and the prescribed projection.
Source: Mathlib `IsQuotientCoveringMap.homeomorph_comp` and `map_smul`; B4 covering interface. -/
theorem b6t_cover (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) (G : Type) [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G) :
    ∃ e : b6t_punctured b ≃ₜ b6t_punctured t,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere b t x) ∧
      IsQuotientCoveringMap (e ∘ π) G ∧
      (∀ u, ((e ∘ π) u : OnePoint ℂ) = b6t_projection b t π u) ∧
      (∀ a : G, ∀ u : U, b6t_projection b t π (a • u) = b6t_projection b t π u) ∧
      (∀ a : G, ∀ u : U, (Homeomorph.refl U) (a • u) = a • (Homeomorph.refl U) u) :=
  b6t_cover_aux b hb t ht G U π hπ

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) (G : Type) [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G) :
    ∃ e : b6t_punctured b ≃ₜ b6t_punctured t,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere b t x) ∧
      IsQuotientCoveringMap (e ∘ π) G ∧
      (∀ u, ((e ∘ π) u : OnePoint ℂ) = b6t_projection b t π u) ∧
      (∀ a : G, ∀ u : U, b6t_projection b t π (a • u) = b6t_projection b t π u) ∧
      (∀ a : G, ∀ u : U, (Homeomorph.refl U) (a • u) = a • (Homeomorph.refl U) u) :=
  b6t_cover b hb t ht G U π hπ

/-- The full based monodromy homomorphism is unchanged through the induced fundamental-group map.
Source: Mathlib `fundamentalGroupToMulOpposite_apply_mk_eq`; B4 `fundamentalGroupToMulOpposite_eq`. -/
theorem b6t_monodromy (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) (G : Type) [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G) (x₀ : b6t_punctured b) (u₀ : π ⁻¹' {x₀})
    (hx₀ : (x₀ : OnePoint ℂ) ∉ ⋃ i : Fin 10, ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (b i) (b6t_radius b)) :
    ∃ e : b6t_punctured b ≃ₜ b6t_punctured t,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere b t x) ∧
      (e x₀ : OnePoint ℂ) = x₀ ∧
      ((hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
        ⟨u₀.val, congrArg e u₀.property⟩).comp
        (FundamentalGroup.map ⟨e, e.continuous⟩ x₀) =
        hπ.fundamentalGroupToMulOpposite u₀ :=
  b6t_monodromy_aux b hb t ht G U π hπ x₀ u₀ hx₀

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) (G : Type) [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G) (x₀ : b6t_punctured b) (u₀ : π ⁻¹' {x₀})
    (hx₀ : (x₀ : OnePoint ℂ) ∉ ⋃ i : Fin 10, ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (b i) (b6t_radius b)) :
    ∃ e : b6t_punctured b ≃ₜ b6t_punctured t,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere b t x) ∧
      (e x₀ : OnePoint ℂ) = x₀ ∧
      ((hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
        ⟨u₀.val, congrArg e u₀.property⟩).comp
        (FundamentalGroup.map ⟨e, e.continuous⟩ x₀) =
        hπ.fundamentalGroupToMulOpposite u₀ :=
  b6t_monodromy b hb t ht G U π hπ x₀ u₀ hx₀

end HodgeLean.Foundations.Program

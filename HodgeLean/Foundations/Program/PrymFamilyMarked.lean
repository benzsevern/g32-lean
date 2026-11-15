import HodgeLean.Foundations.Program.PrymFamilyMarkedProofs

/-! # B6-3g, part 5: the marked Prym family on the marked root cover (FROZEN SPEC)

Each public theorem is the matching `_aux` theorem of `PrymFamilyMarkedProofs.lean`.

**Claimed.** Implications from the marked root cover of `MarkedRootCover.lean` (a connected
Galois `b4b_Group`-cover of the punctured sphere at `mr_base` whose based monodromy sends the
explicit loop `mr_curve i` to `op (b4b_root i)`, with its compact holomorphic filling `f : C → ℙ¹`)
to the fibre hypotheses that the B6-3 statements take at every parameter `t` of a set
`V ⊆ b6t_polydisc mr_base`, on the B6-2 family of filled fibres `b63l_parameterFibre mr_base C V hV t`:
the fibres carry a complex structure with holomorphic projection and deck maps
(`b63g5_fibre_structure`); each fibre is a filling of the transported cover
(`b63g5_fibre_filling`), a surjective Galois cover free off the marks of `t`
(`b63g5_fibre_galois`), with branch set the marks of `t` (`b63g5_fibre_branch`); the explicit
loops lift with endpoint `b4b_root i •` start in every fibre (`b63g5_fibre_lift`, the marking
along the family); and every fibre carries the rotation data of `b4b_root`
(`b63g5_fibre_rot`). The first four hold for a general base `b` of the chart.

With parts 1–3 these give the fields of `g32h_PrymFamily` with `S := V`, `tuple t :=
b63g5_tuple` (the marked tuple `b4b_root`, the same at every `t`) and `fiber t := b63g5_fiber …
t`: `tuple_nielsen` (`b63d_root_nielsen`), `dim_eq`, `hodge`, `nondegenerate` and `rosati`
(chain checks below, all fibres at once), on the actual marked root cover (instance check below).

**Not claimed.** The field `positive` waits for part 4 (`PolarizationPositive` of the model class,
after the sign comparison of the part 1 review); it is a named obligation, and the assembly check
below takes exactly that field as its one extra input. The rational variation of Hodge structure
`d1_PolarizedVHS` over `V` waits for part 6, which needs `b63e_polarized_variation`. No
identification of `b6_Cover` with the marked root cover, no marking outside
`b6t_polydisc mr_base`, no discriminant, algebraicity of Weil classes or dominance.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.AppellHumbert HodgeLean.Papers
open TopologicalSpace
open scoped TensorProduct Manifold ContDiff

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-! ## The filled fibres of the marked family -/

/-- **The filled fibres carry their complex structure.** For a compact holomorphic Galois
filling `f : C → ℙ¹` at `b` with holomorphic deck maps, every filled fibre at a parameter `t` of
the polydisc has a complex-analytic atlas for which the moving projection `b6t_sphere b t ∘ f` and
every deck map are holomorphic. Off the ramification points the projection is a local
homeomorphism and the atlas is the pullback of the sphere's; at a ramification point the punctured
neighbourhood is a finite cyclic covering of a punctured disc, filled by a root chart; the deck
maps commute with the projection and are holomorphic off a finite set, hence holomorphic.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorems 4.22 and 8.4 (complex structure
on a covering and its filling) and Theorem 8.5 (uniqueness); Riemann's removable singularity
theorem; `b6a_fibre_geometry` (the same structure built from a common atlas). -/
theorem b63g5_fibre_structure (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover b4b_Group f)
    (hact : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    ∃ (_ : ChartedSpace ℂ (b63l_parameterFibre b C V hV t))
      (_ : IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t) ∧
      ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
        (fun x : b63l_parameterFibre b C V hV t ↦ g • x) :=
  b63g5_fibre_structure_aux b hb C f hf hgal hact V hV t

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover b4b_Group f)
    (hact : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    ∃ (_ : ChartedSpace ℂ (b63l_parameterFibre b C V hV t))
      (_ : IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t) ∧
      ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
        (fun x : b63l_parameterFibre b C V hV t ↦ g • x) :=
  b63g5_fibre_structure b hb C f hf hgal hact V hV t

/-- **The filled fibre is a filling of the transported cover.** If `ι : U → C` is an open
embedding onto the complement of the marks of `b`, then `u ↦ (t, ι u)` is an open embedding of
`U` into the filled fibre at `t` onto the complement of the marks of `t`. The radial
homeomorphism `b6t_sphere b t` sends the mark `b6_branch b j` to `b6_branch t j` and is a
bijection of the sphere; `b6m_coordinate` is a homeomorphism. With `f ∘ ι = π` the projection on
the image is `b6t_projection b t π` (example in the definitions), so these are the hypotheses
`hι`, `hr`, `hp` of `b6m_fibre_marking` for the filled fibre.
Source: `b6t_sphere`, `b6t_fixed`, `b6m_coordinate`; Harris–Morrison, *Moduli of Curves*, §1.G;
Fulton, Ann. Math. 90 (1969), 542–575. -/
theorem b63g5_fibre_filling (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) {U C : Type} [TopologicalSpace U]
    [TopologicalSpace C] (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    Topology.IsOpenEmbedding (b63g5_fibreMap b ι V hV t) ∧
      Set.range (b63g5_fibreMap b ι V hV t) =
        b63d_projection b C f V hV t ⁻¹' (Set.range (b6_branch t.val))ᶜ :=
  b63g5_fibre_filling_aux b hb f ι hι hrange V hV t

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) {U C : Type} [TopologicalSpace U]
    [TopologicalSpace C] (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    Topology.IsOpenEmbedding (b63g5_fibreMap b ι V hV t) ∧
      Set.range (b63g5_fibreMap b ι V hV t) =
        b63d_projection b C f V hV t ⁻¹' (Set.range (b6_branch t.val))ᶜ :=
  b63g5_fibre_filling b hb f ι hι hrange V hV t

/-- **Each filled fibre is a Galois cover, free off the marks.** If `f` is a surjective Galois
`G`-cover whose action is free off the marks of `b`, then at every parameter `t` of the polydisc
the moving projection `b6t_sphere b t ∘ f` of the filled fibre is a surjective Galois cover whose
action is free off the marks of `t`. The deck action is `g` on the second coordinate, and
`b6t_sphere b t` is a bijection of the sphere that carries the marks of `b` onto those of `t`.
Source: `b6t_sphere`, `b6t_fixed`, `b63l_fibreAction`; Forster, GTM 81, §4 (Galois coverings). -/
theorem b63g5_fibre_galois (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (C : Type) [MulAction b4b_Group C]
    (f : C → OnePoint ℂ) (hgal : b4_IsGaloisCover b4b_Group f) (hsurj : Function.Surjective f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch b) → MulAction.stabilizer b4b_Group x = ⊥)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t) ∧
      Function.Surjective (b63d_projection b C f V hV t) ∧
      ∀ x, b63d_projection b C f V hV t x ∉ Set.range (b6_branch t.val) →
        MulAction.stabilizer b4b_Group x = ⊥ :=
  b63g5_fibre_galois_aux b hb C f hgal hsurj hfree V hV t

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (C : Type) [MulAction b4b_Group C]
    (f : C → OnePoint ℂ) (hgal : b4_IsGaloisCover b4b_Group f) (hsurj : Function.Surjective f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch b) → MulAction.stabilizer b4b_Group x = ⊥)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t) ∧
      Function.Surjective (b63d_projection b C f V hV t) ∧
      ∀ x, b63d_projection b C f V hV t x ∉ Set.range (b6_branch t.val) →
        MulAction.stabilizer b4b_Group x = ⊥ :=
  b63g5_fibre_galois b hb C f hgal hsurj hfree V hV t

/-- **The branch set of each filled fibre is the marks of its parameter.** Let `f` be a surjective
Galois cover with a faithful action, free off the marks of `b`, and with a point of nontrivial
stabilizer over each mark. For any complex structure on the filled fibre at `t` making the
projection and the deck maps holomorphic, the branch set of the projection is exactly the
thirteen marks of `t`. For a holomorphic Galois cover by a finite group the ramification index
at `x` is the order of the stabilizer of `x` (the projection is locally the quotient by the
stabilizer, which acts as a rotation group), stabilizers are those of the base filling, and the
radial homeomorphism carries the marks of `b` onto those of `t`.
Source: Forster, GTM 81, Theorem 2.1 (local normal form) and §4; Miranda, *Algebraic Curves
and Riemann Surfaces*, Ch. III, Proposition 3.1 (stabilizers are cyclic and act by rotations). -/
theorem b63g5_fibre_branch (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (C : Type) [TopologicalSpace C]
    [T2Space C] [ConnectedSpace C] [MulAction b4b_Group C] [FaithfulSMul b4b_Group C]
    (f : C → OnePoint ℂ) (hgal : b4_IsGaloisCover b4b_Group f) (hsurj : Function.Surjective f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch b) → MulAction.stabilizer b4b_Group x = ⊥)
    (hstab : ∀ j : Fin 13, ∃ x, f x = b6_branch b j ∧ MulAction.stabilizer b4b_Group x ≠ ⊥)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x)) :
    b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val) :=
  b63g5_fibre_branch_aux b hb C f hgal hsurj hfree hstab V hV t hk hG

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (C : Type) [TopologicalSpace C]
    [T2Space C] [ConnectedSpace C] [MulAction b4b_Group C] [FaithfulSMul b4b_Group C]
    (f : C → OnePoint ℂ) (hgal : b4_IsGaloisCover b4b_Group f) (hsurj : Function.Surjective f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch b) → MulAction.stabilizer b4b_Group x = ⊥)
    (hstab : ∀ j : Fin 13, ∃ x, f x = b6_branch b j ∧ MulAction.stabilizer b4b_Group x ≠ ⊥)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x)) :
    b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val) :=
  b63g5_fibre_branch b hb C f hgal hsurj hfree hstab V hV t hk hG

/-- **The marking along the family.** For the marked root cover (`mr_rootCover`: based monodromy
`op (b4b_root i)` on the explicit loop `γ i` at `mr_base`), at every parameter `t` of the
polydisc the explicit curve `mr_curve i` lifts to the filled fibre at `t`, starting at the
embedded marked point `(t, ι u₀)` and ending at `b4b_root i • (t, ι u₀)`. The curves avoid the
branch discs, so `b6t_sphere mr_base t` fixes them (`mr_curve_avoids`, `b6t_fixed`); the lift of
the representing path in `U` from `u₀` ends at `b4b_root i • u₀` (`hroot` and Mathlib's
`fundamentalGroupToMulOpposite_apply_eq_iff`); `ι` is equivariant. This is the endpoint
convention `Γ 1 = gᵢ • Γ 0` of `MarkedRootCover.md`, so the tuple `b63g5_tuple` is the based
monodromy of every fibre along the same ordered loops.
Source: `mr_rootCover_family`, `mr_loop_transport`, `mr_curve_avoids`, `b6t_fixed`; Hatcher,
*Algebraic Topology*, Proposition 1.30 (path lifting) and Proposition 1.33. -/
theorem b63g5_fibre_lift (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [MulAction b4b_Group C] (f : C → OnePoint ℂ) (ι : U → C)
    (hι : Continuous ι) (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V) (i : Fin 13) :
    ∃ Γ : C(unitInterval, b63l_parameterFibre mr_base C V hV t),
      Γ 0 = b63g5_fibreMap mr_base ι V hV t u₀ ∧
      (∀ s : unitInterval, b63d_projection mr_base C f V hV t (Γ s) = mr_curve i s) ∧
      Γ 1 = b4b_root i • Γ 0 :=
  b63g5_fibre_lift_aux U π hπ y₀ u₀ γ hγ hroot C f ι hι hproj hequiv V hV t i

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [MulAction b4b_Group C] (f : C → OnePoint ℂ) (ι : U → C)
    (hι : Continuous ι) (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V) (i : Fin 13) :
    ∃ Γ : C(unitInterval, b63l_parameterFibre mr_base C V hV t),
      Γ 0 = b63g5_fibreMap mr_base ι V hV t u₀ ∧
      (∀ s : unitInterval, b63d_projection mr_base C f V hV t (Γ s) = mr_curve i s) ∧
      Γ 1 = b4b_root i • Γ 0 :=
  b63g5_fibre_lift U π hπ y₀ u₀ γ hγ hroot C f ι hι hproj hequiv V hV t i

/-- **The marked rotation data at every fibre.** For the marked root cover and any complex
structure on the filled fibre at `t` making the projection and the deck maps holomorphic, over
each mark `b6_branch t i` there is a point at which `b4b_root i` is the rotation generator
(`z ↦ e^{2πi/n} z`). This is the hypothesis `hrot` of `b63d_lattice_rank`, `b63d_chevalleyWeil_hodge`
and `b63g2_eigen_rank` at `t`. It follows from `b63g5_fibre_lift` (the lift of the explicit loop
`i` ends at `b4b_root i •` its start), `b63g5_fibre_galois` and the positivity of the explicit
loops `mr_loops_positive` at `t`; a check in this file carries out that derivation.
Source: `mr_loops_positive`, `b63g5_fibre_lift`, `b63g5_fibre_galois`; Forster, GTM 81,
Theorem 4.23 and §5; Miranda, Ch. III, Proposition 3.1. -/
theorem b63g5_fibre_rot (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] [FaithfulSMul b4b_Group C] (f : C → OnePoint ℂ) (ι : U → C)
    (hι : Continuous ι) (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (hgal : b4_IsGaloisCover b4b_Group f) (hsurj : Function.Surjective f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre mr_base C V hV t ↦ g • x)) :
    ∀ i : Fin 13, ∃ x : b63l_parameterFibre mr_base C V hV t,
      b63d_projection mr_base C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i) :=
  b63g5_fibre_rot_aux U π hπ y₀ u₀ γ hγ hroot C f ι hι hproj hequiv hgal hsurj hfree V hV t hk hG

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] [FaithfulSMul b4b_Group C] (f : C → OnePoint ℂ) (ι : U → C)
    (hι : Continuous ι) (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (hgal : b4_IsGaloisCover b4b_Group f) (hsurj : Function.Surjective f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre mr_base C V hV t ↦ g • x)) :
    ∀ i : Fin 13, ∃ x : b63l_parameterFibre mr_base C V hV t,
      b63d_projection mr_base C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i) :=
  b63g5_fibre_rot U π hπ y₀ u₀ γ hγ hroot C f ι hι hproj hequiv hgal hsurj hfree V hV t hk hG

/-! ## The marking gives the rotation data

The rotation data `b63g5_fibre_rot` at `t` follow from the marking `b63g5_fibre_lift`, the Galois
statement `b63g5_fibre_galois` and the positivity `mr_loops_positive` of the explicit loops at
`t`: the marking is what fixes the tuple `b4b_root` itself, not only its conjugacy classes. -/

/-- **Derivation of `b63g5_fibre_rot`** from `b63g5_fibre_lift`, `b63g5_fibre_galois`,
`mr_loop_existsUnique` and `mr_loops_positive`. -/
example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] [FaithfulSMul b4b_Group C] (f : C → OnePoint ℂ) (ι : U → C)
    (hι : Continuous ι) (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (hgal : b4_IsGaloisCover b4b_Group f) (hsurj : Function.Surjective f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre mr_base C V hV t ↦ g • x)) :
    ∀ i : Fin 13, ∃ x : b63l_parameterFibre mr_base C V hV t,
      b63d_projection mr_base C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i) := by
  intro i
  have hb : mr_base ∈ b6_chart := mr_base_mem_chart
  have ht : t.val ∈ b6t_polydisc mr_base := hV t.property
  have h0 : mr_curve 12 ((0 : unitInterval) : ℝ) = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
    simp [mr_curve, mr_outer, mr_basePoint]
  have hmem : ((mr_basePoint : ℂ) : OnePoint ℂ) ∈ b6t_punctured t.val := by
    have h := (mr_curve_avoids t.val ht 12 0).1
    rw [h0] at h
    exact h
  let y₁ : b6t_punctured t.val := ⟨_, hmem⟩
  have hex := fun j : Fin 13 ↦ (mr_loop_existsUnique t.val ht y₁ rfl j).exists
  choose γ' hγ' using hex
  obtain ⟨c, hc, hcγ⟩ := hγ' i
  obtain ⟨Γ, -, hΓ, hΓ1⟩ :=
    b63g5_fibre_lift U π hπ y₀ u₀ γ hγ hroot C f ι hι hproj hequiv V hV t i
  obtain ⟨hgal', -, hfree'⟩ := b63g5_fibre_galois mr_base hb C f hgal hsurj hfree V hV t
  exact mr_loops_positive t.val ht y₁ γ' hγ' (b63l_parameterFibre mr_base C V hV t) b4b_Group
    hG (b63d_projection mr_base C f V hV t) hk hgal' hfree' i c hcγ Γ (b4b_root i)
    (fun s ↦ (hΓ s).trans (hc s).symm) hΓ1

/-! ## Chain checks toward the fields of `g32h_PrymFamily`

The binders below are the marked root cover (the conclusion of `mr_rootCover`), the B6-3 fibre
data (complex structures on the filled fibres, period comparisons, intersection forms) and a
rank-twelve basis of the reference lattice `Λ_{s₀}` (as `b63d_lattice_rank` supplies). -/

/-- **The fields `tuple_nielsen`, `dim_eq`, `hodge`, `nondegenerate` and `rosati`** of the marked
family, at every parameter `t` of `V`, with `tuple t := b63g5_tuple` and
`fiber t := b63g5_fiber … t`. The fibre hypotheses at `t` of `b63g2_eigen_rank` come from
`b63g5_fibre_galois`, `b63g5_fibre_branch` and `b63g5_fibre_rot`. -/
example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] [FaithfulSMul b4b_Group C] (f : C → OnePoint ℂ) (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hgal : b4_IsGaloisCover b4b_Group f)
    (hsurj : Function.Surjective f)
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (hι : Continuous ι) (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥)
    (hrot₀ : ∀ j, ∃ x, f x = b6_branch mr_base j ∧ b4_IsRotGen ℂ x (b4b_root j))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre mr_base C V hV t ↦ g • x))
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ
      (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s₀ : V) (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice mr_base C hC V hV s₀))
    (t : V) :
    let X := b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP
      s₀ B t
    g32h_Nielsen b63g5_tuple ∧
      (dim X.X.left : ℤ) = g32h_multCW b63g5_tuple ∧
      (((g32h_h10 X : ℝ) = g32h_holoCW b63g5_tuple ∧
          (g32h_h01 X : ℝ) = g32h_multCW b63g5_tuple - g32h_holoCW b63g5_tuple) ∨
        ((g32h_h01 X : ℝ) = g32h_holoCW b63g5_tuple ∧
          (g32h_h10 X : ℝ) = g32h_multCW b63g5_tuple - g32h_holoCW b63g5_tuple)) ∧
      IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X.X) X.pol) ∧
      (letI := (torusCohomology_cupProductOf X.X).finite
       IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf X.X) X.pol) X.W.J) := by
  intro X
  have hb : mr_base ∈ b6_chart := mr_base_mem_chart
  let _ : Module.Free ℤ (b63l_parameterLattice mr_base C hC V hV s₀) := Module.Free.of_basis B
  let _ : Module.Finite ℤ (b63l_parameterLattice mr_base C hC V hV s₀) := Module.Finite.of_basis B
  have W := b63e_weight_one_riemann mr_base C hC V hV hG hb f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ t
  have hsq := b63g2_operator_sq mr_base C hC V hV s₀ (hG s₀)
  have hφ := b63g2_operator_filtration mr_base C hC V hV hG P hP s₀ t
  have hX : X = b63g2_sixfold _ _ W.1 _ W.2 _ hsq hφ := rfl
  obtain ⟨hgal', hs', hfree'⟩ := b63g5_fibre_galois mr_base hb C f hgal hsurj hfree V hV t
  have hstab : ∀ j : Fin 13, ∃ x, f x = b6_branch mr_base j ∧
      MulAction.stabilizer b4b_Group x ≠ ⊥ := by
    intro j
    obtain ⟨x, hx, hrx⟩ := hrot₀ j
    refine ⟨x, hx, fun h ↦ ?_⟩
    have hmem : b4b_root j ∈ MulAction.stabilizer b4b_Group x := hrx.1
    rw [h, Subgroup.mem_bot] at hmem
    have h3 := b63_root_order j
    rw [hmem, orderOf_one] at h3
    split_ifs at h3 <;> omega
  have hbranch := b63g5_fibre_branch mr_base hb C f hgal hsurj hfree hstab V hV t (hk t) (hG t)
  have hrot := b63g5_fibre_rot U π hπ y₀ u₀ γ hγ hroot C f ι hι hproj hequiv hgal hsurj hfree
    V hV t (hk t) (hG t)
  have hE := b63g2_eigen_rank mr_base C hC V hV hG P hP s₀ t hb f (hk t) hs' hgal' hbranch hrot
  have h10 : g32h_h10 X = 3 := by
    have h := (b63g2_sixfold_h10 _ _ W.1 _ W.2 _ hsq hφ).trans
      (b63g2_weil_h10 _ _ W.1 _ W.2 3 (by norm_num) _ hsq hφ)
    rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
      norm_num] at h
    rw [hX]
    exact h.trans hE.2
  have h01 : g32h_h01 X = 3 := by
    have h := (b63g2_sixfold_h01 _ _ W.1 _ W.2 _ hsq hφ).trans
      (b63g2_weil_h01 _ _ W.1 _ W.2 3 (by norm_num) _ hsq hφ)
    rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
      norm_num] at h
    rw [hX]
    exact h.trans hE.1
  have hdim : (dim X.X.left : ℤ) = 6 := by
    let _ : IsIntegral (b5_model _ _ W.1
        (b63e_singularQ mr_base C hC V hV s₀ (P s₀) (Q s₀))).left :=
      b5_integral_aux _ _ W.1 _ W.2
    have h := b63g_model_finrank _ _ W.1 _ W.2
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin] at h
    rw [hX]
    change (dim (b5_model _ _ W.1 (b63e_singularQ mr_base C hC V hV s₀ (P s₀) (Q s₀))).left : ℤ)
      = 6
    omega
  have hN : g32h_Nielsen b63g5_tuple := b63d_root_nielsen
  refine ⟨hN, ?_, Or.inl ?_, ?_, ?_⟩
  · rw [hdim, g32h_multCW_of_nielsen _ hN]
  · rw [h10, h01, g32h_holoCW_of_nielsen _ hN, g32h_multCW_of_nielsen _ hN]
    norm_num
  · have h :=
      letI := b5_groupObj _ _ W.1 _ W.2
      letI : IsIntegral (b5_model _ _ W.1
          (b63e_singularQ mr_base C hC V hV s₀ (P s₀) (Q s₀))).left :=
        b5_integral_aux _ _ W.1 _ W.2
      letI := b5_smooth_aux _ _ W.1 _ W.2
      letI := b5_projective_aux _ _ W.1 _ W.2
      b2_abelian_nondegenerate _ _ (b63g_modelForm_riemann _ _ W.1 _ W.2)
    rw [hX]
    unfold b63g2_sixfold
    exact h
  · rw [hX]
    exact b63g2_sixfold_rosati _ _ W.1 _ W.2 _ hsq hφ
      (b63g2_operator_skew mr_base C hC V hV s₀ (hG s₀) (P s₀) (hP s₀) (Q s₀) (hQ s₀))

/-- **Assembly of `g32h_PrymFamily` with `S := V`.** The one input beyond the binders of the
fields check is the field `positive`, in exactly its type: the obligation of part 4. Every other
field is supplied by parts 1–3 and the statements of this file. -/
example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] [FaithfulSMul b4b_Group C] (f : C → OnePoint ℂ) (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hgal : b4_IsGaloisCover b4b_Group f)
    (hsurj : Function.Surjective f)
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (hι : Continuous ι) (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥)
    (hrot₀ : ∀ j, ∃ x, f x = b6_branch mr_base j ∧ b4_IsRotGen ℂ x (b4b_root j))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre mr_base C V hV t ↦ g • x))
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ
      (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s₀ : V) (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice mr_base C hC V hV s₀))
    (hpos : ∀ (t : V) (h : IsNondegenerate (polarizationVec
      (torusCohomology_cupProductOf (b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t).X) (b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t).pol)),
      PolarizationPositive (finiteBetti_abelian (b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t).X)
        (spec_bettiDeRhamIso_abelian (b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t).X)
        (hodgeDecomposition_of_abelian (b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t).X)
        (torusCohomology_cupProductOf (b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t).X) h) :
    ∃ F : g32h_PrymFamily, ∃ j : V ≃ F.S, ∀ t : V,
      F.tuple (j t) = b63g5_tuple ∧ F.fiber (j t) = b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t := by
  let X : V → g32t_Sixfold := fun t ↦ b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t
  have key : ∀ t : V, (dim (X t).X.left : ℤ) = g32h_multCW b63g5_tuple ∧
      (((g32h_h10 (X t) : ℝ) = g32h_holoCW b63g5_tuple ∧
          (g32h_h01 (X t) : ℝ) = g32h_multCW b63g5_tuple - g32h_holoCW b63g5_tuple) ∨
        ((g32h_h01 (X t) : ℝ) = g32h_holoCW b63g5_tuple ∧
          (g32h_h10 (X t) : ℝ) = g32h_multCW b63g5_tuple - g32h_holoCW b63g5_tuple)) ∧
      IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (X t).X) (X t).pol) ∧
      (letI := (torusCohomology_cupProductOf (X t).X).finite
       IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (X t).X) (X t).pol)
        (X t).W.J) := by
    intro t
    have hb : mr_base ∈ b6_chart := mr_base_mem_chart
    let _ : Module.Free ℤ (b63l_parameterLattice mr_base C hC V hV s₀) := Module.Free.of_basis B
    let _ : Module.Finite ℤ (b63l_parameterLattice mr_base C hC V hV s₀) := Module.Finite.of_basis B
    have W := b63e_weight_one_riemann mr_base C hC V hV hG hb f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ t
    have hsq := b63g2_operator_sq mr_base C hC V hV s₀ (hG s₀)
    have hφ := b63g2_operator_filtration mr_base C hC V hV hG P hP s₀ t
    have hX : X t = b63g2_sixfold _ _ W.1 _ W.2 _ hsq hφ := rfl
    obtain ⟨hgal', hs', hfree'⟩ := b63g5_fibre_galois mr_base hb C f hgal hsurj hfree V hV t
    have hstab : ∀ j : Fin 13, ∃ x, f x = b6_branch mr_base j ∧
        MulAction.stabilizer b4b_Group x ≠ ⊥ := by
      intro j
      obtain ⟨x, hx, hrx⟩ := hrot₀ j
      refine ⟨x, hx, fun h ↦ ?_⟩
      have hmem : b4b_root j ∈ MulAction.stabilizer b4b_Group x := hrx.1
      rw [h, Subgroup.mem_bot] at hmem
      have h3 := b63_root_order j
      rw [hmem, orderOf_one] at h3
      split_ifs at h3 <;> omega
    have hbranch := b63g5_fibre_branch mr_base hb C f hgal hsurj hfree hstab V hV t (hk t) (hG t)
    have hrot := b63g5_fibre_rot U π hπ y₀ u₀ γ hγ hroot C f ι hι hproj hequiv hgal hsurj hfree
      V hV t (hk t) (hG t)
    have hE := b63g2_eigen_rank mr_base C hC V hV hG P hP s₀ t hb f (hk t) hs' hgal' hbranch hrot
    have h10 : g32h_h10 (X t) = 3 := by
      have h := (b63g2_sixfold_h10 _ _ W.1 _ W.2 _ hsq hφ).trans
        (b63g2_weil_h10 _ _ W.1 _ W.2 3 (by norm_num) _ hsq hφ)
      rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
        norm_num] at h
      rw [hX]
      exact h.trans hE.2
    have h01 : g32h_h01 (X t) = 3 := by
      have h := (b63g2_sixfold_h01 _ _ W.1 _ W.2 _ hsq hφ).trans
        (b63g2_weil_h01 _ _ W.1 _ W.2 3 (by norm_num) _ hsq hφ)
      rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
        norm_num] at h
      rw [hX]
      exact h.trans hE.1
    have hdim : (dim (X t).X.left : ℤ) = 6 := by
      let _ : IsIntegral (b5_model _ _ W.1
          (b63e_singularQ mr_base C hC V hV s₀ (P s₀) (Q s₀))).left :=
        b5_integral_aux _ _ W.1 _ W.2
      have h := b63g_model_finrank _ _ W.1 _ W.2
      rw [Module.finrank_eq_card_basis B, Fintype.card_fin] at h
      rw [hX]
      change (dim (b5_model _ _ W.1 (b63e_singularQ mr_base C hC V hV s₀ (P s₀) (Q s₀))).left : ℤ)
        = 6
      omega
    have hN : g32h_Nielsen b63g5_tuple := b63d_root_nielsen
    refine ⟨?_, Or.inl ?_, ?_, ?_⟩
    · rw [hdim, g32h_multCW_of_nielsen _ hN]
    · rw [h10, h01, g32h_holoCW_of_nielsen _ hN, g32h_multCW_of_nielsen _ hN]
      norm_num
    · have h :=
        letI := b5_groupObj _ _ W.1 _ W.2
        letI : IsIntegral (b5_model _ _ W.1
            (b63e_singularQ mr_base C hC V hV s₀ (P s₀) (Q s₀))).left :=
          b5_integral_aux _ _ W.1 _ W.2
        letI := b5_smooth_aux _ _ W.1 _ W.2
        letI := b5_projective_aux _ _ W.1 _ W.2
        b2_abelian_nondegenerate _ _ (b63g_modelForm_riemann _ _ W.1 _ W.2)
      rw [hX]
      unfold b63g2_sixfold
      exact h
    · rw [hX]
      exact b63g2_sixfold_rosati _ _ W.1 _ W.2 _ hsq hφ
        (b63g2_operator_skew mr_base C hC V hV s₀ (hG s₀) (P s₀) (hP s₀) (Q s₀) (hQ s₀))
  exact ⟨{ S := V
           tuple := fun _ ↦ b63g5_tuple
           tuple_nielsen := fun _ ↦ b63d_root_nielsen
           fiber := X
           dim_eq := fun t ↦ (key t).1
           hodge := fun t ↦ (key t).2.1
           nondegenerate := fun t ↦ (key t).2.2.1
           rosati := fun t ↦ (key t).2.2.2
           positive := fun t ↦ hpos t _ }, Equiv.refl _, fun _ ↦ ⟨rfl, rfl⟩⟩

/-- **Non-degeneracy of the marked tuple.** No entry of `b63g5_tuple` is the identity matrix:
`b4b_toMatrix` is injective and every `b4b_root i` has order `3` or `2` (`b63_root_order`). So the
tuple is not the trivial one, and each mark is a genuine branch point. -/
example (i : Fin 13) : b63g5_tuple i ≠ 1 := by
  intro h
  have h1 : b4b_root i = 1 :=
    Subtype.val_injective (h.trans (map_one b4b_toMatrix).symm)
  have h3 := b63_root_order i
  rw [h1, orderOf_one] at h3
  split_ifs at h3 <;> omega

/-! ## Instance check on the actual marked root cover

Not elliptic data: the cover is the one of `mr_rootCover`, with `V` the whole polydisc about
`mr_base`. The reference lattice has rank twelve (not zero), every fibre carries the rotation data
of `b4b_root` (no entry of which is `1`), and every fibre sixfold has dimension six and Hodge
numbers `(3, 3)`. -/

/-- **The marked root cover satisfies every binder.** From `mr_rootCover`, the complex structures
of `b63g5_fibre_structure`, the period comparisons `b6m_period_comparison`, the intersection forms
`b3_exists_intersectionForm` and the rank-twelve basis of `b63d_lattice_rank`, every fibre of the
marked family over `b6t_polydisc mr_base` has branch set the marks of `t`, the rotation data of
`b4b_root`, dimension six and Hodge numbers `(3, 3)`. -/
example (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i)) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C) (_ : IsManifold 𝓘(ℂ, ℂ) ω C)
      (_ : T2Space C) (_ : CompactSpace C) (_ : ConnectedSpace C) (_ : MulAction b4b_Group C)
      (_ : FaithfulSMul b4b_Group C)
      (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x)) (f : C → OnePoint ℂ)
      (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hsurj : Function.Surjective f)
      (_ : ∀ t : b6t_polydisc mr_base,
        ChartedSpace ℂ (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t))
      (_ : ∀ t : b6t_polydisc mr_base,
        IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t))
      (hG : ∀ (t : b6t_polydisc mr_base) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
        (fun x : b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t ↦ g • x))
      (hk : ∀ t : b6t_polydisc mr_base, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
        (b63d_projection mr_base C f (b6t_polydisc mr_base) Set.Subset.rfl t))
      (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
      (Q : (t : b6t_polydisc mr_base) → LinearMap.BilinForm ℤ
        (b3_periodLattice ℂ (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t)))
      (hQ : ∀ t, b3_IsIntersectionForm ℂ (Q t))
      (P : (t : b6t_polydisc mr_base) →
        b6m_H1 (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t) →ₗ[ℤ]
          b3_periodLattice ℂ (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t))
      (hP : ∀ (t : b6t_polydisc mr_base)
        (γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t)),
        P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
      (s₀ : b6t_polydisc mr_base)
      (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice mr_base C hC (b6t_polydisc mr_base) Set.Subset.rfl s₀)),
      ∀ t : b6t_polydisc mr_base,
        b4_branchSet ℂ ℂ (b63d_projection mr_base C f (b6t_polydisc mr_base) Set.Subset.rfl t) =
          Set.range (b6_branch t.val) ∧
        (∀ i : Fin 13, ∃ x, b63d_projection mr_base C f (b6t_polydisc mr_base) Set.Subset.rfl t x =
          b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i)) ∧
        (dim (b63g5_fiber mr_base C hC (b6t_polydisc mr_base) Set.Subset.rfl hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t).X.left : ℤ) = 6 ∧
        g32h_h10 (b63g5_fiber mr_base C hC (b6t_polydisc mr_base) Set.Subset.rfl hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t) = 3 ∧
        g32h_h01 (b63g5_fiber mr_base C hC (b6t_polydisc mr_base) Set.Subset.rfl hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t) = 3 := by
  have hb : mr_base ∈ b6_chart := mr_base_mem_chart
  obtain ⟨U, _, _, _, π, hπ, u₀, hroot, C, _, _, _, _, _, _, _, _, f, ι, hf, hgal, hsurj, hact,
    hι, hrange, hproj, hequiv, hfree, hrot₀⟩ := mr_rootCover y₀ γ hγ
  have hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x) := fun g ↦ (hact g).continuous
  let V : Set (Fin 10 → ℂ) := b6t_polydisc mr_base
  have hV : V ⊆ b6t_polydisc mr_base := Set.Subset.rfl
  have hS := fun t : V ↦ b63g5_fibre_structure mr_base hb C f hf hgal hact V hV t
  choose cs ms hk hG using hS
  obtain ⟨Q₀, hQ₀⟩ := b3_exists_intersectionForm (E := ℂ) (C := C) (Module.finrank_self ℂ)
  choose Q hQ using fun t : V ↦
    b3_exists_intersectionForm (E := ℂ) (C := b63l_parameterFibre mr_base C V hV t)
      (Module.finrank_self ℂ)
  choose P hP using fun t : V ↦ b6m_period_comparison (b63l_parameterFibre mr_base C V hV t)
  have hstab : ∀ j : Fin 13, ∃ x, f x = b6_branch mr_base j ∧
      MulAction.stabilizer b4b_Group x ≠ ⊥ := by
    intro j
    obtain ⟨x, hx, hrx⟩ := hrot₀ j
    refine ⟨x, hx, fun h ↦ ?_⟩
    have hmem : b4b_root j ∈ MulAction.stabilizer b4b_Group x := hrx.1
    rw [h, Subgroup.mem_bot] at hmem
    have h3 := b63_root_order j
    rw [hmem, orderOf_one] at h3
    split_ifs at h3 <;> omega
  have hdata : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection mr_base C f V hV t) ∧
      Function.Surjective (b63d_projection mr_base C f V hV t) ∧
      b4_branchSet ℂ ℂ (b63d_projection mr_base C f V hV t) = Set.range (b6_branch t.val) ∧
      ∀ i : Fin 13, ∃ x, b63d_projection mr_base C f V hV t x = b6_branch t.val i ∧
        b4_IsRotGen ℂ x (b4b_root i) := fun t ↦
    ⟨(b63g5_fibre_galois mr_base hb C f hgal hsurj hfree V hV t).1,
      (b63g5_fibre_galois mr_base hb C f hgal hsurj hfree V hV t).2.1,
      b63g5_fibre_branch mr_base hb C f hgal hsurj hfree hstab V hV t (hk t) (hG t),
      b63g5_fibre_rot U π hπ y₀ u₀ γ hγ hroot C f ι hι.continuous hproj hequiv hgal hsurj
        hfree V hV t (hk t) (hG t)⟩
  let s₀ : V := ⟨mr_base, (b6t_polydisc_neighbourhood mr_base hb).1⟩
  have B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice mr_base C hC V hV s₀) :=
    (b63d_lattice_rank mr_base C hC V hV s₀ (hG s₀) hb f (hk s₀) (hdata s₀).2.1 (hdata s₀).1
      (hdata s₀).2.2.1 (hdata s₀).2.2.2).1.some
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hC, f, hf, hsurj, cs, ms, hG, hk, Q₀, hQ₀, Q, hQ,
    fun t ↦ (P t).toLinearMap, hP, s₀, B, fun t ↦ ⟨(hdata t).2.2.1, (hdata t).2.2.2, ?_⟩⟩
  let X : V → g32t_Sixfold := fun t ↦ b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf
    hsurj hk Q₀ hQ₀ Q hQ (fun t ↦ (P t).toLinearMap) hP s₀ B t
  change (dim (X t).X.left : ℤ) = 6 ∧ g32h_h10 (X t) = 3 ∧ g32h_h01 (X t) = 3
  let _ : Module.Free ℤ (b63l_parameterLattice mr_base C hC V hV s₀) := Module.Free.of_basis B
  let _ : Module.Finite ℤ (b63l_parameterLattice mr_base C hC V hV s₀) :=
    Module.Finite.of_basis B
  have W := b63e_weight_one_riemann mr_base C hC V hV hG hb f hf hsurj hk Q₀ hQ₀ Q hQ
    (fun t ↦ (P t).toLinearMap) hP s₀ t
  have hsq := b63g2_operator_sq mr_base C hC V hV s₀ (hG s₀)
  have hφ := b63g2_operator_filtration mr_base C hC V hV hG (fun t ↦ (P t).toLinearMap) hP s₀ t
  have hX : X t = b63g2_sixfold _ _ W.1 _ W.2 _ hsq hφ := rfl
  have hE := b63g2_eigen_rank mr_base C hC V hV hG (fun t ↦ (P t).toLinearMap) hP s₀ t hb f
    (hk t) (hdata t).2.1 (hdata t).1 (hdata t).2.2.1 (hdata t).2.2.2
  have h10 : g32h_h10 (X t) = 3 := by
    have h := (b63g2_sixfold_h10 _ _ W.1 _ W.2 _ hsq hφ).trans
      (b63g2_weil_h10 _ _ W.1 _ W.2 3 (by norm_num) _ hsq hφ)
    rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
      norm_num] at h
    rw [hX]
    exact h.trans hE.2
  have h01 : g32h_h01 (X t) = 3 := by
    have h := (b63g2_sixfold_h01 _ _ W.1 _ W.2 _ hsq hφ).trans
      (b63g2_weil_h01 _ _ W.1 _ W.2 3 (by norm_num) _ hsq hφ)
    rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
      norm_num] at h
    rw [hX]
    exact h.trans hE.1
  have hdim : (dim (X t).X.left : ℤ) = 6 := by
    let _ : IsIntegral (b5_model _ _ W.1
        (b63e_singularQ mr_base C hC V hV s₀ ((P s₀).toLinearMap) (Q s₀))).left :=
      b5_integral_aux _ _ W.1 _ W.2
    have h := b63g_model_finrank _ _ W.1 _ W.2
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin] at h
    rw [hX]
    change (dim (b5_model _ _ W.1 (b63e_singularQ mr_base C hC V hV s₀ ((P s₀).toLinearMap) (Q s₀))).left : ℤ)
      = 6
    omega
  exact ⟨hdim, h10, h01⟩

end HodgeLean.Foundations.Program

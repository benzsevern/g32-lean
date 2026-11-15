import HodgeLean.Foundations.Program.MarkedRootCoverProofs

/-! # The marked root cover: explicit peripheral loops and the retained root monodromy (FROZEN SPEC)

B6-1 selects `b6_Cover` from `b4_riemannExistence`, whose conclusion keeps only local rotation
data; the based monodromy `φ` with `φ (γ j) = op (g j)` built inside
`b4_riemannExistence_aux` is dropped, and the loops there come from an existential
presentation. This spec constructs the marking instead.

Claimed (as implications from the stated binders): at the explicit configuration `mr_base`
(marks `-12, …, -3, 0, 1, ∞`) and on its B6-2a polydisc, the thirteen explicit curves
`mr_curve` give unique loop classes at the base point `mr_basePoint`; they satisfy the
reversed product relation, present the fundamental group, and are positively oriented; a
homomorphism hitting every `op (b4b_root i)` is surjective; the B6-2a radial homeomorphism
carries the explicit loops at `mr_base` to those at `t`; a marked root cover exists over
`mr_base` with based monodromy `op (b4b_root i)` on loop `i` and a compact filling carrying
the B4 conclusion for `b4b_root`; and every configuration `t` of the polydisc carries the
transported marking with the same monodromy values.

Not claimed: any identification of the selected `b6_Cover` with the marked root cover (the
selection is an unspecified witness of a weaker existential); a marking on configurations
outside `b6t_polydisc mr_base`, where transport depends on the path through the braid group;
any identification of `mr_base` with the paper's initial point `C₀`; the Prym lattice,
period or Hodge comparison. Convention: chronological concatenation multiplies in reverse in
`FundamentalGroup`, and monodromy takes values in `Gᵐᵒᵖ` (see `MarkedRootCoverDefs`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The explicit base configuration is a point of the normalized chart: the thirteen marks
`-12, …, -3, 0, 1, ∞` are distinct.
Source: `b6_chart`; distinct integers and `OnePoint.coe_ne_infty`. -/
theorem mr_base_mem_chart :
    mr_base ∈ b6_chart :=
  mr_base_mem_chart_aux

example :
    mr_base ∈ b6_chart :=
  mr_base_mem_chart

/-- Every explicit curve avoids the thirteen marks of each configuration of the polydisc
about `mr_base`, and avoids the ten branch discs with their boundary (so the radial push of B6-2a fixes it).
The circles have radius `1/4` while `b6t_radius mr_base < 1/4`; the segments stay in
`Im z ≥ 1/4`; the outer circle has radius `10` about `-11/2`, and every mark lies within `13/2`.
Source: `b6t_radius`, `b6t_polydisc`; elementary plane geometry. -/
theorem mr_curve_avoids (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    ∀ (i : Fin 13) (s : unitInterval), mr_curve i s ∉ Set.range (b6_branch t) ∧
      mr_curve i s ∉ ⋃ k : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
        Metric.closedBall (mr_base k) (b6t_radius mr_base) :=
  mr_curve_avoids_aux t ht

example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    ∀ (i : Fin 13) (s : unitInterval), mr_curve i s ∉ Set.range (b6_branch t) ∧
      mr_curve i s ∉ ⋃ k : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
        Metric.closedBall (mr_base k) (b6t_radius mr_base) :=
  mr_curve_avoids t ht

/-- At every configuration of the polydisc and the base point `mr_basePoint`, each explicit
curve is a based loop in the punctured sphere, and determines exactly one loop class.
Source: `mr_curve_avoids`; continuity of the piecewise formula at `1/3` and `2/3`
(`Complex.exp_two_pi_mul_I`); Mathlib `Path.ext`. -/
theorem mr_loop_existsUnique (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ)) (i : Fin 13) :
    ∃! c : FundamentalGroup (b6t_punctured t) y₀, mr_IsLoop t y₀ i c :=
  mr_loop_existsUnique_aux t ht y₀ hy₀ i

example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ)) (i : Fin 13) :
    ∃! c : FundamentalGroup (b6t_punctured t) y₀, mr_IsLoop t y₀ i c :=
  mr_loop_existsUnique t ht y₀ hy₀ i

/-- The explicit loops satisfy the sphere relation in chronological order: running the lassos
from left to right traces the counterclockwise boundary of the outer disc, and the outer loop
traces it back. With `fromPath (c.trans d) = fromPath d * fromPath c` this is the reversed
product.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §13; Völklein, *Groups as Galois
Groups*, Cambridge Stud. Adv. Math. 53 (1996), §4.1 (standard generating systems). -/
theorem mr_loops_product (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀)
    (hγ : ∀ i, mr_IsLoop t y₀ i (γ i)) :
    (List.ofFn γ).reverse.prod = 1 :=
  mr_loops_product_aux t ht y₀ γ hγ

example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀)
    (hγ : ∀ i, mr_IsLoop t y₀ i (γ i)) :
    (List.ofFn γ).reverse.prod = 1 :=
  mr_loops_product t ht y₀ γ hγ

/-- The explicit loops present the fundamental group of the punctured sphere: homomorphisms
to any group are exactly the tuples satisfying the reversed product relation.
Source: Völklein, *Groups as Galois Groups*, Theorem 4.3 (π₁ of the punctured sphere with a
standard generating system); Forster, GTM 81, §13; Hatcher, *Algebraic Topology*, §1.2. -/
theorem mr_loops_universal (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀)
    (hγ : ∀ i, mr_IsLoop t y₀ i (γ i)) :
    ∀ (H : Type) [Group H] (k : Fin 13 → H), (List.ofFn k).reverse.prod = 1 →
      ∃! ψ : FundamentalGroup (b6t_punctured t) y₀ →* H, ∀ i, ψ (γ i) = k i :=
  mr_loops_universal_aux t ht y₀ γ hγ

example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀)
    (hγ : ∀ i, mr_IsLoop t y₀ i (γ i)) :
    ∀ (H : Type) [Group H] (k : Fin 13 → H), (List.ofFn k).reverse.prod = 1 →
      ∃! ψ : FundamentalGroup (b6t_punctured t) y₀ →* H, ∀ i, ψ (γ i) = k i :=
  mr_loops_universal t ht y₀ γ hγ

/-- The explicit loops are positively oriented: on any compact Galois `G`-cover, a lift of
loop `j` ending at `k •` its start detects a point over mark `j` at which `k` is the rotation
generator (`z ↦ e^{2πi/n} z`). The lassos are counterclockwise; the outer loop is
counterclockwise in the chart `1/z` at `∞`.
Source: Forster, GTM 81, Theorem 4.23 (local normal form) and §5 (lifting of paths);
Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III, Proposition 3.1. -/
theorem mr_loops_positive (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀)
    (hγ : ∀ i, mr_IsLoop t y₀ i (γ i)) :
    ∀ (D : Type) [TopologicalSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ, ℂ) ω D]
      [T2Space D] [CompactSpace D] [ConnectedSpace D] (G : Type) [Group G] [Finite G]
      [MulAction G D] [FaithfulSMul G D],
      (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : D ↦ g • x)) →
      ∀ f : D → OnePoint ℂ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f → b4_IsGaloisCover G f →
      (∀ x, f x ∉ Set.range (b6_branch t) → MulAction.stabilizer G x = ⊥) →
      ∀ (j : Fin 13) (c : Path y₀ y₀), FundamentalGroup.fromPath ⟦c⟧ = γ j →
      ∀ (Γ : C(unitInterval, D)) (k : G), (∀ s, f (Γ s) = (c s : OnePoint ℂ)) →
        Γ 1 = k • Γ 0 → ∃ x, f x = b6_branch t j ∧ b4_IsRotGen ℂ x k :=
  mr_loops_positive_aux t ht y₀ γ hγ

example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀)
    (hγ : ∀ i, mr_IsLoop t y₀ i (γ i)) :
    ∀ (D : Type) [TopologicalSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ, ℂ) ω D]
      [T2Space D] [CompactSpace D] [ConnectedSpace D] (G : Type) [Group G] [Finite G]
      [MulAction G D] [FaithfulSMul G D],
      (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : D ↦ g • x)) →
      ∀ f : D → OnePoint ℂ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f → b4_IsGaloisCover G f →
      (∀ x, f x ∉ Set.range (b6_branch t) → MulAction.stabilizer G x = ⊥) →
      ∀ (j : Fin 13) (c : Path y₀ y₀), FundamentalGroup.fromPath ⟦c⟧ = γ j →
      ∀ (Γ : C(unitInterval, D)) (k : G), (∀ s, f (Γ s) = (c s : OnePoint ℂ)) →
        Γ 1 = k • Γ 0 → ∃ x, f x = b6_branch t j ∧ b4_IsRotGen ℂ x k :=
  mr_loops_positive t ht y₀ γ hγ

/-- A homomorphism to `b4b_Groupᵐᵒᵖ` hitting every `op (b4b_root i)` is surjective, since the
root entries generate the group.
Source: `b63d_root_subgroup`; `MulOpposite.op` is an anti-isomorphism. -/
theorem mr_root_surjective {M : Type} [Group M] (φ : M →* b4b_Groupᵐᵒᵖ) (γ : Fin 13 → M)
    (hroot : ∀ i, φ (γ i) = MulOpposite.op (b4b_root i)) :
    Function.Surjective φ :=
  mr_root_surjective_aux φ γ hroot

example {M : Type} [Group M] (φ : M →* b4b_Groupᵐᵒᵖ) (γ : Fin 13 → M)
    (hroot : ∀ i, φ (γ i) = MulOpposite.op (b4b_root i)) :
    Function.Surjective φ :=
  mr_root_surjective φ γ hroot

/-- The B6-2a radial homeomorphism carries each explicit loop class at `mr_base` to the
explicit loop class at `t`: it fixes every point of every explicit curve.
Source: `mr_curve_avoids`; `b6t_fixed`; Mathlib `FundamentalGroup.map`. -/
theorem mr_loop_transport (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (e : b6t_punctured mr_base ≃ₜ b6t_punctured t)
    (he : ∀ x, (e x : OnePoint ℂ) = b6t_sphere mr_base t x)
    (y₀ : b6t_punctured mr_base) (i : Fin 13)
    (c : FundamentalGroup (b6t_punctured mr_base) y₀) (hc : mr_IsLoop mr_base y₀ i c) :
    mr_IsLoop t (e y₀) i (FundamentalGroup.map ⟨e, e.continuous⟩ y₀ c) :=
  mr_loop_transport_aux t ht e he y₀ i c hc

example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (e : b6t_punctured mr_base ≃ₜ b6t_punctured t)
    (he : ∀ x, (e x : OnePoint ℂ) = b6t_sphere mr_base t x)
    (y₀ : b6t_punctured mr_base) (i : Fin 13)
    (c : FundamentalGroup (b6t_punctured mr_base) y₀) (hc : mr_IsLoop mr_base y₀ i c) :
    mr_IsLoop t (e y₀) i (FundamentalGroup.map ⟨e, e.continuous⟩ y₀ c) :=
  mr_loop_transport t ht e he y₀ i c hc

/-- **The marked root cover.** Over the base configuration there is a connected Galois
`b4b_Group`-cover of the punctured sphere with a marked point over the base point whose based
monodromy sends the `i`-th explicit loop to `op (b4b_root i)`, together with a compact
holomorphic filling. The filling carries every property that `b4_riemannExistence` records
for `b4b_root` at `b6_branch mr_base`, the property from which `b6_Cover` is selected.
Source: `mr_loops_universal`, `mr_root_op_reverse_prod`, `mr_root_surjective`,
`b6m_marked_rex`, `mr_loops_positive`; Forster, GTM 81, Theorem 8.4. -/
theorem mr_rootCover (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i)) :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : MulAction b4b_Group U)
      (_ : ConnectedSpace U) (π : U → b6t_punctured mr_base)
      (hπ : IsQuotientCoveringMap π b4b_Group) (u₀ : π ⁻¹' {y₀}),
      (∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i)) ∧
      ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
        (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
        (_ : ConnectedSpace C) (_ : MulAction b4b_Group C) (_ : FaithfulSMul b4b_Group C)
        (f : C → OnePoint ℂ) (ι : U → C),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ b4_IsGaloisCover b4b_Group f ∧
        Function.Surjective f ∧
        (∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
        Topology.IsOpenEmbedding ι ∧ Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ ∧
        (∀ u, f (ι u) = π u) ∧ (∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u) ∧
        (∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥) ∧
        ∀ j, ∃ x, f x = b6_branch mr_base j ∧ b4_IsRotGen ℂ x (b4b_root j) :=
  mr_rootCover_aux y₀ γ hγ

example (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i)) :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : MulAction b4b_Group U)
      (_ : ConnectedSpace U) (π : U → b6t_punctured mr_base)
      (hπ : IsQuotientCoveringMap π b4b_Group) (u₀ : π ⁻¹' {y₀}),
      (∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i)) ∧
      ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
        (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
        (_ : ConnectedSpace C) (_ : MulAction b4b_Group C) (_ : FaithfulSMul b4b_Group C)
        (f : C → OnePoint ℂ) (ι : U → C),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ b4_IsGaloisCover b4b_Group f ∧
        Function.Surjective f ∧
        (∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
        Topology.IsOpenEmbedding ι ∧ Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ ∧
        (∀ u, f (ι u) = π u) ∧ (∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u) ∧
        (∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥) ∧
        ∀ j, ∃ x, f x = b6_branch mr_base j ∧ b4_IsRotGen ℂ x (b4b_root j) :=
  mr_rootCover y₀ γ hγ

/-- **The marking along the family.** Over every configuration `t` of the polydisc, the
transported cover `e ∘ π` (B6-2a) carries the transported marking: the transported loops are
the explicit loops at `t`, and its based monodromy at the transported marked point sends the
`i`-th of them to `op (b4b_root i)`.
Source: `b6t_monodromy`, `mr_loop_transport`, `mr_curve_avoids`; Hatcher, *Algebraic
Topology*, Proposition 1.33 (naturality of lifting). -/
theorem mr_rootCover_family (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i)) :
    ∃ e : b6t_punctured mr_base ≃ₜ b6t_punctured t,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere mr_base t x) ∧
      (e y₀ : OnePoint ℂ) = y₀ ∧
      ∀ i, mr_IsLoop t (e y₀) i (FundamentalGroup.map ⟨e, e.continuous⟩ y₀ (γ i)) ∧
        (hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
          ⟨u₀.val, congrArg e u₀.property⟩
          (FundamentalGroup.map ⟨e, e.continuous⟩ y₀ (γ i)) =
            MulOpposite.op (b4b_root i) :=
  mr_rootCover_family_aux t ht U π hπ y₀ u₀ γ hγ hroot

example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i)) :
    ∃ e : b6t_punctured mr_base ≃ₜ b6t_punctured t,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere mr_base t x) ∧
      (e y₀ : OnePoint ℂ) = y₀ ∧
      ∀ i, mr_IsLoop t (e y₀) i (FundamentalGroup.map ⟨e, e.continuous⟩ y₀ (γ i)) ∧
        (hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
          ⟨u₀.val, congrArg e u₀.property⟩
          (FundamentalGroup.map ⟨e, e.continuous⟩ y₀ (γ i)) =
            MulOpposite.op (b4b_root i) :=
  mr_rootCover_family t ht U π hπ y₀ u₀ γ hγ hroot

/-! ## Satisfiability, non-degeneracy and chain checks -/

/-- **Satisfiability of the loop binders.** At every configuration of the polydisc a base
point and a full system of explicit loop classes exist, so the binder `hγ` is not vacuous. -/
example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    ∃ (y₀ : b6t_punctured t) (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀),
      ∀ i, mr_IsLoop t y₀ i (γ i) := by
  have h0 : mr_curve 12 ((0 : unitInterval) : ℝ) = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
    simp [mr_curve, mr_outer, mr_basePoint]
  have hmem : ((mr_basePoint : ℂ) : OnePoint ℂ) ∈ b6t_punctured t := by
    have h := (mr_curve_avoids t ht 12 0).1
    rw [h0] at h
    exact h
  exact ⟨⟨_, hmem⟩, fun i ↦ (mr_loop_existsUnique t ht ⟨_, hmem⟩ rfl i).exists.choose,
    fun i ↦ (mr_loop_existsUnique t ht ⟨_, hmem⟩ rfl i).exists.choose_spec⟩

/-- **Non-degeneracy.** No explicit loop class is trivial: the presentation sends loop `i`
to `op (b4b_root i)`, which has order `3` or `2`. This rules out a trivial marking. -/
example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured t)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀)
    (hγ : ∀ i, mr_IsLoop t y₀ i (γ i)) (i : Fin 13) : γ i ≠ 1 := by
  obtain ⟨ψ, hψ, -⟩ := mr_loops_universal t ht y₀ γ hγ b4b_Groupᵐᵒᵖ
    (fun j ↦ MulOpposite.op (b4b_root j)) mr_root_op_reverse_prod
  intro h
  have h1 := hψ i
  rw [h, map_one] at h1
  have h2 : b4b_root i = 1 := MulOpposite.op_injective (h1.symm.trans MulOpposite.op_one.symm)
  have h3 := b63_root_order i
  rw [h2, orderOf_one] at h3
  split_ifs at h3 <;> omega

/-- **Compatibility with `b6_Cover`.** The filling of the marked root cover is a witness of
exactly the property of `b4_riemannExistence` (for `b4b_root` at `b6_branch mr_base`) from
which `b6_Cover` is selected; it additionally retains the based marking. -/
example (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i)) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction b4b_Group C) (_ : FaithfulSMul b4b_Group C)
      (f : C → OnePoint ℂ),
      (∀ h : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ h • x)) ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ b4_IsGaloisCover b4b_Group f ∧
      (∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥) ∧
      ∀ j, ∃ x, f x = b6_branch mr_base j ∧ b4_IsRotGen ℂ x (b4b_root j) := by
  obtain ⟨U, _, _, _, π, hπ, u₀, -, C, _, _, _, _, _, _, _, _, f, ι, hf, hgal, -, hG, -, -, -, -,
    hstab, hrot⟩ := mr_rootCover y₀ γ hγ
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, f, hG, hf, hgal, hstab, hrot⟩

/-- **Chain check toward B6-4b.** At every configuration `t` of the polydisc, the marked root
cover and the explicit loops supply the binders `hmon`, `hprod`, `hgen`, `hpositive` and
`hroot` of the B6-4b rational marking statement (`cloud/spec-b64b`,
`b64b_rational_marking`), in the same shapes. -/
example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i)) :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : MulAction b4b_Group U)
      (π : U → b6t_punctured t) (hπ : IsQuotientCoveringMap π b4b_Group)
      (y₁ : b6t_punctured t) (u₁ : π ⁻¹' {y₁})
      (φ : FundamentalGroup (b6t_punctured t) y₁ →* b4b_Groupᵐᵒᵖ)
      (γ' : Fin 13 → FundamentalGroup (b6t_punctured t) y₁),
      hπ.fundamentalGroupToMulOpposite u₁ = φ ∧
      (List.ofFn γ').reverse.prod = 1 ∧
      (∀ (H : Type) [Group H] (k : Fin 13 → H), (List.ofFn k).reverse.prod = 1 →
        ∃! ψ : FundamentalGroup (b6t_punctured t) y₁ →* H, ∀ i, ψ (γ' i) = k i) ∧
      (∀ (D : Type) [TopologicalSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ, ℂ) ω D]
        [T2Space D] [CompactSpace D] [ConnectedSpace D] (G : Type) [Group G] [Finite G]
        [MulAction G D] [FaithfulSMul G D],
        (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : D ↦ g • x)) →
        ∀ f : D → OnePoint ℂ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f → b4_IsGaloisCover G f →
        (∀ x, f x ∉ Set.range (b6_branch t) → MulAction.stabilizer G x = ⊥) →
        ∀ (j : Fin 13) (c : Path y₁ y₁), FundamentalGroup.fromPath ⟦c⟧ = γ' j →
        ∀ (Γ : C(unitInterval, D)) (k : G), (∀ s, f (Γ s) = (c s : OnePoint ℂ)) →
          Γ 1 = k • Γ 0 → ∃ x, f x = b6_branch t j ∧ b4_IsRotGen ℂ x k) ∧
      ∀ i, φ (γ' i) = MulOpposite.op (b4b_root i) := by
  obtain ⟨U, _, _, _, π, hπ, u₀, hroot, -⟩ := mr_rootCover y₀ γ hγ
  obtain ⟨e, -, -, he⟩ := mr_rootCover_family t ht U π hπ y₀ u₀ γ hγ hroot
  have hγ' : ∀ i, mr_IsLoop t (e y₀) i (FundamentalGroup.map ⟨e, e.continuous⟩ y₀ (γ i)) :=
    fun i ↦ (he i).1
  exact ⟨U, inferInstance, inferInstance, e ∘ π, hπ.homeomorph_comp e, e y₀,
    ⟨u₀.val, congrArg e u₀.property⟩, _, fun i ↦ FundamentalGroup.map ⟨e, e.continuous⟩ y₀ (γ i),
    rfl, mr_loops_product t ht _ _ hγ', mr_loops_universal t ht _ _ hγ',
    mr_loops_positive t ht _ _ hγ', fun i ↦ (he i).2⟩

end HodgeLean.Foundations.Program

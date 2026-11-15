import HodgeLean.Foundations.Program.PrymParabolicMarkedLoopsProofs

/-! # Stage H3c: the oriented base decomposition at `mr_base` and the endpoint monodromy (FROZEN SPEC)

The frozen spec for `docs/briefs/cloud-spec-h3c.md` (`docs/specs/PrymParabolicMarkedLoops.md`).
Each theorem restates the matching `_aux` theorem in `PrymParabolicMarkedLoopsProofs.lean`.

**Claimed (once the bodies are proved).** At every configuration `t` of the B6-2a polydisc about
the explicit configuration `mr_base` (marks `-12, …, -3, 0, 1, ∞`, base point `-11/2 + 10 i`):
- the thirteen polygonal arcs `f_i = hg3_arc i` from `b₀` to `b_∞ = -11/2 − 10 i` avoid the marks
  and the branch discs with their boundary circles, and each traces exactly one path in the punctured sphere;
- two arcs meet only at their common endpoints, and each arc is injective;
- the complement of the arcs is the disjoint union of the thirteen open connected sectors
  `hg3_sector i`, and sector `i` contains exactly the mark `p_i` of `t`;
- the loop `f_i · f_{i+1}⁻¹` (index mod `13`) and the explicit lasso `mr_curve i` define the
  same based class: `fromPath ⟦(F i).trans (F (i + 1)).symm⟧ = γ i`;
- on a quotient covering with deck group `G`, a loop with monodromy value `op k` lifts from
  `x • u₀` to a path ending at `(x * k) • u₀`;
- for a covering of the punctured sphere at `t` whose marked monodromy sends `γ i` to `op (g i)`
  (the shape of `mr_rootCover` and `mr_rootCover_family`, with `g = b4b_root`), the lift of
  `f_i · f_{i+1}⁻¹` from `x • u₀` ends at `(x * g i) • u₀`, and the lift of `f_i` from `y • u₀`
  ends at `(y Q_i⁻¹) • v_∞`, where `v_∞` ends the lift of `f_0` from `u₀` and `Q_i = g₀ ⋯ g_{i−1}`
  (`hg_Q`): the labels of H3a's `hg_tgt`.

Each statement is an implication from its binders. The tuple and the configuration are explicit;
`b4b_root` enters through the instances below, and the joint satisfiability check witnesses
every binder at `t = mr_base` with the marked root cover of `mr_rootCover`.

**Not claimed.** The edges `e_i`, `h_i` and the triangles `A_i`, `B_i` as singular simplices;
lifted cells in the compact filling; any comparison of cellular and singular homology; the
existence of the cover of the binders (`mr_rootCover`, `mr_rootCover_family`, cited, not
restated); any configuration outside `b6t_polydisc mr_base`; anything about H4, H5 or H7.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Complex

namespace HodgeLean.Foundations.Program

/-! ## The oriented base decomposition -/

/-- **The arcs avoid the marks.** For every configuration of the polydisc, every point of every
arc `f_i` lies off the thirteen marks and off the ten branch discs about `mr_base` with their boundary circles, so
the B6-2a radial homeomorphism fixes it. The arc has imaginary part `10 − 20 s`; at heights
`|y| ≤ 1/8` its real part is within `7/80` of the half-integer `w_i`, at distance at least
`1/2` from every integer mark, while `b6t_radius mr_base < 1/8`.
Source: `b6t_radius`, `b6t_polydisc`; elementary plane geometry. -/
theorem hg3_arc_avoids (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    ∀ (i : Fin 13) (s : unitInterval),
      ((hg3_arc i s : ℂ) : OnePoint ℂ) ∉ Set.range (b6_branch t) ∧
        ((hg3_arc i s : ℂ) : OnePoint ℂ) ∉ ⋃ k : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
          Metric.closedBall (mr_base k) (b6t_radius mr_base) :=
  hg3_arc_avoids_aux t ht

example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    ∀ (i : Fin 13) (s : unitInterval),
      ((hg3_arc i s : ℂ) : OnePoint ℂ) ∉ Set.range (b6_branch t) ∧
        ((hg3_arc i s : ℂ) : OnePoint ℂ) ∉ ⋃ k : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
          Metric.closedBall (mr_base k) (b6t_radius mr_base) :=
  hg3_arc_avoids t ht

/-- **Each arc is a path.** At every configuration of the polydisc, with base points at `b₀`
and `b_∞`, the arc `f_i` traces exactly one path in the punctured sphere.
Source: `hg3_arc_avoids`; continuity of `min` and `max`; Mathlib `Path.ext`. -/
theorem hg3_arc_existsUnique (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (y₀ y₁ : b6t_punctured t) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (hy₁ : (y₁ : OnePoint ℂ) = ((hg3_bottom : ℂ) : OnePoint ℂ)) (i : Fin 13) :
    ∃! F : Path y₀ y₁, ∀ s : unitInterval, (F s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ) :=
  hg3_arc_existsUnique_aux t ht y₀ y₁ hy₀ hy₁ i

example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (y₀ y₁ : b6t_punctured t) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (hy₁ : (y₁ : OnePoint ℂ) = ((hg3_bottom : ℂ) : OnePoint ℂ)) (i : Fin 13) :
    ∃! F : Path y₀ y₁, ∀ s : unitInterval, (F s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ) :=
  hg3_arc_existsUnique t ht y₀ y₁ hy₀ hy₁ i

/-- **Disjoint interiors.** Two points of the arcs coincide only when they are the same point of
the same arc, or both are the common start `b₀`, or both are the common end `b_∞`. The
imaginary part `10 − 20 s` fixes the parameter, and for `0 < s < 1` the real parts
`hg3_profile i` are strictly increasing in `i`.
Source: G32 v0.16, Figure 1; elementary plane geometry. -/
theorem hg3_arc_interiors (i j : Fin 13) (s s' : unitInterval)
    (h : hg3_arc i s = hg3_arc j s') :
    (i = j ∧ s = s') ∨ (s = 0 ∧ s' = 0) ∨ (s = 1 ∧ s' = 1) :=
  hg3_arc_interiors_aux i j s s' h

example (i j : Fin 13) (s s' : unitInterval) (h : hg3_arc i s = hg3_arc j s') :
    (i = j ∧ s = s') ∨ (s = 0 ∧ s' = 0) ∨ (s = 1 ∧ s' = 1) :=
  hg3_arc_interiors i j s s' h

/-- **Coverage of the sectors.** A point of the sphere lies off every arc exactly when it lies in
exactly one sector: the sectors are disjoint and cover the complement of the arcs.
Source: G32 v0.16, Figure 1; elementary plane geometry (the fan `hg3_fan` is the union of the
arcs and the sectors `0, …, 11`). -/
theorem hg3_sector_partition (z : OnePoint ℂ) :
    z ∉ ⋃ i, hg3_arcSet i ↔ ∃! i, z ∈ hg3_sector i :=
  hg3_sector_partition_aux z

example (z : OnePoint ℂ) : z ∉ ⋃ i, hg3_arcSet i ↔ ∃! i, z ∈ hg3_sector i :=
  hg3_sector_partition z

/-- **The sectors are open and connected.** Sector `i < 12` is the region between two
continuous profiles over the interval `|y| < 10`; sector `12` is the complement in the sphere of
a compact convex quadrilateral.
Source: Mathlib `IsConnected`; Hatcher, *Algebraic Topology*, §1.1 (path-connected regions). -/
theorem hg3_sector_open_connected (i : Fin 13) :
    IsOpen (hg3_sector i) ∧ IsConnected (hg3_sector i) :=
  hg3_sector_open_connected_aux i

example (i : Fin 13) : IsOpen (hg3_sector i) ∧ IsConnected (hg3_sector i) :=
  hg3_sector_open_connected i

/-- **One mark per sector.** At every configuration of the polydisc, the mark `p_j` lies in
sector `i` exactly when `j = i`; `∞` lies in sector `12`.
Source: `b6t_polydisc`; `b6t_radius mr_base < 1/8`; elementary plane geometry. -/
theorem hg3_sector_mark (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (i j : Fin 13) :
    b6_branch t j ∈ hg3_sector i ↔ j = i :=
  hg3_sector_mark_aux t ht i j

example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (i j : Fin 13) :
    b6_branch t j ∈ hg3_sector i ↔ j = i :=
  hg3_sector_mark t ht i j

/-- **The marked lassos.** At every configuration of the polydisc, the loop
`f_i · f_{i+1}⁻¹` (index mod `13`) and the explicit peripheral curve `mr_curve i` define the
same based class. For `i < 12` both lie in sector `i` together with its boundary arcs, with its
mark removed: a disc with its boundary circle, minus an interior point; both go once
counterclockwise around it. For `i = 12` both lie in the region between the fan and the outer
circle, boundaries included: two discs, right and left of the fan, meeting at `b₀` and `b_∞`; `f_12`
and `f_0` are homotopic, relative to their endpoints, to the right and left halves of `mr_outer`.
Construct the homotopy at `mr_base` first; the radial homeomorphism of B6-2a fixes the
arcs (`hg3_arc_avoids`) and the lassos (`mr_curve_avoids`), and `mr_loop_transport` carries it
to `t`.
Source: Hatcher, *Algebraic Topology*, Theorem 1.7 and §1.1 (`π₁` of an annulus);
Forster, GTM 81, §13; Völklein, *Groups as Galois Groups*, §4.1. -/
theorem hg3_ell_isLoop (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (y₀ y₁ : b6t_punctured t) (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀) (hγ : ∀ i, mr_IsLoop t y₀ i (γ i))
    (i : Fin 13) :
    FundamentalGroup.fromPath ⟦(F i).trans (F (finRotate 13 i)).symm⟧ = γ i :=
  hg3_ell_isLoop_aux t ht y₀ y₁ F hF γ hγ i

example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (y₀ y₁ : b6t_punctured t) (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀) (hγ : ∀ i, mr_IsLoop t y₀ i (γ i))
    (i : Fin 13) :
    FundamentalGroup.fromPath ⟦(F i).trans (F (finRotate 13 i)).symm⟧ = γ i :=
  hg3_ell_isLoop t ht y₀ y₁ F hF γ hγ i

/-! ## The endpoint monodromy -/

/-- **Endpoint of a lift.** On a quotient covering with deck group `G`, if the monodromy value
of the class of a loop `c` at `u₀` is `op k`, then the lift of `c` starting at `x • u₀` ends at
`(x * k) • u₀`: monodromy commutes with the deck action.
Source: Mathlib `IsQuotientCoveringMap.monodromy_toPermFiber`,
`IsQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_iff`,
`IsCoveringMap.monodromy_eq_apply_one`; Hatcher, Proposition 1.30. -/
theorem hg3_lift_endpoint {X U : Type*} [TopologicalSpace X] [TopologicalSpace U]
    {G : Type*} [Group G] [MulAction G U] {π : U → X} (hπ : IsQuotientCoveringMap π G)
    {x₀ : X} (u₀ : π ⁻¹' {x₀}) (c : Path x₀ x₀) (k : G)
    (hk : hπ.fundamentalGroupToMulOpposite u₀ (FundamentalGroup.fromPath ⟦c⟧) =
      MulOpposite.op k)
    (x : G) (Γ : C(unitInterval, U)) (hΓ : ∀ s, π (Γ s) = c s) (h0 : Γ 0 = x • (u₀ : U)) :
    Γ 1 = (x * k) • (u₀ : U) :=
  hg3_lift_endpoint_aux hπ u₀ c k hk x Γ hΓ h0

example {X U : Type*} [TopologicalSpace X] [TopologicalSpace U]
    {G : Type*} [Group G] [MulAction G U] {π : U → X} (hπ : IsQuotientCoveringMap π G)
    {x₀ : X} (u₀ : π ⁻¹' {x₀}) (c : Path x₀ x₀) (k : G)
    (hk : hπ.fundamentalGroupToMulOpposite u₀ (FundamentalGroup.fromPath ⟦c⟧) =
      MulOpposite.op k)
    (x : G) (Γ : C(unitInterval, U)) (hΓ : ∀ s, π (Γ s) = c s) (h0 : Γ 0 = x • (u₀ : U)) :
    Γ 1 = (x * k) • (u₀ : U) :=
  hg3_lift_endpoint hπ u₀ c k hk x Γ hΓ h0

/-- **Endpoint monodromy of `ℓ_i`.** For a covering of the punctured sphere at `t` with deck
group `G` whose marked monodromy sends the `i`-th explicit loop class to `op (g i)`, the lift of
`f_i · f_{i+1}⁻¹` from `x • u₀` ends at `(x * g i) • u₀`: the transport `x ↦ x g_i` of H3a.
From `hg3_ell_isLoop` and `hg3_lift_endpoint`; no local rotation data is used.
Source: `mr_rootCover`, `mr_rootCover_family` (the shape of `hroot`); G32 v0.16, Figure 1;
Hatcher, Proposition 1.30. -/
theorem hg3_ell_endpoint (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    {G : Type*} [Group G] (g : Fin 13 → G)
    (U : Type*) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured t) (hπ : IsQuotientCoveringMap π G)
    (y₀ y₁ : b6t_punctured t) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀) (hγ : ∀ i, mr_IsLoop t y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (i : Fin 13) (x : G) (Γ : C(unitInterval, U))
    (hΓ : ∀ s, π (Γ s) = ((F i).trans (F (finRotate 13 i)).symm) s)
    (h0 : Γ 0 = x • (u₀ : U)) :
    Γ 1 = (x * g i) • (u₀ : U) :=
  hg3_ell_endpoint_aux t ht g U π hπ y₀ y₁ u₀ γ hγ hroot F hF i x Γ hΓ h0

/-- The instance at the G32 root `b4b_root`, in the shape of `mr_rootCover_family`. -/
example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured t) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ y₁ : b6t_punctured t) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀) (hγ : ∀ i, mr_IsLoop t y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (i : Fin 13) (x : b4b_Group) (Γ : C(unitInterval, U))
    (hΓ : ∀ s, π (Γ s) = ((F i).trans (F (finRotate 13 i)).symm) s)
    (h0 : Γ 0 = x • (u₀ : U)) :
    Γ 1 = (x * b4b_root i) • (u₀ : U) :=
  hg3_ell_endpoint t ht b4b_root U π hπ y₀ y₁ u₀ γ hγ hroot F hF i x Γ hΓ h0

/-- **Endpoints of the lifted arcs.** Under the binders of `hg3_ell_endpoint`, let `Δ` lift
`f_0` from `u₀`. The lift of `f_i` from `y • u₀` ends at `(y * (g₀ ⋯ g_{i−1})⁻¹) • Δ 1`, the
label `b_∞(y Q_i⁻¹)` of H3a's `hg_tgt`. Product one is not needed: only the loops
`ℓ_0, …, ℓ_{i−1}` enter, through `f_{j+1}` lifted from `(y g_j) • u₀` ending where `f_j` lifted
from `y • u₀` ends, and `hg_Q g (j + 1) = hg_Q g j * g j`.
Source: `hg3_ell_endpoint`, `hg_Q_succ`; G32 v0.16, Figure 1 (the sheet labels over `b_∞`);
Hatcher, Proposition 1.30. -/
theorem hg3_arc_endpoint (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    {G : Type*} [Group G] (g : Fin 13 → G)
    (U : Type*) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured t) (hπ : IsQuotientCoveringMap π G)
    (y₀ y₁ : b6t_punctured t) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀) (hγ : ∀ i, mr_IsLoop t y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (Δ : C(unitInterval, U)) (hΔ : ∀ s, π (Δ s) = F 0 s) (hΔ0 : Δ 0 = (u₀ : U))
    (i : Fin 13) (y : G) (Γ : C(unitInterval, U)) (hΓ : ∀ s, π (Γ s) = F i s)
    (h0 : Γ 0 = y • (u₀ : U)) :
    Γ 1 = (y * (hg_Q g i)⁻¹) • Δ 1 :=
  hg3_arc_endpoint_aux t ht g U π hπ y₀ y₁ u₀ γ hγ hroot F hF Δ hΔ hΔ0 i y Γ hΓ h0

example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured t) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ y₁ : b6t_punctured t) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀) (hγ : ∀ i, mr_IsLoop t y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (Δ : C(unitInterval, U)) (hΔ : ∀ s, π (Δ s) = F 0 s) (hΔ0 : Δ 0 = (u₀ : U))
    (i : Fin 13) (y : b4b_Group) (Γ : C(unitInterval, U)) (hΓ : ∀ s, π (Γ s) = F i s)
    (h0 : Γ 0 = y • (u₀ : U)) :
    Γ 1 = (y * (hg_Q b4b_root i)⁻¹) • Δ 1 :=
  hg3_arc_endpoint t ht b4b_root U π hπ y₀ y₁ u₀ γ hγ hroot F hF Δ hΔ hΔ0 i y Γ hΓ h0

/-! ## Satisfiability, non-degeneracy and chain checks -/

/-- **Satisfiability of `hroot` against the loop relation.** The values `op (b4b_root i)` satisfy
the reversed product relation `(List.ofFn γ).reverse.prod = 1` of the explicit loops
(`mr_loops_product`), so `hroot` with `g = b4b_root` does not contradict it.
Source: `b63d_root_product`; `MulOpposite.op` reverses products. -/
example : (List.ofFn fun i ↦ MulOpposite.op (b4b_root i)).reverse.prod = 1 := by
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_list_prod, MulOpposite.unop_one, List.map_reverse,
    List.reverse_reverse, List.map_ofFn]
  exact b63d_root_product

/-- **Satisfiability of the tuple hypotheses.** `b4b_root` has product one and generates
`b4b_Group` (cited, not restated), the hypotheses of H3a under which `X̃(b4b_root)` is the
compact connected complex that the lifted cells will realize. -/
example : (List.ofFn b4b_root).prod = 1 ∧ Subgroup.closure (Set.range b4b_root) = ⊤ :=
  ⟨b63d_root_product, b63d_root_subgroup⟩

/-- **Satisfiability of `ht`.** The base configuration lies in its own polydisc: the radius
`b6t_radius mr_base` is positive. -/
theorem hg3_base_mem_polydisc : mr_base ∈ b6t_polydisc mr_base := by
  intro i
  rw [Metric.mem_ball, dist_self, b6t_radius]
  apply inv_pos.mpr
  apply mul_pos (by norm_num)
  apply add_pos_of_pos_of_nonneg one_pos
  apply Finset.sum_nonneg
  intro k _
  apply add_nonneg (add_nonneg (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr (norm_nonneg _)))
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_refl 0
  · exact inv_nonneg.mpr dist_nonneg

example : mr_base ∈ b6t_polydisc mr_base := hg3_base_mem_polydisc

/-- **The arcs avoid the marks at `mr_base`** (a check with a body, for every real parameter):
the arc has imaginary part `10 − 20 s`, so it meets the real axis only at `s = 1/2`, at the
half-integer `w_i`, while every finite mark of `mr_base` is an integer. (`hg3_arc_avoids`
claims more, at every `t` of the polydisc; this check does not use it.) -/
theorem hg3_arc_mem_base (i : Fin 13) (s : ℝ) :
    ((hg3_arc i s : ℂ) : OnePoint ℂ) ∈ b6t_punctured mr_base := by
  have him : ∀ i s, (hg3_arc i s).im = 10 - 20 * s := by
    intro i s
    simp only [hg3_arc, mr_basePoint, hg3_bottom, mr_centre, add_im, mul_im, ofReal_re,
      ofReal_im, sub_im, sub_re, add_re, mul_re, I_re, I_im, div_ofNat_re, div_ofNat_im]
    norm_num
    rcases le_total s (1 / 2) with h | h
    · rw [min_eq_left h, max_eq_right h]; ring
    · rw [min_eq_right h, max_eq_left h]; ring
  have hre : ∀ i, (hg3_arc i (1 / 2)).re = hg3_waist i := by
    intro i
    simp only [hg3_arc, mr_basePoint, hg3_bottom, mr_centre, add_re, mul_re, ofReal_re,
      ofReal_im, sub_re, sub_im, add_im, mul_im, I_re, I_im, div_ofNat_re, div_ofNat_im]
    norm_num
  have hhalf : ∀ i, ∃ n : ℤ, hg3_waist i = n + 1 / 2 := by
    intro i
    fin_cases i
    exacts [⟨-13, by norm_num [hg3_waist]⟩, ⟨-12, by norm_num [hg3_waist]⟩,
      ⟨-11, by norm_num [hg3_waist]⟩, ⟨-10, by norm_num [hg3_waist]⟩,
      ⟨-9, by norm_num [hg3_waist]⟩, ⟨-8, by norm_num [hg3_waist]⟩,
      ⟨-7, by norm_num [hg3_waist]⟩, ⟨-6, by norm_num [hg3_waist]⟩,
      ⟨-5, by norm_num [hg3_waist]⟩, ⟨-4, by norm_num [hg3_waist]⟩,
      ⟨-2, by norm_num [hg3_waist]⟩, ⟨0, by norm_num [hg3_waist]⟩, ⟨1, by norm_num [hg3_waist]⟩]
  have hmark : ∀ j : Fin 13, b6_branch mr_base j = OnePoint.infty ∨
      b6_branch mr_base j = ((((if j.val < 10 then (j.val : ℤ) - 12 else (j.val : ℤ) - 10 : ℤ)
        : ℝ) : ℂ) : OnePoint ℂ) := by
    intro j
    fin_cases j
    all_goals first
      | exact Or.inl rfl
      | (refine Or.inr ?_; simp [b6_branch, mr_base, Fin.append, Fin.addCases] <;> norm_num)
  simp only [b6t_punctured, Set.mem_compl_iff, Set.mem_range, not_exists]
  intro j hj
  have hm : b6_branch mr_base j = OnePoint.infty ∨
      ∃ m : ℤ, b6_branch mr_base j = (((m : ℝ) : ℂ) : OnePoint ℂ) :=
    (hmark j).imp id fun h ↦ ⟨_, h⟩
  rcases hm with h | ⟨m, h⟩
  · rw [h] at hj
    exact OnePoint.coe_ne_infty _ hj.symm
  · rw [h] at hj
    have he := OnePoint.coe_injective hj
    have h1 := congrArg Complex.im he
    have h2 := congrArg Complex.re he
    rw [him, ofReal_im] at h1
    have hs : s = 1 / 2 := by linarith
    subst hs
    rw [hre, ofReal_re] at h2
    obtain ⟨n, hn⟩ := hhalf i
    rw [hn] at h2
    have h3 : ((2 * m : ℤ) : ℝ) = ((2 * n + 1 : ℤ) : ℝ) := by push_cast; linarith
    have h4 := Int.cast_injective h3
    omega

/-- **The arc paths at `mr_base`.** For base points at `b₀` and `b_∞`, the thirteen arcs are
paths in the punctured sphere at the base configuration (`hg3_arc_mem_base`; continuity of
`min` and `max`). -/
theorem hg3_arc_paths_base (y₀ y₁ : b6t_punctured mr_base)
    (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (hy₁ : (y₁ : OnePoint ℂ) = ((hg3_bottom : ℂ) : OnePoint ℂ)) :
    ∃ F : Fin 13 → Path y₀ y₁,
      ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ) := by
  have hcont : ∀ i, Continuous (hg3_arc i) := by
    intro i
    unfold hg3_arc
    fun_prop
  have h0 : ∀ i, hg3_arc i 0 = mr_basePoint := by intro i; simp [hg3_arc]
  have h1 : ∀ i, hg3_arc i 1 = hg3_bottom := by
    intro i
    have e1 : min (1 : ℝ) (1 / 2) = 1 / 2 := by norm_num
    have e2 : max (1 : ℝ) (1 / 2) = 1 := by norm_num
    simp only [hg3_arc, e1, e2]
    push_cast
    ring
  refine ⟨fun i ↦ ⟨⟨fun s ↦ ⟨_, hg3_arc_mem_base i s⟩, ?_⟩, ?_, ?_⟩, fun i s ↦ rfl⟩
  · exact (OnePoint.continuous_coe.comp ((hcont i).comp continuous_subtype_val)).subtype_mk _
  · exact Subtype.ext (by simp [h0, hy₀])
  · exact Subtype.ext (by simp [h1, hy₁])

/-- **Joint satisfiability of the binders of `hg3_ell_isLoop`, `hg3_ell_endpoint` and
`hg3_arc_endpoint` against `b4b_root`.** At `t = mr_base` there are base points over `b₀` and
`b_∞`, the explicit loop classes `γ` (`mr_loop_existsUnique`), the marked root cover with
monodromy `op (b4b_root i)` on `γ i` (`mr_rootCover`), and the arc paths `F`
(`hg3_arc_paths_base`), all at once. For every other `t` of the polydisc the transported cover
`mr_rootCover_family` supplies the cover and the loops; the arc paths there are
`hg3_arc_existsUnique`. -/
example : ∃ (U : Type) (_ : TopologicalSpace U) (_ : MulAction b4b_Group U)
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ y₁ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀) (F : Fin 13 → Path y₀ y₁),
    (∀ i, mr_IsLoop mr_base y₀ i (γ i)) ∧
      (∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i)) ∧
      ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ) := by
  have hb₀ : ((mr_basePoint : ℂ) : OnePoint ℂ) ∈ b6t_punctured mr_base := by
    simpa [hg3_arc] using hg3_arc_mem_base 0 0
  have hb₁ : ((hg3_bottom : ℂ) : OnePoint ℂ) ∈ b6t_punctured mr_base := by
    have e1 : min (1 : ℝ) (1 / 2) = 1 / 2 := by norm_num
    have e2 : max (1 : ℝ) (1 / 2) = 1 := by norm_num
    have h := hg3_arc_mem_base 0 1
    have he : hg3_arc 0 1 = hg3_bottom := by
      simp only [hg3_arc, e1, e2]
      push_cast
      ring
    rwa [he] at h
  let y₀ : b6t_punctured mr_base := ⟨_, hb₀⟩
  let y₁ : b6t_punctured mr_base := ⟨_, hb₁⟩
  have hγ := fun i ↦
    (mr_loop_existsUnique mr_base hg3_base_mem_polydisc y₀ rfl i).exists.choose_spec
  obtain ⟨U, _, _, _, π, hπ, u₀, hroot, -⟩ := mr_rootCover y₀ _ hγ
  obtain ⟨F, hF⟩ := hg3_arc_paths_base y₀ y₁ rfl rfl
  exact ⟨U, inferInstance, inferInstance, π, hπ, y₀, y₁, u₀, _, F, hγ, hroot, hF⟩

/-- **Non-degeneracy of `hg3_ell_endpoint` at `b4b_root`.** The lift of every `ℓ_i` changes the
sheet: `x * b4b_root i ≠ x`, since `b4b_root i` has order `3`, or `2` for `i = 12`
(`b63_root_order`). This rules out the trivial monodromy. -/
example (i : Fin 13) (x : b4b_Group) : x * b4b_root i ≠ x := by
  intro h
  have h1 : b4b_root i = 1 := mul_eq_left.mp h
  have h2 := b63_root_order i
  rw [h1, orderOf_one] at h2
  split_ifs at h2 <;> omega

/-- **Non-degeneracy of `hg3_arc_endpoint` at `b4b_root`.** Consecutive arcs lifted from the
same sheet end at different labels over `b_∞`: `Q_{i+1} = Q_i g_i ≠ Q_i`. So the labelling of
the points over `b_∞` by `hg3_arc_endpoint` is not constant along the arcs. -/
example (i : Fin 12) : hg_Q b4b_root i.succ ≠ hg_Q b4b_root i.castSucc := by
  have hs : hg_Q b4b_root i.succ = hg_Q b4b_root i.castSucc * b4b_root i.castSucc :=
    hg_Q_succ b4b_root i.castSucc (by simp; omega)
  rw [hs]
  intro h
  have h1 : b4b_root i.castSucc = 1 := mul_eq_left.mp h
  have h2 := b63_root_order i.castSucc
  rw [h1, orderOf_one] at h2
  split_ifs at h2 <;> omega

/-- **Chain check toward H3a (`hg_tgt`).** The two endpoint formulas agree with the incidences of
H3a's complex for `b4b_root`: the arc `f_{i+1}` from the sheet `x * b4b_root i` and the arc
`f_i` from the sheet `x` end at the same vertex over `b_∞`, for every `i`, the wraparound
`i = 12` included (product one, `hg_Q_rotate`). This is the identity that `hg3_ell_endpoint`
and `hg3_arc_endpoint` give in the cover. -/
example (i : Fin 13) (x : b4b_Group) :
    hg_tgt b4b_root (Sum.inr (Sum.inl (finRotate 13 i, x * b4b_root i))) =
      hg_tgt b4b_root (Sum.inr (Sum.inl (i, x))) := by
  simp only [hg_tgt, hg_Q_rotate b4b_root b63d_root_product i, mul_inv_rev, mul_assoc,
    mul_inv_cancel_left]

/-- **Chain check toward the lifted cells (H3b item 3).** Under the binders of
`hg3_arc_endpoint` with `g = b4b_root`, the lift of `f_i` from the sheet `y` ends at the point
`z • v_∞` named by H3a's incidence `hg_tgt b4b_root (f_i(y)) = b_∞(z)`. So `b_∞(z) ↦ z • v_∞`
is the vertex map of the lifted cells on the `f`-edges. -/
example (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured t) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ y₁ : b6t_punctured t) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀) (hγ : ∀ i, mr_IsLoop t y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (Δ : C(unitInterval, U)) (hΔ : ∀ s, π (Δ s) = F 0 s) (hΔ0 : Δ 0 = (u₀ : U))
    (i : Fin 13) (y z : b4b_Group) (hz : hg_tgt b4b_root (Sum.inr (Sum.inl (i, y))) =
      Sum.inr (Sum.inl z))
    (Γ : C(unitInterval, U)) (hΓ : ∀ s, π (Γ s) = F i s) (h0 : Γ 0 = y • (u₀ : U)) :
    Γ 1 = z • Δ 1 := by
  simp only [hg_tgt, Sum.inr.injEq, Sum.inl.injEq] at hz
  rw [← hz]
  exact hg3_arc_endpoint t ht b4b_root U π hπ y₀ y₁ u₀ γ hγ hroot F hF Δ hΔ hΔ0 i y Γ hΓ h0

end HodgeLean.Foundations.Program

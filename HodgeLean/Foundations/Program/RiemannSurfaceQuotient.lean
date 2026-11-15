import HodgeLean.Foundations.Program.RiemannSurfaceQuotientProofs

/-! # Finite-group quotients of compact Riemann surfaces (FROZEN SPEC)

Each theorem is the matching `_aux` theorem of `RiemannSurfaceQuotientProofs.lean`. The objects
are built in `RiemannSurfaceQuotientDefs.lean`: the orbit space `rsq_Quot H X`
(`MulAction.orbitRel.Quotient H X` with the quotient topology), the quotient map `rsq_proj`,
the induced map `rsq_lift`, the action `rsq_quotAction` of `H ⧸ K` on `X ⧸ K` for `K ⊴ H`, and
the tower map `rsq_tower : (X ⧸ K) ⧸ (H ⧸ K) → X ⧸ H`. A compact connected Riemann surface is
B3's: `ChartedSpace E X`, `IsManifold 𝓘(ℂ, E) ω X` with `finrank ℂ E = 1`, `T2Space X`,
`CompactSpace X`, `ConnectedSpace X`. A finite group `H` acts faithfully by holomorphic maps:
`[Finite H] [FaithfulSMul H X]` and `hH : ∀ g, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (g • ·)`.

**Claimed (open statements).** The quotient map is nonconstant. The orbit space carries a
charted structure modelled on `ℂ` that is an analytic manifold, for which the quotient map is
holomorphic. For every such structure, a map out of the quotient is holomorphic once its
composite with the quotient map is (the quotient is the categorical quotient among complex
manifolds with finite-dimensional models). For `K ⊴ H`, the induced action of `H ⧸ K` on
`X ⧸ K` is faithful, its stabilizers satisfy `|Stab_{H ⧸ K}[x]| · |K_x| = |H_x|`, and the tower
map is a homeomorphism.

**Derived here from those statements and existing theorems (not restated).** Compactness,
connectedness and the Hausdorff property of `X ⧸ H` are Mathlib instances (example in the Defs
file). Stabilizers are cyclic with a unique rotation generator: `b4_exists_rotGen`,
`b4_rotGen_unique`. For any complex structure on `X ⧸ H` making the quotient map holomorphic,
the examples below derive: the ramification index at `x` is `|H_x|` (`b4_ramIndex_galois`; in
the local normal form the chart at the image is `z ↦ z^{|H_x|}`), the branch set is the image of
the points with nontrivial stabilizer, the degree is `|H|` (`b4_fiberDegree_galois`), and
Riemann–Hurwitz `2g(X) − 2 = |H| (2g(X/H) − 2) + Σ_x (|H_x| − 1)` with `g = dim Ω¹`
(`b4_riemannHurwitz`). Every element of `H ⧸ K` acts holomorphically on `X ⧸ K`, so
`(X ⧸ K) ⧸ (H ⧸ K)` again carries a structure, and the tower map is holomorphic.

**Instances.** Satisfiable instance, using no open statement: `μ₄` acting on `ℂ ⧸ (ℤ + iℤ)`
by `z ↦ i z` is faithful and holomorphic, of order four, with stabilizer of order four at `0`
(so the branch set is nonempty), on a surface of genus one; the normal subgroup `{1, σ²}` has
order two, as does the quotient group. Chain check: on every fibre of the retained family
`rf8_SharedFamily` and for every normal subgroup `K` of `b4b_Group`, any structure on the
intermediate curve `X ⧸ K` making the quotient map holomorphic makes the map
`X ⧸ K → ℙ¹` induced by `b63d_projection` holomorphic.

**Not claimed.** No uniqueness statement for the structure on the quotient is frozen, though
it follows from the descent statement. No algebraic curve, no comparison of `X ⧸ H` with a
scheme, and no character, kernel or Jacobian of an intermediate curve of the retained family.
Nothing reaches the `algebraic` field of `b63gV_OpenSupply`. HC no distance; AV milestone no
distance.
-/

noncomputable section

open Manifold
open scoped ContDiff

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

section Surface

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ω X]
variable {H : Type} [Group H] [Finite H] [MulAction H X]

/-- **The quotient map is nonconstant**: a nonempty surface modelled on a complex line is
infinite, and each orbit has at most `|H|` points.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §1.1 (charts onto open subsets of
`ℂ`); Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §3 (orbits of a finite group are
finite). Usable from Mathlib vocabulary alone. -/
theorem rsq_proj_nonconstant [ConnectedSpace X] (hE : Module.finrank ℂ E = 1) :
    ∃ x x' : X, rsq_proj H X x ≠ rsq_proj H X x' :=
  rsq_proj_nonconstant_aux hE

example [ConnectedSpace X] (hE : Module.finrank ℂ E = 1) :
    ¬ Subsingleton (rsq_Quot H X) := fun _ ↦ by
  obtain ⟨x, x', hx⟩ := rsq_proj_nonconstant (X := X) (H := H) hE
  exact hx (Subsingleton.elim _ _)

/-- **The quotient is a Riemann surface and the quotient map is holomorphic**: near a point `x`
with stabilizer of order `n`, in a coordinate where `H_x` acts by rotations, the chart of the
quotient at `[x]` is `z ↦ zⁿ`; at points with trivial stabilizer the quotient map is a local
homeomorphism and the charts are those of `X`.
Source: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III, Theorem 3.4; Forster,
*Lectures on Riemann Surfaces*, §4 (quotients and branched coverings). Usable from Mathlib
vocabulary alone. -/
theorem rsq_exists_manifold [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (hE : Module.finrank ℂ E = 1) [FaithfulSMul H X]
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x)) :
    ∃ cs : ChartedSpace ℂ (rsq_Quot H X), letI := cs
      IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot H X) ∧ ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (rsq_proj H X) :=
  rsq_exists_manifold_aux hE hH

example [T2Space X] [CompactSpace X] [ConnectedSpace X] (hE : Module.finrank ℂ E = 1)
    [FaithfulSMul H X] (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x)) :
    Nonempty (ChartedSpace ℂ (rsq_Quot H X)) :=
  let ⟨cs, _⟩ := rsq_exists_manifold hE hH
  ⟨cs⟩

/-- **Descent of holomorphic maps**: for any complex structure on `X ⧸ H` making the quotient
map holomorphic, a map `f` out of the quotient is holomorphic once `f ∘ π` is. In the chart
`s = zⁿ` at a branch point, `f` is continuous and `f(zⁿ)` is holomorphic, so `f` is holomorphic
off the centre and extends across it (Riemann's removable singularity theorem).
Source: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §3 (holomorphic functions on
`X ⧸ G` are the `G`-invariant holomorphic functions on `X`); Forster, *Lectures on Riemann
Surfaces*, Theorem 1.8 (removable singularities). Usable from Mathlib vocabulary alone. -/
theorem rsq_contMDiff_of_comp [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (hE : Module.finrank ℂ E = 1) [FaithfulSMul H X]
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    [ChartedSpace ℂ (rsq_Quot H X)] [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot H X)]
    (hπ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (rsq_proj H X))
    {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
    {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]
    (f : rsq_Quot H X → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω (f ∘ rsq_proj H X)) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, E') ω f :=
  rsq_contMDiff_of_comp_aux hE hH hπ f hf

/-- A map induced by a holomorphic `H`-invariant map is holomorphic. -/
example [T2Space X] [CompactSpace X] [ConnectedSpace X] (hE : Module.finrank ℂ E = 1)
    [FaithfulSMul H X] (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    [ChartedSpace ℂ (rsq_Quot H X)] [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot H X)]
    (hπ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (rsq_proj H X)) (u : X → ℂ)
    (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω u) (hinv : ∀ (g : H) (x : X), u (g • x) = u x) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_lift u hinv) :=
  rsq_contMDiff_of_comp hE hH hπ _ hu

/-- **The induced action of `H ⧸ K` on `X ⧸ K` is faithful**: if `h` moves every point into its
`K`-orbit, then at a point with trivial stabilizer (all but finitely many points, the fixed
points of a nontrivial holomorphic automorphism being isolated) `h` agrees with an element of
`K`, so `h ∈ K`.
Source: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §3 (quotients in stages);
Forster, *Lectures on Riemann Surfaces*, §1.11 (identity theorem). Usable from Mathlib
vocabulary alone. -/
theorem rsq_faithful_quotient [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (hE : Module.finrank ℂ E = 1) [FaithfulSMul H X]
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    (K : Subgroup H) [K.Normal] :
    FaithfulSMul (H ⧸ K) (rsq_Quot K X) :=
  rsq_faithful_quotient_aux hE hH K

example [T2Space X] [CompactSpace X] [ConnectedSpace X] (hE : Module.finrank ℂ E = 1)
    [FaithfulSMul H X] (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    (K : Subgroup H) [K.Normal] (h : H) (hh : ∀ x : X, (h : H ⧸ K) • rsq_proj K X x = rsq_proj K X x) :
    h ∈ K := by
  have := rsq_faithful_quotient hE hH K
  have h1 : (h : H ⧸ K) = 1 := eq_of_smul_eq_smul fun q ↦ by
    induction q using Quotient.inductionOn' with
    | h x => rw [one_smul]; exact hh x
  exact (QuotientGroup.eq_one_iff h).1 h1

end Surface

/-- **Stabilizers in the quotient action**: the stabilizer of `[x]` in `H ⧸ K` is the image
`H_x K ⧸ K ≅ H_x ⧸ (H_x ∩ K)` and `H_x ∩ K = K_x`, so `|Stab_{H ⧸ K}[x]| · |K_x| = |H_x|`.
Source: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §3 (ramification in a tower of
quotients); Mathlib `MulAction.stabilizer`, `Subgroup.card_mul_index`. Usable from Mathlib
vocabulary alone. -/
theorem rsq_card_stabilizer_quotient {H X : Type} [Group H] [Finite H] [MulAction H X]
    (K : Subgroup H) [K.Normal] (x : X) :
    Nat.card (MulAction.stabilizer (H ⧸ K) (rsq_proj K X x)) *
      Nat.card (MulAction.stabilizer K x) = Nat.card (MulAction.stabilizer H x) :=
  rsq_card_stabilizer_quotient_aux K x

/-- For `K = ⊤` the quotient group has trivial stabilizers, so `K_x = H_x`. -/
example {H X : Type} [Group H] [Finite H] [MulAction H X] (x : X)
    (h1 : Nat.card (MulAction.stabilizer (H ⧸ (⊤ : Subgroup H)) (rsq_proj (⊤ : Subgroup H) X x)) = 1) :
    Nat.card (MulAction.stabilizer (⊤ : Subgroup H) x) = Nat.card (MulAction.stabilizer H x) := by
  rw [← rsq_card_stabilizer_quotient (⊤ : Subgroup H) x, h1, one_mul]

/-- **Quotients in stages**: for `K ⊴ H` the tower map `(X ⧸ K) ⧸ (H ⧸ K) → X ⧸ H` is a
homeomorphism. Both sides are quotients of `X` by the same equivalence relation, and a
composite of quotient maps is a quotient map.
Source: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §3; Bourbaki, *Topologie
générale*, ch. I, §3.4 (composites of quotient maps). Usable from Mathlib vocabulary alone. -/
theorem rsq_tower_isHomeomorph {H X : Type} [Group H] [MulAction H X] [TopologicalSpace X]
    (K : Subgroup H) [K.Normal] :
    IsHomeomorph (rsq_tower (X := X) K) :=
  rsq_tower_isHomeomorph_aux K

example {H X : Type} [Group H] [MulAction H X] [TopologicalSpace X] (K : Subgroup H)
    [K.Normal] : Function.Injective (rsq_tower (X := X) K) :=
  (rsq_tower_isHomeomorph K).injective

/-! ## Branch data and Riemann–Hurwitz for every compatible structure

These examples combine the statements above with B4's frozen theorems; none is restated. -/

section Derived

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ω X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]
variable {H : Type} [Group H] [Finite H] [MulAction H X] [FaithfulSMul H X]

/-- Ramification index `|H_x|` at `x` (`b4_ramIndex_galois`). -/
example (hE : Module.finrank ℂ E = 1)
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    [ChartedSpace ℂ (rsq_Quot H X)] [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot H X)]
    (hπ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (rsq_proj H X)) (x : X) :
    b4_ramIndex E ℂ (rsq_proj H X) x = Nat.card (MulAction.stabilizer H x) := by
  have := rsq_t2Space hE fun g ↦ (hH g).continuous
  exact b4_ramIndex_galois hE (Module.finrank_self ℂ) hH _ hπ (rsq_proj_isGaloisCover H X) x

/-- The branch set is the image of the points with nontrivial stabilizer. -/
example (hE : Module.finrank ℂ E = 1)
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    [ChartedSpace ℂ (rsq_Quot H X)] [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot H X)]
    (hπ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (rsq_proj H X)) :
    b4_branchSet E ℂ (rsq_proj H X) =
      rsq_proj H X '' {x | MulAction.stabilizer H x ≠ ⊥} := by
  have := rsq_t2Space hE fun g ↦ (hH g).continuous
  refine congrArg (rsq_proj H X '' ·) (Set.ext fun x ↦ ?_)
  change 2 ≤ b4_ramIndex E ℂ (rsq_proj H X) x ↔ _
  rw [b4_ramIndex_galois hE (Module.finrank_self ℂ) hH _ hπ (rsq_proj_isGaloisCover H X) x]
  exact Subgroup.one_lt_card_iff_ne_bot _

/-- Degree `|H|` over every point (`b4_fiberDegree_galois`). -/
example (hE : Module.finrank ℂ E = 1)
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    [ChartedSpace ℂ (rsq_Quot H X)] [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot H X)]
    (hπ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (rsq_proj H X)) (y : rsq_Quot H X) :
    b4_fiberDegree E ℂ (rsq_proj H X) y = Nat.card H := by
  have := rsq_t2Space hE fun g ↦ (hH g).continuous
  exact b4_fiberDegree_galois hE (Module.finrank_self ℂ) hH _ hπ (rsq_proj_isGaloisCover H X) y

/-- **Riemann–Hurwitz for the quotient**, `2g(X) − 2 = |H| (2g(X/H) − 2) + Σ_x (|H_x| − 1)`,
from `b4_riemannHurwitz`, `b4_fiberDegree_galois` and `b4_ramIndex_galois`. -/
example (hE : Module.finrank ℂ E = 1)
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    [ChartedSpace ℂ (rsq_Quot H X)] [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot H X)]
    (hπ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (rsq_proj H X)) :
    2 * (Module.finrank ℂ (b3_HolForm E X) : ℤ) - 2 =
      Nat.card H * (2 * (Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot H X)) : ℤ) - 2) +
        ∑ᶠ x : X, ((Nat.card (MulAction.stabilizer H x) : ℤ) - 1) := by
  have := rsq_t2Space hE fun g ↦ (hH g).continuous
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have h := b4_riemannHurwitz hE (Module.finrank_self ℂ) (rsq_proj H X) hπ
    (rsq_proj_nonconstant hE) (rsq_proj H X x₀)
  rw [b4_fiberDegree_galois hE (Module.finrank_self ℂ) hH _ hπ (rsq_proj_isGaloisCover H X)] at h
  simp_rw [b4_ramIndex_galois hE (Module.finrank_self ℂ) hH _ hπ
    (rsq_proj_isGaloisCover H X)] at h
  exact h

variable (hE : Module.finrank ℂ E = 1)
  (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
  (K : Subgroup H) [K.Normal]
  [ChartedSpace ℂ (rsq_Quot K X)] [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot K X)]
  (hπK : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (rsq_proj K X))
include hE hH hπK

/-- Every element of `H ⧸ K` acts holomorphically on `X ⧸ K` (descent of `[x] ↦ [h x]`). -/
example (a : H ⧸ K) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun q : rsq_Quot K X ↦ a • q) := by
  induction a using QuotientGroup.induction_on with
  | H h => exact rsq_contMDiff_of_comp hE (fun k : K ↦ hH k) hπK _ (hπK.comp (hH h))

/-- The second stage: `(X ⧸ K) ⧸ (H ⧸ K)` carries a structure making its quotient map
holomorphic. -/
example : ∃ cs : ChartedSpace ℂ (rsq_Quot (H ⧸ K) (rsq_Quot K X)), letI := cs
      IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot (H ⧸ K) (rsq_Quot K X)) ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_proj (H ⧸ K) (rsq_Quot K X)) := by
  have := rsq_t2Space (H := K) hE fun k ↦ (hH k).continuous
  have := rsq_faithful_quotient hE hH K
  exact rsq_exists_manifold (Module.finrank_self ℂ) (fun a ↦ by
    induction a using QuotientGroup.induction_on with
    | H h => exact rsq_contMDiff_of_comp hE (fun k : K ↦ hH k) hπK _ (hπK.comp (hH h)))

/-- For compatible structures on all three quotients, the tower map is holomorphic. -/
example [ChartedSpace ℂ (rsq_Quot H X)] [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot H X)]
    (hπ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (rsq_proj H X))
    [ChartedSpace ℂ (rsq_Quot (H ⧸ K) (rsq_Quot K X))]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot (H ⧸ K) (rsq_Quot K X))]
    (hπ' : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_proj (H ⧸ K) (rsq_Quot K X))) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_tower (X := X) K) := by
  have := rsq_t2Space (H := K) hE fun k ↦ (hH k).continuous
  have := rsq_faithful_quotient hE hH K
  have hc : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_coarsen (X := X) K) :=
    rsq_contMDiff_of_comp hE (fun k : K ↦ hH k) hπK _ hπ
  exact rsq_contMDiff_of_comp (Module.finrank_self ℂ) (fun a ↦ by
    induction a using QuotientGroup.induction_on with
    | H h => exact rsq_contMDiff_of_comp hE (fun k : K ↦ hH k) hπK _ (hπK.comp (hH h))) hπ' _ hc

end Derived

/-! ## Satisfiable instance and chain check -/

/-- **Satisfiable, nondegenerate instance** (no open statement used): `μ₄` acting on
`ℂ ⧸ (ℤ + iℤ)` by `z ↦ i z` meets every hypothesis, the group has order four (not trivial),
the stabilizer of `0` has order four (a genuine branch point), the surface has genus one (not
rank zero), and `{1, σ²}` and `μ₄ ⧸ {1, σ²}` both have order two. -/
example : Module.finrank ℂ b3_EllipticModel = 1 ∧
    FaithfulSMul (Multiplicative (ZMod 4)) b3_Elliptic ∧
    (∀ g : Multiplicative (ZMod 4),
      ContMDiff 𝓘(ℂ, b3_EllipticModel) 𝓘(ℂ, b3_EllipticModel) ω (fun x : b3_Elliptic ↦ g • x)) ∧
    Nat.card (Multiplicative (ZMod 4)) = 4 ∧
    Nat.card (MulAction.stabilizer (Multiplicative (ZMod 4)) (0 : b3_Elliptic)) = 4 ∧
    Module.finrank ℂ (b3_HolForm b3_EllipticModel b3_Elliptic) = 1 ∧
    Nat.card rsq_mu2 = 2 ∧ Nat.card (Multiplicative (ZMod 4) ⧸ rsq_mu2) = 2 := by
  have h4 : Nat.card (Multiplicative (ZMod 4)) = 4 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  refine ⟨b3_ellipticModel_finrank, b4_ellipticRot_faithful, b4_ellipticRot_contMDiff, h4, ?_,
    b3_elliptic_finrank_holForm, rsq_mu2_card, ?_⟩
  · rw [rsq_mu4_stabilizer_zero, Subgroup.card_top, h4]
  · have := Subgroup.card_eq_card_quotient_mul_card_subgroup rsq_mu2
    rw [h4, rsq_mu2_card] at this
    omega

/-- **Chain check** toward the intermediate curves of the retained family: on every fibre of
`rf8_SharedFamily` and for every normal subgroup `K` of `b4b_Group`, any structure on `X ⧸ K`
making its quotient map holomorphic makes the map `X ⧸ K → ℙ¹` induced by `b63d_projection`
holomorphic. This is the tower `X → X ⧸ K → ℙ¹` of `docs/specs/SchoenSupplierBridge.md`; no
character or kernel is chosen here. -/
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (K : Subgroup b4b_Group) [K.Normal]
    [ChartedSpace ℂ (rsq_Quot K (rf8_fibre R.C t))]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot K (rf8_fibre R.C t))]
    (hπ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_proj K (rf8_fibre R.C t))) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (rsq_lift (H := K) (b63d_projection mr_base R.C R.atlas.f (b6t_polydisc mr_base)
        (Set.Subset.refl _) t) fun k x ↦ (R.hgal t).1 k x) :=
  rsq_contMDiff_of_comp (Module.finrank_self ℂ) (fun k : K ↦ R.hG t k) hπ _ (R.hk t)

/-- The chain check is not vacuous: the retained family exists, by a frozen theorem that uses
none of this lane's statements. -/
example : Nonempty rf8_SharedFamily :=
  let ⟨R, _⟩ := rf8_shared_root
  ⟨R⟩

end HodgeLean.Foundations.Program

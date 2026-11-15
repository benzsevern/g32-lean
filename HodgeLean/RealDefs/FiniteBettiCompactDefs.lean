import HodgeLean.RealDefs.TopDegreeRank
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.MayerVietoris

/-! # Finite Betti numbers of compact charted spaces (FROZEN DEFINITIONS)

Definitions for the spec `HodgeLean/RealDefs/FiniteBettiCompact.lean`
(`docs/specs/FiniteBettiCompact.md`). Homology is upstream's rational singular
`Homology ℚ (TopCat.of Y) i`; a subset `U : Set Y` is the subspace `TopCat.of ↥U`.

* `subsetInclusionHom h`: for `V ⊆ U ⊆ Y`, the inclusion `V → U` as a `TopCat` morphism.
* `FiniteHomology Y`: every `H_i(Y; ℚ)` is a finite-dimensional `ℚ`-vector space.
* `FiniteHomologyImage h`: for `V ⊆ U`, every image of `H_i(V; ℚ) → H_i(U; ℚ)` is
  finite-dimensional.
* `subsetMayerVietorisBoundary hU hV n : H_{n+1}(U ∪ V; ℚ) → H_n(U ∩ V; ℚ)`, for open `U`, `V`:
  upstream's Mayer–Vietoris boundary `singularMayerVietorisBoundary` of the open cover of the
  space `U ∪ V` by the preimages of `U` and `V`, followed by the identification of the overlap
  with `U ∩ V`.

These are data and predicates only; every statement of the spec takes its hypotheses as explicit
binders. -/

noncomputable section

open CategoryTheory AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

/-- The inclusion `V → U` of subspaces of `Y`, for `V ⊆ U`, as a morphism of `TopCat`.

Source: Hatcher, *Algebraic Topology*, §2.1 (maps induced on singular homology by continuous
maps); `Set.inclusion` with `continuous_inclusion`. -/
def subsetInclusionHom {Y : Type} [TopologicalSpace Y] {V U : Set Y} (h : V ⊆ U) :
    TopCat.of V ⟶ TopCat.of U :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

example {Y : Type} [TopologicalSpace Y] {V U : Set Y} (h : V ⊆ U) (v : V) :
    ((subsetInclusionHom h) v : Y) = v :=
  rfl

/-- Finite rational Betti numbers: every singular homology group `H_i(Y; ℚ)` is a
finite-dimensional `ℚ`-vector space.

Source: Hatcher, *Algebraic Topology*, Appendix, Corollary A.8 and the remarks after it (a compact
manifold has finitely generated homology). -/
def FiniteHomology (Y : Type) [TopologicalSpace Y] : Prop :=
  ∀ i : ℕ, Module.Finite ℚ (Homology ℚ (TopCat.of Y) i)

example (Y : Type) [TopologicalSpace Y] :
    FiniteHomology Y ↔ ∀ i : ℕ, Module.Finite ℚ (Homology ℚ (TopCat.of Y) i) :=
  Iff.rfl

/-- For `V ⊆ U ⊆ Y`, the image of `H_i(V; ℚ) → H_i(U; ℚ)` is finite-dimensional in every degree.

Source: Hatcher, *Algebraic Topology*, §2.1 (maps induced on singular homology); the predicate is
the finite-rank form of finiteness that the Mayer–Vietoris induction of
`docs/specs/FiniteBettiCompact.md` carries through nested open sets. -/
def FiniteHomologyImage {Y : Type} [TopologicalSpace Y] {V U : Set Y} (h : V ⊆ U) : Prop :=
  ∀ i : ℕ, Module.Finite ℚ (LinearMap.range (homologyMap ℚ i (subsetInclusionHom h)))

example {Y : Type} [TopologicalSpace Y] {V U : Set Y} (h : V ⊆ U) :
    FiniteHomologyImage h ↔
      ∀ i : ℕ, Module.Finite ℚ (LinearMap.range (homologyMap ℚ i (subsetInclusionHom h))) :=
  Iff.rfl

/-- The preimage of `U` in the subspace `U ∪ V`.
Source: Hatcher, *Algebraic Topology*, §2.2, "Mayer–Vietoris Sequences" (the open cover of
`U ∪ V` by `U` and `V`). -/
abbrev subsetUnionLeft {Y : Type} (U V : Set Y) : Set ↥(U ∪ V) :=
  Subtype.val ⁻¹' U

example {Y : Type} (U V : Set Y) (p : ↥(U ∪ V)) : p ∈ subsetUnionLeft U V ↔ (p : Y) ∈ U :=
  Iff.rfl

/-- The preimage of `V` in the subspace `U ∪ V`.
Source: Hatcher, *Algebraic Topology*, §2.2, "Mayer–Vietoris Sequences". -/
abbrev subsetUnionRight {Y : Type} (U V : Set Y) : Set ↥(U ∪ V) :=
  Subtype.val ⁻¹' V

example {Y : Type} (U V : Set Y) (p : ↥(U ∪ V)) : p ∈ subsetUnionRight U V ↔ (p : Y) ∈ V :=
  Iff.rfl

theorem subsetUnionLeft_union_right {Y : Type} (U V : Set Y) :
    subsetUnionLeft U V ∪ subsetUnionRight U V = Set.univ :=
  Set.eq_univ_of_forall fun p => p.2

/-- The overlap of the two preimages, mapped to `U ∩ V ⊆ Y`.
Source: Hatcher, *Algebraic Topology*, §2.2, "Mayer–Vietoris Sequences" (the intersection term of
the sequence for the cover of `U ∪ V`). -/
def subsetOverlapHom {Y : Type} [TopologicalSpace Y] (U V : Set Y) :
    TopCat.of ↥(subsetUnionLeft U V ∩ subsetUnionRight U V) ⟶ TopCat.of ↥(U ∩ V) :=
  TopCat.ofHom ⟨fun p => ⟨p.1.1, p.2.1, p.2.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

example {Y : Type} [TopologicalSpace Y] (U V : Set Y)
    (p : ↥(subsetUnionLeft U V ∩ subsetUnionRight U V)) :
    ((subsetOverlapHom U V p : ↥(U ∩ V)) : Y) = ((p : ↥(U ∪ V)) : Y) :=
  rfl

/-- The Mayer–Vietoris boundary `H_{n+1}(U ∪ V; ℚ) → H_n(U ∩ V; ℚ)` for open `U`, `V ⊆ Y`:
upstream's `singularMayerVietorisBoundary` for the open cover of the subspace `U ∪ V` by the
preimages of `U` and `V`, followed by `subsetOverlapHom` on homology.

Source: Hatcher, *Algebraic Topology*, §2.2, subsection "Mayer–Vietoris Sequences" (the
Mayer–Vietoris sequence and its boundary map). -/
def subsetMayerVietorisBoundary {Y : Type} [TopologicalSpace Y] {U V : Set Y} (hU : IsOpen U)
    (hV : IsOpen V) (n : ℕ) :
    Homology ℚ (TopCat.of ↥(U ∪ V)) (n + 1) →ₗ[ℚ] Homology ℚ (TopCat.of ↥(U ∩ V)) n :=
  homologyMap ℚ n (subsetOverlapHom U V) ∘ₗ
    (singularMayerVietorisBoundary (TopCat.of ↥(U ∪ V)) (subsetUnionLeft U V)
      (subsetUnionRight U V) (hU.preimage continuous_subtype_val)
      (hV.preimage continuous_subtype_val) (subsetUnionLeft_union_right U V) n).hom

example {Y : Type} [TopologicalSpace Y] {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V) :
    Homology ℚ (TopCat.of ↥(U ∪ V)) 1 →ₗ[ℚ] Homology ℚ (TopCat.of ↥(U ∩ V)) 0 :=
  subsetMayerVietorisBoundary hU hV 0

end HodgeLean.RealDefs

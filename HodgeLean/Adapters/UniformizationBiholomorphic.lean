import HodgeLean.Adapters.UniformizationBiholomorphicProofs

/-! # The uniformization as complex manifolds: frozen specification

S12 (`HodgeLean/Foundations/Uniformization.lean`) gives the exponential `exp : ℂ^d → X(ℂ)` of a
smooth commutative complex group scheme (`complexExponential`), its kernel
`Λ = complexExponentialLattice X d` (discrete), openness, a local homeomorphism at `0`, and, for
`X` integral and projective, surjectivity and the homeomorphism of topological groups
`ℂ^d ⧸ Λ ≃ X(ℂ)` (`complexExponentialQuotientEquiv`). Stage 4e
(`HodgeLean/Adapters/ExpHolomorphic.lean`) gives `exp` holomorphic and `X(ℂ)` a complex Lie group.
This file freezes the complex-analytic identification, phrased through `exp` itself: Mathlib has
no analytic manifold structure on `ℂ^d ⧸ Λ` (its quotient charted space is for
`orbitRel.Quotient` and does not apply to `(Fin d → ℂ) ⧸ Λ` by instance search, and the
`IsManifold` instance on quotients is a Mathlib TODO).

Claimed:
* for smooth commutative `X`: the manifold derivative of `exp` is invertible at every point;
* for smooth commutative `X`: `exp` is a local biholomorphism, i.e. every point has an open
  neighbourhood on which `exp` agrees with an open partial homeomorphism whose inverse is
  holomorphic;
* for smooth commutative, integral, projective `X`: `exp` is a quotient covering map for the
  translation action of `Λ`, so its fibres are exactly the cosets `v + Λ`;
* for smooth commutative, integral, projective `X`: a function `F : X(ℂ) → ℂ` is holomorphic if
  and only if `F ∘ exp` is holomorphic on `ℂ^d`;
* for smooth commutative, integral, projective `X`: a `Λ`-periodic holomorphic function on `ℂ^d`
  descends to a unique holomorphic function on `X(ℂ)`, the implication from the previous
  statement and surjectivity;
* falsification: the quotient of `ℂ` by the non-discrete subgroup `ℚ` is not Hausdorff, and the
  quotient of `ℂ` by the discrete but non-full subgroup `ℤ` is not compact.

Not claimed: an analytic manifold structure on `ℂ^d ⧸ Λ` or a biholomorphism
`ℂ^d ⧸ Λ ≃ X(ℂ)` as manifolds; any identification of the line bundle `L(H, χ)` on `ℂ^d ⧸ Λ`
with a line bundle on `X(ℂ)`; the descent of non-periodic theta functions (sections for a
nontrivial factor of automorphy) (`docs/specs/UniformizationBiholomorphic.md`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint
open HodgeLean.Foundations
open Filter Topology
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace HodgeLean.Adapters

/-- For a smooth commutative group scheme, the manifold derivative of the uniformization `exp` is
invertible at every point: at `0`, in the chart `localChart X d 1 = identityChart + c`, the
derivative is the identity (S12's `hasFDerivAt_complexExponential_chart`); at `v`,
`exp = (exp v * ·) ∘ exp ∘ (· - v)`, and left translation is a biholomorphism (stage 4e), so its
derivative is invertible.

Source: Mumford, *Abelian Varieties*, §1 (the exponential of a complex Lie group is a local
isomorphism); Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; through S12's
`hasFDerivAt_complexExponential_chart`, `complexExponentialHom` and stage 4e's
`spec_contMDiff_mul_left`, `spec_mdifferentiable_complexExponential`. -/
theorem spec_isInvertible_mfderiv_complexExponential (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] (v : Fin d → ℂ) :
    (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ)
      (fun w ↦ (complexExponential X d w).toMul) v).IsInvertible :=
  spec_isInvertible_mfderiv_complexExponential_aux X d v

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] :
    (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ)
      (fun w ↦ (complexExponential X d w).toMul) 0).IsInvertible :=
  spec_isInvertible_mfderiv_complexExponential X d 0

/-- For a smooth commutative group scheme, the uniformization `exp` is a local biholomorphism:
every `v` lies in the source of an open partial homeomorphism `e : ℂ^d → X(ℂ)` which agrees with
`exp` on its source and whose inverse is holomorphic on its target. At `0` this is the analytic
inverse function theorem (`ContDiffAt.toOpenPartialHomeomorph`, valid for `ω`) applied to the
analytic germ `identityChart ∘ exp` (stage 4e) with derivative the identity (S12), followed by the
inverse of the identity chart; at `v` it is translated by `exp v`.

Source: Mumford, *Abelian Varieties*, §1; Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed.,
§1.1; through stage 4e's `spec_analyticAt_complexExponential_chart` and
`spec_lieGroup_complexPoint`, S12's `hasFDerivAt_complexExponential_chart`, and Mathlib's
`ContDiffAt.toOpenPartialHomeomorph`. -/
theorem spec_complexExponential_localBiholomorph (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] (v : Fin d → ℂ) :
    ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (ComplexPoint X),
      v ∈ e.source ∧ Set.EqOn (fun w ↦ (complexExponential X d w).toMul) e e.source ∧
        ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω e.symm e.target :=
  spec_complexExponential_localBiholomorph_aux X d v

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] (v : Fin d → ℂ) :
    ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (ComplexPoint X),
      v ∈ e.source ∧ ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω e e.source ∧
        ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω e.symm e.target := by
  obtain ⟨e, hv, he, hs⟩ := spec_complexExponential_localBiholomorph X d v
  exact ⟨e, hv, (spec_contMDiff_complexExponential X d).contMDiffOn.congr
    fun w hw ↦ (he hw).symm, hs⟩

/-- For a smooth commutative, integral, projective group scheme, the uniformization `exp` is a
quotient covering map for the translation action of the period lattice `Λ` on `ℂ^d`: it is a
quotient map (continuous, open and onto, S12), `exp a = exp b` if and only if `a ∈ Λ + b`
(the kernel is `Λ`), and every point has a neighbourhood disjoint from its nonzero `Λ`-translates
(`Λ` is discrete, S12's `discrete_complexExponentialLattice`).

Source: Mumford, *Abelian Varieties*, §1; Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed.,
§1.1; through S12's `surjective_complexExponential`, `isOpenMap_complexExponential` and
`discrete_complexExponentialLattice`, and Mathlib's
`Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup`. -/
theorem spec_isAddQuotientCoveringMap_complexExponential (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    [IsIntegral X.left] [IsProjective X.hom] :
    IsAddQuotientCoveringMap (fun v ↦ (complexExponential X d v).toMul)
      (complexExponentialLattice X d).toAddSubgroup :=
  spec_isAddQuotientCoveringMap_complexExponential_aux X d

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom] :
    IsCoveringMap (fun v ↦ (complexExponential X d v).toMul) :=
  (spec_isAddQuotientCoveringMap_complexExponential X d).isCoveringMap

/-- For a smooth commutative, integral, projective group scheme, holomorphy on `X(ℂ)` is tested on
`ℂ^d`: `F : X(ℂ) → ℂ` is holomorphic if and only if `F ∘ exp` is analytic. Forward, compose with
the holomorphic `exp` (stage 4e); backward, every point of `X(ℂ)` is some `exp v` (S12), and near
it `F = (F ∘ exp) ∘ e.symm` for the local biholomorphism `e` at `v`.

Source: Mumford, *Abelian Varieties*, §1; Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed.,
§1.1 (functions on `ℂ^g / Λ` are `Λ`-periodic functions on `ℂ^g`); through
`spec_complexExponential_localBiholomorph`, stage 4e's `spec_contMDiff_complexExponential` and S12's
`surjective_complexExponential`. -/
theorem spec_contMDiff_iff_contDiff_comp_complexExponential (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    [IsIntegral X.left] [IsProjective X.hom] (F : ComplexPoint X → ℂ) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω F ↔
      ContDiff ℂ ω (fun v ↦ F (complexExponential X d v).toMul) :=
  spec_contMDiff_iff_contDiff_comp_complexExponential_aux X d F

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (F : ComplexPoint X → ℂ) (hF : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω F) :
    Differentiable ℂ (fun v ↦ F (complexExponential X d v).toMul) :=
  ((spec_contMDiff_iff_contDiff_comp_complexExponential X d F).mp hF).differentiable (by simp)

/-- For a smooth commutative, integral, projective group scheme, a `Λ`-periodic analytic function
`f` on `ℂ^d` descends to a unique holomorphic function `F` on `X(ℂ)` with `F ∘ exp = f`: `F` exists
as a function because `exp` is onto with fibres `v + Λ` (S12), is unique by surjectivity, and is
holomorphic by `spec_contMDiff_iff_contDiff_comp_complexExponential`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §2.1 (holomorphic
functions on `ℂ^g / Λ` are the `Λ`-periodic holomorphic functions on `ℂ^g`); through
`spec_contMDiff_iff_contDiff_comp_complexExponential` and S12's `surjective_complexExponential`. -/
theorem spec_existsUnique_contMDiff_descent (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    [IsIntegral X.left] [IsProjective X.hom] (f : (Fin d → ℂ) → ℂ) (hf : ContDiff ℂ ω f)
    (hper : ∀ l ∈ complexExponentialLattice X d, ∀ v, f (v + l) = f v) :
    ∃! F : ComplexPoint X → ℂ, ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω F ∧
      ∀ v, F (complexExponential X d v).toMul = f v :=
  spec_existsUnique_contMDiff_descent_aux X d f hf hper

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (f : (Fin d → ℂ) → ℂ) (hf : ContDiff ℂ ω f)
    (hper : ∀ l ∈ complexExponentialLattice X d, ∀ v, f (v + l) = f v)
    (F G : ComplexPoint X → ℂ)
    (hF : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω F ∧ ∀ v, F (complexExponential X d v).toMul = f v)
    (hG : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω G ∧ ∀ v, G (complexExponential X d v).toMul = f v) :
    F = G :=
  (spec_existsUnique_contMDiff_descent X d f hf hper).unique hF hG

/-- Falsification check for the covering and descent statements: discreteness of the subgroup is
needed. The quotient of `ℂ` by the dense subgroup `ℚ` is not Hausdorff, since a quotient of a
topological group is Hausdorff only if the subgroup is closed, and `ℚ` is not closed in `ℂ`. So
no statement of this file holds for an arbitrary subgroup in place of `Λ`.

Source: Bourbaki, *General Topology*, Ch. III §2.6, Proposition 18 (`G ⧸ H` is Hausdorff if and
only if `H` is closed); Mathlib's `QuotientAddGroup` topology. -/
theorem spec_rat_quotient_not_t2Space :
    ¬ T2Space (ℂ ⧸ (Rat.castHom ℂ).toAddMonoidHom.range) :=
  spec_rat_quotient_not_t2Space_aux

example : ¬ ∀ S : AddSubgroup ℂ, T2Space (ℂ ⧸ S) := fun h ↦
  spec_rat_quotient_not_t2Space (h _)

/-- Falsification check for the compactness input of the covering and descent statements: a
discrete subgroup that is not a full lattice, here `ℤ ⊆ ℂ`, gives a noncompact quotient
(`ℂ ⧸ ℤ ≅ (ℝ ⧸ ℤ) × ℝ`). So `exp` of a group whose kernel were not full could not be onto the
compact `X(ℂ)`; S12's surjectivity and compactness (`compact_complexExponentialQuotient`) are what
make `Λ` full, and they are used.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`ℂ^g / Λ` is compact if and
only if `Λ` has rank `2g`); Mathlib's `QuotientAddGroup` topology. -/
theorem spec_int_quotient_discrete_not_compact :
    DiscreteTopology (Int.castAddHom ℂ).range ∧ ¬ CompactSpace (ℂ ⧸ (Int.castAddHom ℂ).range) :=
  spec_int_quotient_discrete_not_compact_aux

example : ¬ ∀ S : AddSubgroup ℂ, DiscreteTopology S → CompactSpace (ℂ ⧸ S) := fun h ↦
  spec_int_quotient_discrete_not_compact.2 (h _ spec_int_quotient_discrete_not_compact.1)

/-- For a smooth commutative, integral, projective group scheme, holomorphy of maps out of `X(ℂ)`
into any complex manifold is tested on `ℂ^d`: for a model `I'` and a space `Y` charted on it,
`F : X(ℂ) → Y` is holomorphic if and only if `F ∘ exp` is. Forward, compose with the holomorphic
`exp` (stage 4e); backward, every point of `X(ℂ)` is some `exp v` (S12), and on the open target of
the local biholomorphism `e` at `v`, `F = (F ∘ exp) ∘ e.symm`. No `IsManifold I' ω Y` is needed:
both directions only compose `ContMDiff` maps and restrict to open sets. This generalizes
`spec_contMDiff_iff_contDiff_comp_complexExponential`, which is the case `Y = ℂ` (see the
`example`).

Source: Mumford, *Abelian Varieties*, §1; Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed.,
§1.1 (`ℂ^g → ℂ^g / Λ` is a local biholomorphism, so holomorphy is local on `ℂ^g`); through
`spec_complexExponential_localBiholomorph`, stage 4e's `spec_contMDiff_complexExponential` and S12's
`surjective_complexExponential`. -/
theorem spec_contMDiff_iff_contMDiff_comp_complexExponential (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    [IsIntegral X.left] [IsProjective X.hom]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {H' : Type*} [TopologicalSpace H']
    (I' : ModelWithCorners ℂ E' H') {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y]
    (F : ComplexPoint X → Y) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) I' ω F ↔
      ContMDiff 𝓘(ℂ, Fin d → ℂ) I' ω (fun v ↦ F (complexExponential X d v).toMul) :=
  spec_contMDiff_iff_contMDiff_comp_complexExponential_aux X d I' F

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (F : ComplexPoint X → ℂ) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω F ↔
      ContDiff ℂ ω (fun v ↦ F (complexExponential X d v).toMul) :=
  (spec_contMDiff_iff_contMDiff_comp_complexExponential X d 𝓘(ℂ, ℂ) F).trans
    contMDiff_iff_contDiff

/-- For a smooth commutative, integral, projective group scheme, a `Λ`-periodic holomorphic map
`f : ℂ^d → Y` into any complex manifold descends to a unique holomorphic `F : X(ℂ) → Y` with
`F ∘ exp = f`: `F` exists as a map because `exp` is onto with fibres `v + Λ` (S12), is unique by
surjectivity, and is holomorphic by
`spec_contMDiff_iff_contMDiff_comp_complexExponential`. This is the analytic universal property of
`X(ℂ)` as the quotient `ℂ^d ⧸ Λ`; `spec_existsUnique_contMDiff_descent` is the case `Y = ℂ` (see
the `example`), where it has little content, since such scalar functions are constant.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`ℂ^g / Λ` is the quotient
complex manifold, so holomorphic maps out of it are the `Λ`-invariant holomorphic maps out of
`ℂ^g`); through `spec_contMDiff_iff_contMDiff_comp_complexExponential` and S12's
`surjective_complexExponential`. -/
theorem spec_existsUnique_contMDiff_descent_manifold (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    [IsIntegral X.left] [IsProjective X.hom]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {H' : Type*} [TopologicalSpace H']
    (I' : ModelWithCorners ℂ E' H') {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y]
    (f : (Fin d → ℂ) → Y) (hf : ContMDiff 𝓘(ℂ, Fin d → ℂ) I' ω f)
    (hper : ∀ l ∈ complexExponentialLattice X d, ∀ v, f (v + l) = f v) :
    ∃! F : ComplexPoint X → Y, ContMDiff 𝓘(ℂ, Fin d → ℂ) I' ω F ∧
      ∀ v, F (complexExponential X d v).toMul = f v :=
  spec_existsUnique_contMDiff_descent_manifold_aux X d I' f hf hper

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    [IsIntegral X.left] [IsProjective X.hom] (f : (Fin d → ℂ) → ℂ) (hf : ContDiff ℂ ω f)
    (hper : ∀ l ∈ complexExponentialLattice X d, ∀ v, f (v + l) = f v) :
    ∃! F : ComplexPoint X → ℂ, ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω F ∧
      ∀ v, F (complexExponential X d v).toMul = f v :=
  spec_existsUnique_contMDiff_descent_manifold X d 𝓘(ℂ, ℂ) f (contMDiff_iff_contDiff.mpr hf) hper

end HodgeLean.Adapters

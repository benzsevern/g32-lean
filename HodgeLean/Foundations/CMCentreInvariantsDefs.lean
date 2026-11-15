import HodgeLean.Foundations.MultiBlockInvariantsDefs

/-! # The centre of `G_k`: weighted monomials, stage A4 (FROZEN DEFINITIONS)

Definitions for `CMCentreInvariants`, stage A4 of the Powers flagship (PW v0.3, Theorem 4.2,
doi:10.5281/zenodo.23570103; plan `docs/roadmap/pw-flagship-plan.md`, §4.2 row A4, step T4 and
Lemma 4.1(b), (c)). They refine A3b's generator products by recording how many determinant
factors each block carries:

* `CountedGeneratorProduct k α β g`: `g ∈ ⋀^k Space` is a `∧`-product of generators `θ(a, a')`,
  `det(W ⊗ a)`, `det(W^∨ ⊗ a')` with exactly `α` factors `det(W ⊗ a)` and `β` factors
  `det(W^∨ ⊗ a')` (one block; the paper's `α`, `β` of Lemma 4.1(b));
* `MultiCountedProduct k α β x`: `x ∈ ⋀^k (Π_v Space_v)` is a `∧`-product of images `⋀(ι_v) g` of
  such products, block `v` contributing `α v` and `β v` determinant factors (the paper's
  monomials `P`, with `c_v = α_v - β_v`);
* `constWeightDegree k`: the span of the `MultiCountedProduct`s whose weight `α v - β v` is the
  same integer `c` for every block `v`;
* `blockTheta v a a'`, `multiDetW x`, `multiDetWDual x'`: in the exterior algebra of `Π_v Space_v`,
  the contraction `Θ_v(a, a')` of block `v`, and the ordered products `∏_v det(W^v ⊗ x_v)` and
  `∏_v det((W^v)^∨ ⊗ x'_v)` over the blocks `v : Fin e`;
* `centreNormalProducts`: the products of contractions `Θ_v` times `c` factors `multiDetW`, or
  times `c` factors `multiDetWDual`, for `c : ℕ` (the paper's normal form in the "Centre" step).

These are constructions only: no definition asserts an eigenvalue, an invariance or a span
identity. HC no distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance] HodgeLean.Foundations.SchurWeyl.dualAddCommGroup
open scoped TensorProduct
namespace HodgeLean.Foundations
open InvariantsExterior SchurWeyl Module

variable {K : Type*} [Field K]

section OneBlock

variable {W U U' : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U] [AddCommGroup U'] [Module K U']

/-- `∧`-products of the F-1575 (1) generators that carry exactly `α` factors `det(W ⊗ a)` and
`β` factors `det(W^∨ ⊗ a')`; contractions `θ(a, a')` are not counted.
Source: PW v0.3, Lemma 4.1(b) ("a product with `α` factors `det(W ⊗ x)` and `β` factors
`det(W^∨ ⊗ x')`"); the generators are those of `InvariantsExterior.GeneratorProduct`. -/
inductive CountedGeneratorProduct : (k : ℕ) → ℕ → ℕ → ⋀[K]^k (Space K W U U') → Prop
  | unit : CountedGeneratorProduct 0 0 0 (exteriorPower.ιMulti K 0 Fin.elim0)
  | theta (a : U) (a' : U') : CountedGeneratorProduct 2 0 0 (theta a a')
  | detW (a : U) : CountedGeneratorProduct (finrank K W) 1 0 (detW a)
  | detWDual (a' : U') : CountedGeneratorProduct (finrank K W) 0 1 (detWDual a')
  | wedge {k l α β γ δ : ℕ} {v : ⋀[K]^k (Space K W U U')} {w : ⋀[K]^l (Space K W U U')} :
      CountedGeneratorProduct k α β v → CountedGeneratorProduct l γ δ w →
      CountedGeneratorProduct (k + l) (α + γ) (β + δ)
        (exteriorPower.wedge K (Space K W U U') k l v w)

example (a : U) (a' : U') :
    CountedGeneratorProduct (2 + finrank K W) 1 0
      (exteriorPower.wedge K (Space K W U U') 2 (finrank K W) (theta a a') (detW a)) :=
  CountedGeneratorProduct.wedge (CountedGeneratorProduct.theta a a')
    (CountedGeneratorProduct.detW a)

end OneBlock

section Blocks

variable {ι : Type*} {W U U' : ι → Type*}
  [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)]
  [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
  [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)]
  [DecidableEq ι] [∀ v, FiniteDimensional K (W v)]

/-- `∧`-products, in any order, of images `⋀(ι_v) g` of per-block counted products; block `v`
contributes `α v` factors `det(W_v ⊗ a)` and `β v` factors `det(W_v^∨ ⊗ a')`. Forgetting the
counts gives A3b's `MultiGeneratorProduct`.
Source: PW v0.3, proof of Theorem 4.2, "Derived group" step (the tensor products `P` over `v` of
monomials, with `c_v = α_v - β_v` computed as in Lemma 4.1(b) for the block `v`). -/
inductive MultiCountedProduct : (k : ℕ) → (ι → ℕ) → (ι → ℕ) → ⋀[K]^k (MultiSpace K W U U') → Prop
  | unit : MultiCountedProduct 0 0 0 (exteriorPower.ιMulti K 0 Fin.elim0)
  | block (v : ι) {k α β : ℕ} {g : ⋀[K]^k (Space K (W v) (U v) (U' v))} :
      CountedGeneratorProduct k α β g →
      MultiCountedProduct k (Pi.single v α) (Pi.single v β)
        (exteriorPower.map k (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v) g)
  | wedge {k l : ℕ} {α β γ δ : ι → ℕ} {x : ⋀[K]^k (MultiSpace K W U U')}
      {y : ⋀[K]^l (MultiSpace K W U U')} :
      MultiCountedProduct k α β x → MultiCountedProduct l γ δ y →
      MultiCountedProduct (k + l) (α + γ) (β + δ) (exteriorPower.wedge K _ k l x y)

example (v : ι) (a : U v) (a' : U' v) :
    MultiCountedProduct (K := K) (W := W) (U := U) (U' := U') 2
      (Pi.single v 0) (Pi.single v 0)
      (exteriorPower.map 2 (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
        (theta a a')) :=
  MultiCountedProduct.block v (CountedGeneratorProduct.theta a a')

/-- The degree-`k` span of the counted products whose weight `c_v = α_v - β_v` is one integer
`c` for all blocks `v`.
Source: PW v0.3, proof of Theorem 4.2, "Centre" step ("the `G_k(A)_ℂ`-invariants are spanned by
those `P` with constant `c_v = c`"). -/
def constWeightDegree (k : ℕ) : Submodule K (⋀[K]^k (MultiSpace K W U U')) :=
  Submodule.span K
    {x | ∃ (c : ℤ) (α β : ι → ℕ), (∀ v, (α v : ℤ) - β v = c) ∧ MultiCountedProduct k α β x}

example (v : ι) (a : U v) (a' : U' v) :
    exteriorPower.map 2 (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
        (theta a a') ∈ constWeightDegree (K := K) (W := W) (U := U) (U' := U') 2 :=
  Submodule.subset_span ⟨0, Pi.single v 0, Pi.single v 0, fun _ => by simp,
    MultiCountedProduct.block v (CountedGeneratorProduct.theta a a')⟩

/-- The contraction `Θ_v(a, a')` of block `v`, included in the exterior algebra of `Π_v Space_v`.
Source: PW v0.3, proof of Theorem 4.2, "Derived group" step (the contractions `Θ_v`); the
one-block contraction is `InvariantsExterior.theta`. -/
def blockTheta (v : ι) (a : U v) (a' : U' v) : ExteriorAlgebra K (MultiSpace K W U U') :=
  ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
    ((theta (K := K) (W := W v) a a' : ExteriorAlgebra K (Space K (W v) (U v) (U' v))))

example (v : ι) (a : U v) (a' : U' v) :
    blockTheta (K := K) (W := W) v a a' =
      ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
        ((theta (K := K) (W := W v) a a' : ExteriorAlgebra K (Space K (W v) (U v) (U' v)))) :=
  rfl

end Blocks

section FinBlocks

variable {e : ℕ} {W U U' : Fin e → Type*}
  [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
  [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
  [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)]

/-- The ordered product `∏_{v=0}^{e-1} det(W_v ⊗ x_v)` in the exterior algebra of `Π_v Space_v`,
block `v` entering through `ι_v = LinearMap.single`.
Source: PW v0.3, proof of Theorem 4.2, "Centre" step (the tensors `⊗_v det(W^v ⊗ x_v)`; in the
exterior algebra the tensor product over the blocks is the product, up to the order of factors). -/
def multiDetW (x : (v : Fin e) → U v) : ExteriorAlgebra K (MultiSpace K W U U') :=
  (List.ofFn fun v => ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
    ((detW (K := K) (W := W v) (U' := U' v) (x v) :
      ExteriorAlgebra K (Space K (W v) (U v) (U' v))))).prod

/-- The ordered product `∏_{v=0}^{e-1} det(W_v^∨ ⊗ x'_v)` in the exterior algebra of
`Π_v Space_v`.
Source: PW v0.3, proof of Theorem 4.2, "Centre" step (the dual tensors
`⊗_v det((W^v)^∨ ⊗ x'_v)`, used when `c < 0`). -/
def multiDetWDual (x' : (v : Fin e) → U' v) : ExteriorAlgebra K (MultiSpace K W U U') :=
  (List.ofFn fun v => ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
    ((detWDual (K := K) (W := W v) (U := U v) (x' v) :
      ExteriorAlgebra K (Space K (W v) (U v) (U' v))))).prod

example {W U U' : Fin 0 → Type*}
    [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
    [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
    [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)] (x : (v : Fin 0) → U v) :
    multiDetW (K := K) (W := W) (U' := U') x = 1 :=
  rfl

/-- The paper's normal form: a product of contractions `Θ_v(a, a')`, over a list of blocks and
arguments, times `c` factors `multiDetW (x j)`, or times `c` factors `multiDetWDual (x' j)`,
`c : ℕ`.
Source: PW v0.3, proof of Theorem 4.2, "Centre" step ("a polynomial in the contractions times a
product of `c` tensors `⊗_v det(W^v ⊗ x_v)`; if `c < 0`, the same holds with
`det((W^v)^∨ ⊗ x'_v)`"). -/
def centreNormalProducts : Set (ExteriorAlgebra K (MultiSpace K W U U')) :=
  {y | ∃ (l : List ((v : Fin e) × U v × U' v)) (c : ℕ) (x : Fin c → (v : Fin e) → U v),
      y = (l.map fun p => blockTheta (K := K) (W := W) p.1 p.2.1 p.2.2).prod *
        (List.ofFn fun j => multiDetW (K := K) (W := W) (U' := U') (x j)).prod} ∪
  {y | ∃ (l : List ((v : Fin e) × U v × U' v)) (c : ℕ) (x' : Fin c → (v : Fin e) → U' v),
      y = (l.map fun p => blockTheta (K := K) (W := W) p.1 p.2.1 p.2.2).prod *
        (List.ofFn fun j => multiDetWDual (K := K) (W := W) (U := U) (x' j)).prod}

example (x : (v : Fin e) → U v) :
    multiDetW (K := K) (W := W) (U' := U') x ∈
      centreNormalProducts (K := K) (W := W) (U := U) (U' := U') :=
  Or.inl ⟨[], 1, fun _ => x, by simp⟩

example (x' : (v : Fin e) → U' v) :
    multiDetWDual (K := K) (W := W) (U := U) x' ∈
      centreNormalProducts (K := K) (W := W) (U := U) (U' := U') :=
  Or.inr ⟨[], 1, fun _ => x', by simp⟩

end FinBlocks

end HodgeLean.Foundations

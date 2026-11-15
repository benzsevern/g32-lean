module

public import Mathlib

/-! # Degree and quasi-compact pushforward of algebraic cycles, Mathlib-only definitions

The degree of a point is the degree of the residue-field extension, which at the generic point of
`Z = closure {z}` is `[K(Z) : K(f(Z))]`, with the value `0` when that extension is infinite. The
quasi-compact cycle pushforward extending Fulton's proper pushforward is the linear extension
`[z] ↦ deg • [f z]`, on Mathlib's cycle carrier `AlgebraicCycle X R` (locally finitely supported
functions on the points of `X`). The statements about them are in
`HodgeLean.Adapters.CyclePushforward`. HC no distance; AV milestone no distance.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Adapters

universe u

/-- The degree of `f` at a point `x`: the dimension of `κ(x)` over `κ(f x)` along
`Scheme.Hom.residueFieldMap`, as a natural number (`Module.finrank`, so `0` when infinite).
At the generic point of `Z = closure {x}` this is `[K(Z) : K(f(Z))]`.
Source: Fulton, *Intersection Theory*, second edition, §1.4, definition of `deg(V/W)`;
Stacks Project, Tag 02R4. -/
def a1p_degree {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : ℕ :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  Module.finrank (Y.residueField (f x)) (X.residueField x)

example {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : a1p_degree f x = f.residueDegree x := rfl

/-- The quasi-compact cycle pushforward extending Fulton's proper pushforward: the coefficient at
`y` is `∑ x ∈ f⁻¹{y}, c x * a1p_degree f x`. Quasi-compactness makes every fibre meet the locally
finite support in a finite set.
Source: Fulton, *Intersection Theory*, second edition, §1.4, `f_*[V] = deg(V/f(V)) [f(V)]`;
Stacks Project, Tag 02R4. -/
def a1p_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] {R : Type*} [Semiring R]
    (c : AlgebraicCycle X R) : AlgebraicCycle Y R :=
  Function.locallyFinsupp.map f (fun x => (a1p_degree f x : R)) f.isSpectralMap c

example {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (c : AlgebraicCycle X ℤ) (y : Y) :
    a1p_pushforward f c y = ∑ᶠ x ∈ f ⁻¹' {y}, c x * (a1p_degree f x : ℤ) := rfl

end HodgeLean.Adapters

/-
Ported from https://github.com/resolutionorg/hironaka
at commit 044d89c9455859446fc5e986667319f910e15f4b.
Licensed under Apache-2.0; see LICENSE.
-/
/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HodgeLean.Ported.Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Admissible
public import HodgeLean.Ported.Hironaka.Scheme.BlowUp.CoordinateSubspace.Charts
public import HodgeLean.Ported.Hironaka.Algebra.RegularSmooth.SmoothAt
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étale coordinates adapted to a center: the definitions

`X` is a scheme over a field `k` (`f : X ⟶ Spec k`), `𝔸ⁿ_k = Spec k[t_0, …, t_{n-1}]` (that is,
`Spec (MvPolynomial (Fin n) k)`), `Z` an ideal sheaf on `X`.

* `toAffineSpace f U v : U ⟶ 𝔸ⁿ_k`, for `n` sections `v` of an open `U ⊆ X`, is the morphism over
  `k` whose coordinate functions are the `v i`: `U ⟶ Spec Γ(X, U)` followed by `Spec` of the
  `k`-algebra map `k[t] → Γ(X, U)`, `t_i ↦ v i` (`MvPolynomial.aeval v`; the `k`-algebra structure
  on `Γ(X, U)` is `Scheme.Hom.sectionsAlgebra f U`, through `f`). Kollár's "local coordinates
  `(x_1, …, x_n)`" read as a morphism to affine space ([Kol07, Definition 24] and
  [Kol07, Definition 60]; [Sta, Tag 054L]). Mathlib's `AffineSpace.homOfVector` is not used:
  `𝔸(Fin n; S)` forces the index type and the scheme into one universe.
* `coordinateSubspace k n r ⊆ 𝔸ⁿ_k` is the ideal sheaf of `L = V(t_0, …, t_{r-1})`, the coordinate
  subspace of codimension `r`: `specIdealSheaf` of the ideal `centerIdeal k n r` of the center of
  the model blow-up `modelBlowUp k n r`.
* `EtaleCoordinatesAdapted f n r Z x`: an affine open `U ∋ x`, sections `v` with
  `toAffineSpace f U v` étale, and `Z ∩ U = g⁻¹(L)` as closed subschemes of `U`
  (`Z.comap U.ι = L.comap g`). This is [Kol07, Definition 24, (4)]: local coordinates `z_1, …, z_n`
  at `x` with "`Z = (z_{j_1} = ⋯ = z_{j_s} = 0)`" near `x`, here with the coordinates made an
  étale chart: the form in which the blow-up of `Z` is computed locally
  (`B_{Z∩U} U ≅ U ×_{𝔸ⁿ} B_L 𝔸ⁿ`, `Hironaka/Scheme/Smooth/BlowUpSmoothChart.lean`).
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The morphism `U ⟶ 𝔸ⁿ_k = Spec k[t_0, …, t_{n-1}]` over `k` with coordinate functions
`v 0, …, v (n-1) ∈ Γ(X, U)` (Kollár's local coordinates as a morphism to affine space). -/
noncomputable def toAffineSpace (f : X ⟶ Spec (.of k)) {n : ℕ} (U : X.Opens)
    (v : Fin n → Γ(X, U)) : (U : Scheme.{u}) ⟶ Spec (.of (MvPolynomial (Fin n) k)) :=
  letI := f.sectionsAlgebra U
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom)

/-- The coordinate subspace `L = V(t_0, …, t_{r-1}) ⊆ 𝔸ⁿ_k` as an ideal sheaf on
`Spec k[t_0, …, t_{n-1}]`: the ideal sheaf of `centerIdeal k n r = (t_0, …, t_{r-1})`, the center
of the model blow-up `modelBlowUp k n r`. -/
noncomputable abbrev coordinateSubspace (k : Type u) [Field k] (n r : ℕ) :
    (Spec (.of (MvPolynomial (Fin n) k))).IdealSheafData :=
  specIdealSheaf (CoordinateSubspace.centerIdeal k n r)

/-- **Étale coordinates at `x` adapted to `Z`** ([Kol07, Definition 24, (4)];
[Kol07, Definition 60]): an affine open `U ∋ x` and sections `v_0, …, v_{n-1}` of `U` such that the
coordinate morphism `g = toAffineSpace f U v : U ⟶ 𝔸ⁿ_k` is étale and `Z ∩ U = g⁻¹(L)`,
`L = V(t_0, …, t_{r-1})`, as closed subschemes of `U`. -/
structure EtaleCoordinatesAdapted (f : X ⟶ Spec (.of k)) (n r : ℕ) (Z : X.IdealSheafData)
    (x : X) where
  /-- The affine chart around `x`. -/
  U : X.affineOpens
  /-- `x` lies in the chart. -/
  mem : x ∈ U.1
  /-- The coordinate functions. -/
  v : Fin n → Γ(X, U.1)
  /-- The coordinate morphism `U ⟶ 𝔸ⁿ_k` is étale. -/
  etale : Etale (toAffineSpace f U.1 v)
  /-- Adaptedness: `Z ∩ U` is the pullback of the coordinate subspace `V(t_0, …, t_{r-1})`. -/
  adapted : Z.comap U.1.ι = (coordinateSubspace k n r).comap (toAffineSpace f U.1 v)

end AlgebraicGeometry

-- Audit generated public interfaces as well as explicit declarations.
set_option linter.auxLemma false

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.U

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.adapted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.adapted

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.casesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.casesOn

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.ctorIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.ctorIdx

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.etale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.etale

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.mem

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.mk

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.mk.inj

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.mk.injEq

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.mk.noConfusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.mk.noConfusion

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.mk.sizeOf_spec

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.noConfusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.noConfusion

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.noConfusionType' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.noConfusionType

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.rec

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.recOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.recOn

/-- info: 'AlgebraicGeometry.EtaleCoordinatesAdapted.v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EtaleCoordinatesAdapted.v

/-- info: 'AlgebraicGeometry.coordinateSubspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.coordinateSubspace

/-- info: 'AlgebraicGeometry.toAffineSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.toAffineSpace

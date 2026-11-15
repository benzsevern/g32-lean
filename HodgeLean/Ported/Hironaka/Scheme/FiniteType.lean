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

public import HodgeLean.Ported.Hironaka.Scheme.Defs

/-!
# Morphisms of finite type

A morphism of schemes is of finite type (`AlgebraicGeometry.FiniteType`) if it is locally of finite
type and quasi-compact [Sta, Tag 01T0]. The class is bundled like Mathlib's `IsProper`: its parents
are instances, and conversely `FiniteType f` is inferred from the two parts (the instance
`FiniteType.of_locallyOfFiniteType_of_quasiCompact`), so that statements may carry the bundled class
while the lemmas feeding them keep the two unbundled ones. `finiteType_iff` unbundles it.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

attribute [mk_iff] FiniteType

/-- A morphism that is locally of finite type and quasi-compact is of finite type. -/
instance FiniteType.of_locallyOfFiniteType_of_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] : FiniteType f where

end AlgebraicGeometry

-- Audit generated public interfaces as well as explicit declarations.
set_option linter.auxLemma false

/-- info: 'AlgebraicGeometry.FiniteType.of_locallyOfFiniteType_of_quasiCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.FiniteType.of_locallyOfFiniteType_of_quasiCompact

/-- info: 'AlgebraicGeometry.finiteType_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.finiteType_iff

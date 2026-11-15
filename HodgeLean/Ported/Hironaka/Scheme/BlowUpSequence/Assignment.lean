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

public import HodgeLean.Ported.Hironaka.Scheme.BlowUpSequence.Defs

/-!
# Assignments of successions of blow-ups

The data of the functors that the proofs of Kollár's Theorem 36 and of Włodarczyk's Theorem 1.0.2
construct (`Hironaka.Resolution.BRFunctor`, `Hironaka.Resolution.EDFunctor`): a succession of
blow-ups for every input, with no conditions. The
statements of the theorems use `AlgebraicGeometry.BlowUpSequenceFunctor`
(`HodgeLean.Ported.Hironaka.Scheme.Resolution.Defs`); these unbundled forms are the ones the constructions are
written in. -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

/-- A resolution functor on all algebraic `k`-schemes [Kol07, Theorem 36]: an assignment of a
succession of monoidal transformations `BR(X)` to every scheme of finite type over `Spec k`
(separated, as every scheme of this library). The resolution functor
`Hironaka.Resolution.BRFunctor` is one; the statement of the theorem uses
`AlgebraicGeometry.BlowUpSequenceFunctor`. -/
structure ResolutionAssignment (k : Type u) [Field k] where
  /-- The succession `BR(X)`. -/
  seq : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] [FiniteType (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))],
    BlowUpSequence X

/-- An embedded desingularization assignment [Wlo05, Theorem 1.0.2]: a succession of monoidal
transformations of the smooth ambient `X` for every closed subscheme `Y ⊆ X` (given by its ideal
sheaf). The embedded desingularization functor `Hironaka.Resolution.EDFunctor` is one; the
statement of the theorem, `AlgebraicGeometry.exists_functorial_embeddedDesingularization`, uses
`AlgebraicGeometry.BlowUpSequenceFunctor` on embedded pairs. -/
structure EmbeddedDesingularizationAssignment (k : Type u) [Field k] where
  /-- The succession assigned to `Y ⊆ X`. -/
  seq : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] [FiniteType (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [Smooth (X ↘ Spec (.of k))],
    X.IdealSheafData → BlowUpSequence X

end AlgebraicGeometry

-- Audit generated public interfaces as well as explicit declarations.
set_option linter.auxLemma false

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment.casesOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment.casesOn

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment.ctorIdx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment.ctorIdx

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment.mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment.mk

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment.mk.inj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment.mk.inj

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment.mk.injEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment.mk.injEq

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment.mk.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment.mk.noConfusion

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment.mk.sizeOf_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment.mk.sizeOf_spec

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment.noConfusion

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment.noConfusionType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment.noConfusionType

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment.rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment.rec

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment.recOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment.recOn

/-- info: 'AlgebraicGeometry.EmbeddedDesingularizationAssignment.seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.EmbeddedDesingularizationAssignment.seq

/-- info: 'AlgebraicGeometry.ResolutionAssignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment

/-- info: 'AlgebraicGeometry.ResolutionAssignment.casesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment.casesOn

/-- info: 'AlgebraicGeometry.ResolutionAssignment.ctorIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment.ctorIdx

/-- info: 'AlgebraicGeometry.ResolutionAssignment.mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment.mk

/-- info: 'AlgebraicGeometry.ResolutionAssignment.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment.mk.inj

/-- info: 'AlgebraicGeometry.ResolutionAssignment.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment.mk.injEq

/-- info: 'AlgebraicGeometry.ResolutionAssignment.mk.noConfusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment.mk.noConfusion

/-- info: 'AlgebraicGeometry.ResolutionAssignment.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment.mk.sizeOf_spec

/-- info: 'AlgebraicGeometry.ResolutionAssignment.noConfusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment.noConfusion

/-- info: 'AlgebraicGeometry.ResolutionAssignment.noConfusionType' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment.noConfusionType

/-- info: 'AlgebraicGeometry.ResolutionAssignment.rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment.rec

/-- info: 'AlgebraicGeometry.ResolutionAssignment.recOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment.recOn

/-- info: 'AlgebraicGeometry.ResolutionAssignment.seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.ResolutionAssignment.seq

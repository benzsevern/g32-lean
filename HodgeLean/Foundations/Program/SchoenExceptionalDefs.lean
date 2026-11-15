module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology
public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.Constant
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueAcyclic
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.InjectiveFlasque
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic

/-! # Explicit topological fibre models for the S3 specification

These are spaces and maps, without an identification with Schoen's resolution.
HC no distance; AV milestone no distance.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped OnePoint

namespace HodgeLean.Foundations.Program

/-- A disjoint union of `d` Riemann spheres when `d > 0`.
Source: G32 v0.16, Lemma 4.3; normalization of the local binomial cover of a
projective line branched at two points has `gcd(m,a)` rational components. -/
abbrev s3_Fibre (d : ℕ) := ZMod d × OnePoint ℂ

example : s3_Fibre 1 := (0, ∞)

/-- Cyclic permutation of components, followed by the same nonzero complex dilation
on each sphere. This is an explicit model map, not an action extracted from a resolution.
Source: G32 v0.16, Lemma 4.3, two-point fibre; the topological rotation model. -/
def s3_deck (d : ℕ) (c : ℂ) (hc : c ≠ 0) : s3_Fibre d ≃ₜ s3_Fibre d :=
  (Homeomorph.ofDiscrete (Equiv.addRight (1 : ZMod d))).prodCongr
    (Homeomorph.onePointCongr (Homeomorph.mulLeft₀ c hc))

example (d : ℕ) (c : ℂ) (hc : c ≠ 0) (i : ZMod d) (z : ℂ) :
    s3_deck d c hc (i, (z : OnePoint ℂ)) = (i + 1, ((c * z : ℂ) : OnePoint ℂ)) := rfl

/-- Inclusion of a point fibre with its subspace topology.
Source: Schapira, An Introduction to Categories and Sheaves, version 2023-10-01,
Theorem 11.3.6 (the fibre inclusion in proper base change). -/
def s3_fibreInclusion {X Y : TopCat} (p : X ⟶ Y) (y : Y) :
    TopCat.of {x : X // p x = y} ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

example {X Y : TopCat} (p : X ⟶ Y) (y : Y) (x : {x : X // p x = y}) :
    p (s3_fibreInclusion p y x) = y := x.property

-- Two independent checks, using only the definitions and ring arithmetic.
example : (6 : ZMod 12) ≠ 0 := by decide

example (z : ℂ) : (-1 - 1) * ((-1 / 2) * z) = z := by ring

example (i : ZMod 6) : s3_deck 6 (-1) (by norm_num) (i, ∞) = (i + 1, ∞) := rfl

end HodgeLean.Foundations.Program

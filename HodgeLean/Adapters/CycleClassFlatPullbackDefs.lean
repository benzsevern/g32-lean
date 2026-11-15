import HodgeLean.Adapters.CycleClassPullbackDefs
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.Length

/-! # Scheme-theoretic inverse images and their cycle coefficients

These are actual finite-sum constructions. The finite-type properties and coefficient
identities are stated separately. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint

namespace HodgeLean.Adapters

/-- The reduced closed subscheme with generic point `x`.
Source: Fulton, *Intersection Theory*, second edition, §1.5 (cycles). -/
def ccm3_primeIdeal (Z : Scheme) (x : Z) : Z.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure ({x} : Set Z), isClosed_closure⟩

/-- The ideal of the scheme-theoretic inverse image, before taking any reduction.
Source: Fulton, *Intersection Theory*, second edition, §1.7 (flat pullback). -/
def ccm3_inverseIdeal {X Z : Scheme} (f : X ⟶ Z) (x : Z) : X.IdealSheafData :=
  (ccm3_primeIdeal Z x).comap f

/-- Generic length of the inverse image at a point. Only component generic points are
used in the cycle; finiteness there is a separate theorem.
Source: Fulton, *Intersection Theory*, second edition, §1.5, definition of `[X]`. -/
def ccm3_genericLength {X Z : Scheme} (f : X ⟶ Z) (x : Z)
    (y : (ccm3_inverseIdeal f x).subscheme) : ℕ∞ :=
  Module.length ((ccm3_inverseIdeal f x).subscheme.presheaf.stalk y)
    ((ccm3_inverseIdeal f x).subscheme.presheaf.stalk y)

/-- The inverse-image cycle: each component contributes its generic length at its
image in the ambient scheme. On finite-type schemes the indexing set is finite and
these lengths are finite; those facts are separate obligations, not input certificates.
Source: Fulton, *Intersection Theory*, second edition, §1.7, definition `f⁎[V] = [f⁻¹(V)]`. -/
def ccm3_flatPullbackPrime {X Z : Scheme} (f : X ⟶ Z) (x : Z) :
    AlgebraicCycle X ℚ := by
  classical
  exact ∑ᶠ y : (ccm3_inverseIdeal f x).subscheme,
    if closure ({y} : Set (ccm3_inverseIdeal f x).subscheme) ∈
        irreducibleComponents (ccm3_inverseIdeal f x).subscheme then
      Function.locallyFinsuppWithin.single ((ccm3_inverseIdeal f x).subschemeι y)
        ((ccm3_genericLength f x y).toNat : ℚ)
    else 0

/-- Extension over all source components with their original rational coefficients.
For finite-type complex schemes every input cycle has finite support.
Source: Fulton, *Intersection Theory*, second edition, §1.7, linear extension of flat pullback. -/
def ccm3_flatPullback {X Z : Scheme} (f : X ⟶ Z) (c : AlgebraicCycle Z ℚ) :
    AlgebraicCycle X ℚ :=
  ∑ᶠ x : Z, (ccm3_flatPullbackPrime f x).mapRange (c x * ·) (mul_zero _)

example (Z : Scheme) (x : Z) : Z.IdealSheafData := ccm3_primeIdeal Z x
example {X Z : Scheme} (f : X ⟶ Z) (x : Z) : X.IdealSheafData := ccm3_inverseIdeal f x
example {X Z : Scheme} (f : X ⟶ Z) (x : Z)
    (y : (ccm3_inverseIdeal f x).subscheme) : ℕ∞ := ccm3_genericLength f x y
example {X Z : Scheme} (f : X ⟶ Z) (x : Z) : AlgebraicCycle X ℚ :=
  ccm3_flatPullbackPrime f x
example {X Z : Scheme} (f : X ⟶ Z) (c : AlgebraicCycle Z ℚ) : AlgebraicCycle X ℚ :=
  ccm3_flatPullback f c

/-- Realize the codimension-`q` part of an actual rational algebraic cycle.
The comparison target below uses this sum on the constructed inverse-image cycle.
Source: Fulton, *Intersection Theory*, second edition, §19.1, linear extension of the cycle class. -/
def ccm3_cycleClass (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (q : ℕ) (c : AlgebraicCycle X.left ℚ) : HodgeLean.RealDefs.HQ X (2 * q) :=
  ∑ᶠ z : {z : X.left // Order.coheight z = q},
    c z.1 • cycleComponentSheafClass X z.1 z.2

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (c : AlgebraicCycle X.left ℚ) : HodgeLean.RealDefs.HQ X (2 * q) :=
  ccm3_cycleClass X q c

end HodgeLean.Adapters

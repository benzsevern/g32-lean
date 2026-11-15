import HodgeLean.Adapters.AbelianCMData
import HodgeLean.Adapters.CycleClassScope

/-! # Algebraic pullback along powers sum maps: definitions -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

/-- A point indexing an integral cycle component of codimension `q`.
Source: Fulton, *Intersection Theory*, §1.5, cycles by codimension. -/
abbrev ccm2_CodimensionPoint (X : Over (Spec ↧ℂ)) (q : ℕ) :=
  {x : X.left // Order.coheight x = q}

/-- Finite rational combinations of codimension-`q` components.
Source: Fulton, *Intersection Theory*, §1.7, cycles with rational coefficients. -/
abbrev ccm2_ComponentCycle (X : Over (Spec ↧ℂ)) (q : ℕ) :=
  ccm2_CodimensionPoint X q →₀ ℚ

/-- The cohomology class of a finite rational component cycle.
Source: Fulton, *Intersection Theory*, §19.1; rational linear extension of component classes. -/
def ccm2_ComponentCycle.class {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] {q : ℕ} (c : ccm2_ComponentCycle X q) : HQ X (2 * q) :=
  c.sum fun x m ↦ m • cycleComponentSheafClass X x.1 x.2

/-- The available pointwise meaning of an isogeny: finite kernel and surjectivity on complex
points. Mathlib has no abelian-scheme isogeny structure at this layer.
Source: Mumford, *Abelian Varieties*, §18, definition of an isogeny. -/
def ccm2_IsogenyOnPoints {X Z : Over (Spec ↧ℂ)} [GrpObj X] [GrpObj Z]
    (f : X ⟶ Z) : Prop :=
  Set.Finite {x : ComplexPoint X | Point.map f x = 1} ∧ Function.Surjective (Point.map f)

end HodgeLean.Adapters

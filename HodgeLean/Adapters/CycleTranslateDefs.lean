import HodgeLean.Adapters.CycleClassDivisorIntersection

/-! # Translation bookkeeping and transverse translation parameters -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Adapters

/-- The generic point of the inverse translate of the component with generic point `y`.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28
(1974), §1; Mathlib `GrpObj.mulRight`. -/
def hc9k_translatePoint (X : Over (Spec ↧ℂ)) [GrpObj X] (t : ComplexPoint X)
    (y : X.left) : X.left :=
  (GrpObj.mulRight t).inv.left y

/-- The translation parameters for which the reduced closures of `x` and the inverse translate
of `y` meet properly, and their scheme-theoretic intersection is smooth wherever both
components are regular.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28
(1974), Theorem 2; Hartshorne, Algebraic Geometry, III.10.8; Fulton,
Intersection Theory, second edition, Example 11.4.5. -/
def hc9k_transverseLocus (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x y : X.left) : Set (ComplexPoint X) :=
  {t | let z := hc9k_translatePoint X t y
    let I := ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left z
    (∀ w : I.subscheme,
      closure ({w} : Set I.subscheme) ∈ irreducibleComponents I.subscheme →
        Order.coheight (I.subschemeι w) = Order.coheight x + Order.coheight y) ∧
    (∀ v : I.subscheme,
      I.subschemeι v ∉ (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) →
      I.subschemeι v ∉ (cycleComponentSingularAmbientClosedFiltration X z 0 : Set X.left) →
        v ∈ (I.subschemeι ≫ X.hom).smoothLocus)}

open HodgeLean.Foundations HodgeLean.Foundations.Curves

/-- Source: the cubic group in `HodgeLean.Foundations.Curves`. -/
example : E.left :=
  hc9k_translatePoint E (Over.homMk finitePoint finitePoint_over : ComplexPoint E) cubicInfinity

/-- Source: Kleiman, Compositio Math. 28 (1974), Theorem 2. -/
example : Set (ComplexPoint E) := hc9k_transverseLocus E cubicInfinity cubicInfinity

end HodgeLean.Adapters

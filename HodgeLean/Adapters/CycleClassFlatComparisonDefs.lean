import HodgeLean.Adapters.CycleClassFlatPullback
import HodgeLean.RealDefs.SupportEnlargement

/-! # Supported pullback constructions for cycle classes

The pullback below is defined in relative singular cohomology and transported back to
supported sheaf cohomology.  It is independent of the ordinary-cohomology map
`homPullback`. HC no distance; AV milestone no distance.
-/

noncomputable section

set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

/-- Rational scalars on supported cohomology transported from relative singular cohomology.
Source: `supportedSingularClass` and Mathlib `AddEquiv.module`. -/
instance ccm4_supportHModule (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    Module ℚ (TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) :=
  (supportedSingularClass X S n).module ℚ

example (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) : (1 : ℚ) • u = u :=
  one_smul ℚ u

/-- The analytic inverse image of a closed support.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §11. -/
def ccm4_inverseAnalyticSupport {X Z : Over (Spec ↧ℂ)} (f : X ⟶ Z)
    (S : Closeds (ComplexPoint Z)) : Closeds (ComplexPoint X) :=
  ⟨Point.continuousMap f ⁻¹' (S : Set (ComplexPoint Z)),
    S.isClosed.preimage (Point.continuousMap f).continuous⟩

/-- The map of relative pairs induced by inverse image of a support.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §11. -/
def ccm4_inverseSupportPairMap {X Z : Over (Spec ↧ℂ)} (f : X ⟶ Z)
    (S : Closeds (ComplexPoint Z)) :
    neighborhoodSupportComplementPair Set.univ
        (ccm4_inverseAnalyticSupport f S : Set (ComplexPoint X)) ⟶
      neighborhoodSupportComplementPair Set.univ (S : Set (ComplexPoint Z)) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun x => ⟨Point.continuousMap f x.1, Set.mem_univ _⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun x =>
      ⟨⟨Point.continuousMap f x.1.1, Set.mem_univ _⟩, x.2⟩, by fun_prop⟩)
    (by ext x; rfl)

/-- Pullback in supported sheaf cohomology, constructed through relative singular
cohomology with the inverse-image support.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §11. -/
def ccm4_supportedPullback {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (S : Closeds (ComplexPoint Z)) (n : ℕ) :
    TopCat.Sheaf.supportH (TopCat.of (ComplexPoint Z)) S
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint Z))).obj
          (AddCommGrpCat.of ℚ)) n →+
      TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X))
        (ccm4_inverseAnalyticSupport f S)
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of ℚ)) n :=
  (supportedSingularClass X (ccm4_inverseAnalyticSupport f S) n).symm.toAddMonoidHom.comp
    ((relativeCohomologyMap ℚ n (ccm4_inverseSupportPairMap f S)).toAddMonoidHom.comp
      (supportedSingularClass Z S n).toAddMonoidHom)

example {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (S : Closeds (ComplexPoint Z)) (n : ℕ) :=
  ccm4_supportedPullback f S n

end HodgeLean.Adapters

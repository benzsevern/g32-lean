import HodgeLean.Foundations.ChowProjective

/-! # Definitions for algebraizing holomorphic maps -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped MonoidalCategory

namespace HodgeLean.Adapters

/-- The product of two complex schemes over `Spec ℂ`.
Source: Mathlib `Over.cartesianMonoidalCategory`; the tensor product in an over-category is the
fibre product over its base. -/
def gagam_product (X Y : Over (Spec ↧ℂ)) : Over (Spec ↧ℂ) := X ⊗ Y

example (X Y : Over (Spec ↧ℂ)) :
    (gagam_product X Y).left = Limits.pullback X.hom Y.hom := rfl

/-- The set-theoretic graph of a map on complex points, inside the complex points of the
fibre product.
Source: Hartshorne, *Algebraic Geometry*, Chapter I, §5 (graphs and products). -/
def gagam_graph (X Y : Over (Spec ↧ℂ)) (F : ComplexPoint X → ComplexPoint Y) :
    Set (ComplexPoint (gagam_product X Y)) :=
  {z | Point.map (CartesianMonoidalCategory.snd X Y) z =
    F (Point.map (CartesianMonoidalCategory.fst X Y) z)}

example (X Y : Over (Spec ↧ℂ)) (F : ComplexPoint X → ComplexPoint Y)
    (z : ComplexPoint (gagam_product X Y)) :
    z ∈ gagam_graph X Y F ↔
      Point.map (CartesianMonoidalCategory.snd X Y) z =
        F (Point.map (CartesianMonoidalCategory.fst X Y) z) :=
  Iff.rfl

end HodgeLean.Adapters

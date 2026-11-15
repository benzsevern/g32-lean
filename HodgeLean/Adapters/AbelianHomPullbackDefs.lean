import HodgeLean.Adapters.AbelianEndomorphismsDefs

/-! # Pullback along morphisms between different varieties: definition (FROZEN)

* `homPullback f n : HQ X n →ₗ[ℚ] HQ Y n`, for `f : Y ⟶ X` between smooth projective integral
  varieties over `ℂ`: pullback along the continuous map `Y(ℂ) → X(ℂ)` of `f`, on singular
  cohomology, carried to `HQ · n` along the S7 comparisons `cupComparison X n` and
  `cupComparison Y n`. For `Y = X` it is `complexPointPullback X f n`, by `rfl`.

The comparisons are the ones `cupProductOf` is transported along, so they send the sheaf unit to
the singular unit; nothing here compares `homPullback` with a pullback of sheaf cohomology, and
nothing here says it is functorial, additive or Hodge-compatible.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

variable {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- Pullback along the map of complex points of `f : Y ⟶ X`, on singular cohomology, carried from
`X(ℂ)` to `HQ X n` and from `Y(ℂ)` to `HQ Y n` along the S7 comparisons.
Source: Hatcher, *Algebraic Topology*, §3.1 (induced maps on cohomology); Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., §1.2 (rational representation of a homomorphism); upstream
`Point.continuousMap` at `2ead713`; S7 `cupComparison`. -/
def homPullback (f : Y ⟶ X) (n : ℕ) : HQ X n →ₗ[ℚ] HQ Y n :=
  (cupComparison Y n).symm.toLinearMap ∘ₗ
    cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap f)) ∘ₗ (cupComparison X n).toLinearMap

example (f : Y ⟶ X) (n : ℕ) (x : HQ X n) :
    cupComparison Y n (homPullback f n x) =
      cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap f)) (cupComparison X n x) := by
  simp [homPullback]

-- For an endomorphism it is the existing endomorphism pullback.
example (f : X ⟶ X) (n : ℕ) : homPullback f n = complexPointPullback X f n := rfl

end HodgeLean.Adapters

import HodgeLean.Adapters.CycleClassScopeProofs

/-! # Cycle-class multiplicativity and pullback: scoped formal cases (FROZEN)

These statements isolate formal consequences of the cycle-class span already available in the
repository. They add no geometric hypothesis structure and make no comparison between the
constructed sheaf classes and an intersection product.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

variable {X Y Z : Over (Spec ↧ℂ)}
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
  [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]

/-- Identity pullback preserves the algebraic cycle-class span.
Source: Hatcher, *Algebraic Topology*, §3.1; functoriality of `homPullback`. -/
theorem ccm1_homPullback_id_span (p : ℕ) :
    (algebraicCycleClassSpan X p).map (homPullback (𝟙 X) (2 * p)) ≤
      algebraicCycleClassSpan X p :=
  ccm1_homPullback_id_span_aux p

example (p : ℕ) :
    (algebraicCycleClassSpan X p).map (homPullback (𝟙 X) (2 * p)) ≤
      algebraicCycleClassSpan X p :=
  ccm1_homPullback_id_span p

/-- Preservation of algebraic spans is stable under composition.
Source: Hatcher, *Algebraic Topology*, §3.1; functoriality of `homPullback`. -/
theorem ccm1_homPullback_comp_span (g : Z ⟶ Y) (f : Y ⟶ X) (p : ℕ)
    (hf : (algebraicCycleClassSpan X p).map (homPullback f (2 * p)) ≤
      algebraicCycleClassSpan Y p)
    (hg : (algebraicCycleClassSpan Y p).map (homPullback g (2 * p)) ≤
      algebraicCycleClassSpan Z p) :
    (algebraicCycleClassSpan X p).map (homPullback (g ≫ f) (2 * p)) ≤
      algebraicCycleClassSpan Z p :=
  ccm1_homPullback_comp_span_aux g f p hf hg

example (p : ℕ) :
    (algebraicCycleClassSpan X p).map (homPullback ((𝟙 X) ≫ (𝟙 X)) (2 * p)) ≤
      algebraicCycleClassSpan X p :=
  ccm1_homPullback_comp_span (𝟙 X) (𝟙 X) p
    (ccm1_homPullback_id_span p) (ccm1_homPullback_id_span p)

/-- Every morphism pulls the degree-zero unit to an algebraic class.
Source: Hatcher, *Algebraic Topology*, §3.1–3.2; the unit is the class of the ambient variety. -/
theorem ccm1_homPullback_unit_mem (f : Y ⟶ X) :
    homPullback f 0 (unitClass X) ∈ algebraicCycleClassSpan Y 0 :=
  ccm1_homPullback_unit_mem_aux f

example : homPullback (𝟙 X) 0 (unitClass X) ∈ algebraicCycleClassSpan X 0 :=
  ccm1_homPullback_unit_mem (𝟙 X)

/-- An algebraic class in codimension above the relative dimension is zero.
Source: the absence of points of coheight above the relative dimension. -/
theorem ccm1_algebraic_class_eq_zero_of_lt (d p : ℕ)
    [SmoothOfRelativeDimension d X.hom] (h : d < p)
    (a : HQ X (2 * p)) (ha : a ∈ algebraicCycleClassSpan X p) : a = 0 :=
  ccm1_algebraic_class_eq_zero_of_lt_aux d p h a ha

section RelativeDimensionZeroExample

private abbrev ccm1Point : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))

private instance : IsIntegral ccm1Point.left := by
  change IsIntegral (Spec ↧ℂ)
  infer_instance

private instance : Smooth ccm1Point.hom := by
  change Smooth (𝟙 (Spec ↧ℂ))
  infer_instance

private instance : IsProjective ccm1Point.hom := by
  change IsProjective (𝟙 (Spec ↧ℂ))
  exact HodgeLean.Foundations.isProjective_specComplex_id

private instance : SmoothOfRelativeDimension 0 ccm1Point.hom := by
  change SmoothOfRelativeDimension 0 (𝟙 (Spec ↧ℂ))
  infer_instance

example (p : ℕ) (hp : 0 < p) (a : HQ ccm1Point (2 * p))
    (ha : a ∈ algebraicCycleClassSpan ccm1Point p) : a = 0 :=
  ccm1_algebraic_class_eq_zero_of_lt 0 p hp a ha

end RelativeDimensionZeroExample

end HodgeLean.Adapters

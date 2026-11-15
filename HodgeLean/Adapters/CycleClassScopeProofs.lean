import HodgeLean.Adapters.AbelianHomPullback
import HodgeLean.RealDefs.AbelianVariety
import Other.AlgebraicGeometry.Cycle.ClassDimension

/-! # Proofs for the cycle-class scope specification -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

variable {X Y Z : Over (Spec ↧ℂ)}
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
  [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]

theorem ccm1_homPullback_id_span_aux (p : ℕ) :
    (algebraicCycleClassSpan X p).map (homPullback (𝟙 X) (2 * p)) ≤
      algebraicCycleClassSpan X p := by
  rintro _ ⟨a, ha, rfl⟩
  rw [spec_homPullback_id, LinearMap.id_apply]
  convert ha using 1

theorem ccm1_homPullback_comp_span_aux (g : Z ⟶ Y) (f : Y ⟶ X) (p : ℕ)
    (hf : (algebraicCycleClassSpan X p).map (homPullback f (2 * p)) ≤
      algebraicCycleClassSpan Y p)
    (hg : (algebraicCycleClassSpan Y p).map (homPullback g (2 * p)) ≤
      algebraicCycleClassSpan Z p) :
    (algebraicCycleClassSpan X p).map (homPullback (g ≫ f) (2 * p)) ≤
      algebraicCycleClassSpan Z p := by
  rintro _ ⟨a, ha, rfl⟩
  rw [spec_homPullback_comp, LinearMap.comp_apply]
  exact hg ⟨homPullback f (2 * p) a, hf ⟨a, ha, rfl⟩, rfl⟩

theorem ccm1_homPullback_unit_mem_aux (f : Y ⟶ X) :
    homPullback f 0 (unitClass X) ∈ algebraicCycleClassSpan Y 0 := by
  rw [show unitClass X = cupUnit X from rfl, spec_homPullback_unit]
  exact unitClass_mem_algebraicCycleClassSpan

theorem ccm1_algebraic_class_eq_zero_of_lt_aux (d p : ℕ)
    [SmoothOfRelativeDimension d X.hom] (h : d < p)
    (a : HQ X (2 * p)) (ha : a ∈ algebraicCycleClassSpan X p) : a = 0 := by
  rw [algebraicCycleClassSpan_eq_bot_of_lt X d p h] at ha
  exact ha

end HodgeLean.Adapters

import HodgeLean.Foundations.Program.SchoenTowerL1aLocalCurveCoordinate
import HodgeLean.Foundations.Program.SchoenFiniteMorphisms
import HodgeConjecture.Mathlib.AlgebraicGeometry.GenericPoint

import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalCoordinates

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every point of the retained smooth curve is generic or comes from an actual complex point. -/
theorem s2v_l1b_divisor_curve_generic_or_complex
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (z : Z.left) :
    z = genericPoint Z.left ∨ ∃ b : ComplexPoint Z, b.underlying = z := by
  letI : SmoothOfRelativeDimension 1 Z.hom := by
    simpa only [hdim] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim Z.left) Z.hom)
  have hdim' : Order.krullDim Z.left = 1 :=
    SmoothOfRelativeDimension.orderKrullDim_eq_complex (f := Z.hom) (d := 1)
  obtain hmin | hmax := Order.krullDim_le_one_iff.mp hdim'.le z
  · right
    have hclosed : IsClosed ({z} : Set Z.left) := by
      apply isClosed_of_closure_subset
      intro y hy
      have hle : y ≤ z := specializes_iff_mem_closure.mpr hy
      exact Set.mem_singleton_iff.mpr (inseparable_iff_eq.mp
        (inseparable_iff_specializes_and.mpr ⟨hmin hle, hle⟩))
    let b : ComplexPoint Z := Over.homMk (pointOfClosedPoint Z.hom z hclosed)
      (pointOfClosedPoint_comp Z.hom z hclosed)
    exact ⟨b, pointOfClosedPoint_apply Z.hom z hclosed _⟩
  · left
    exact eq_genericPoint_of_coheight_zero z (Order.coheight_eq_zero.mpr hmax)

/-- A complex point on a smooth integral curve of dimension one differs from its generic point. -/
theorem s2v_l1b_divisor_curve_complex_ne_generic
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (b : ComplexPoint Z) :
    b.underlying ≠ genericPoint Z.left := by
  letI : SmoothOfRelativeDimension 1 Z.hom := by
    simpa only [hdim] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim Z.left) Z.hom)
  have hc : IsClosed ({b.underlying} : Set Z.left) :=
    ((pointEquivClosedPoint Z.hom) ⟨b.left, by simp⟩).2
  have hb := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
    (f := Z.hom) (d := 1) b.underlying hc
  intro he
  have hg : Order.coheight (genericPoint Z.left) = 0 :=
    Order.coheight_eq_zero.mpr (fun y _ => genericPoint_specializes y)
  rw [he, hg] at hb
  exact zero_ne_one hb

end HodgeLean.Foundations.Program

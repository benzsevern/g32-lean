import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SelectorComponentFamily
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Actual selector and sphere parameter maps produce all projective-line component immersions with their retained sphere coordinates. -/
theorem labelled_projective_sections
    {I : Type} (F C : Over (Spec ↧ℂ))
    [IsProper F.hom] [IsSeparated C.hom]
    (q : F ⟶ C) (r : F ⟶ projectiveLine)
    (b : I → ComplexPoint C) (hb : Function.Injective b)
    (E : ComplexPoint F ≃ I × OnePoint ℂ)
    (hq : ∀ z, Point.map q z = b (E z).1)
    (hr : ∀ z, lineCoordinate (Point.map r z) = (E z).2) :
    ∃ j : I → (projectiveLine ⟶ F),
      (∀ i, IsClosedImmersion (j i).left) ∧
      (∀ z : ComplexPoint F, ∃! i, z ∈ Set.range (Point.map (j i))) ∧
      (∀ i y, E (Point.map (j i) y) = (i, lineCoordinate y)) := by
  haveI : IsIntegral projectiveLine.left := s0_complex_projective_integral 1
  let E' : ComplexPoint F ≃ I × ComplexPoint projectiveLine :=
    E.trans (Equiv.prodCongr (Equiv.refl I) lineCoordinate.symm.toEquiv)
  have hr' (z) : Point.map r z = (E' z).2 :=
    lineCoordinate.injective ((hr z).trans (lineCoordinate.apply_symm_apply (E z).2).symm)
  obtain ⟨j, hj, hex, he⟩ := selector_component_family F C projectiveLine
    (zmtiso_normal_of_smooth _ projectiveLine.hom) q r b hb E' hq hr'
  refine ⟨j, hj, hex, ?_⟩
  intro i y
  have hh := he i y
  change ((E (Point.map (j i) y)).1,
    lineCoordinate.symm (E (Point.map (j i) y)).2) = (i, y) at hh
  apply Prod.ext
  · exact congrArg (fun z : I × ComplexPoint projectiveLine => z.1) hh
  · have hv := congrArg (fun z : I × ComplexPoint projectiveLine => lineCoordinate z.2) hh
    simpa only [lineCoordinate.apply_symm_apply] using hv

end AlgebraicGeometry.RamifiedNormalization.StageFour

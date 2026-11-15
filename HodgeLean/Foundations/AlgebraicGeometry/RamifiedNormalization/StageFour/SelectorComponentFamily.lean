import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SelectorFibreSection

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Compatible selector and parameter morphisms retain an exhaustive family of actual component immersions with their specified coordinates. -/
theorem selector_component_family
    {I : Type} (F C Y : Over (Spec ↧ℂ))
    [IsProper F.hom] [IsSeparated C.hom]
    [IsIntegral Y.left] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (hY : zmtiso_IsNormal Y.left)
    (q : F ⟶ C) (r : F ⟶ Y)
    (b : I → ComplexPoint C) (hb : Function.Injective b)
    (E : ComplexPoint F ≃ I × ComplexPoint Y)
    (hq : ∀ z, Point.map q z = b (E z).1)
    (hr : ∀ z, Point.map r z = (E z).2) :
    ∃ j : I → (Y ⟶ F),
      (∀ i, IsClosedImmersion (j i).left) ∧
      (∀ z : ComplexPoint F, ∃! i, z ∈ Set.range (Point.map (j i))) ∧
      (∀ i y, E (Point.map (j i) y) = (i, y)) := by
  choose j hj he using selector_fibre_component_section F C Y hY q r b hb E hq hr
  refine ⟨j, hj, ?_, he⟩
  intro z
  refine ⟨(E z).1, ?_, ?_⟩
  · refine ⟨(E z).2, E.injective ?_⟩
    rw [he]
  · intro i hi
    obtain ⟨y, hy⟩ := hi
    have hh := he i y
    rw [hy] at hh
    exact (congrArg Prod.fst hh).symm

end AlgebraicGeometry.RamifiedNormalization.StageFour

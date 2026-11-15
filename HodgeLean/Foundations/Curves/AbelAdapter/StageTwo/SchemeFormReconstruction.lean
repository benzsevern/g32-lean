import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.SchemeFormLocalReconstruction
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.LocalFormSheaf
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.SchemeFormRegularity

/-! # Global scheme representatives of B3 one-forms

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Program Opposite TopologicalSpace
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- Local representatives of one B3 form agree as scheme-form sections on every overlap.
Source: Griffiths–Harris, chapter 0 §2; localSheafForm_eq_of_tangentValues.
HC no distance; AV milestone no distance. -/
theorem localB3Form_compatible (θ : b3_HolForm (Fin d → ℂ) (ComplexPoint X))
    (z w : ComplexPoint X) :
    let U := schemeChartSource X d z
    let V := schemeChartSource X d w
    (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op
        (localSheafForm X d U (localB3Form X d θ z)) =
      (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op
        (localSheafForm X d V (localB3Form X d θ w)) := by
  dsimp only
  rw [localSheafForm_restrict, localSheafForm_restrict]
  apply localSheafForm_eq_of_tangentValues
  intro v hv
  rw [localFormValues_restrict X d _ _ inf_le_left _ v hv,
    localFormValues_restrict X d _ _ inf_le_right _ v hv]
  exact (localB3Form_tangent_values X d θ z v hv.1).trans
    (localB3Form_tangent_values X d θ w v hv.2).symm

/-- The local representatives of a B3 form glue to a global scheme-form section.
Source: Godement, Topologie algébrique et théorie des faisceaux, II.1.2;
TopCat.Sheaf.existsUnique_gluing'.
HC no distance; AV milestone no distance. -/
theorem exists_gluedB3Form (θ : b3_HolForm (Fin d → ℂ) (ComplexPoint X)) :
    ∃ η : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤),
      ∀ z : ComplexPoint X,
        (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op η =
          localSheafForm X d (schemeChartSource X d z) (localB3Form X d θ z) := by
  obtain ⟨η, hη, -⟩ := (holomorphicDeRhamSheaf X d 1).existsUnique_gluing'
    (schemeChartSource X d) ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, mem_extChartAt_source x⟩)
    (fun z ↦ localSheafForm X d (schemeChartSource X d z) (localB3Form X d θ z))
    (fun z w ↦ localB3Form_compatible X d θ z w)
  exact ⟨η, hη⟩

/-- Every B3 form is the literal tangent function of a global scheme one-form.
Source: Griffiths–Harris, chapter 0 §2; exists_gluedB3Form.
HC no distance; AV milestone no distance. -/
theorem schemeFormHolHom_surjective (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] :
    Function.Surjective (schemeFormHolHom Y) := by
  intro θ
  obtain ⟨η, hη⟩ := exists_gluedB3Form Y (TopologicalSpace.dim Y.left) θ
  refine ⟨η, Subtype.ext (funext fun v ↦ ?_)⟩
  have hv : v.1 ∈ schemeChartSource Y (TopologicalSpace.dim Y.left) v.1 :=
    mem_extChartAt_source v.1
  have he := globalFormValue_eq_chartEvaluation_self Y (TopologicalSpace.dim Y.left) 1 η
    (schemeChartSource Y (TopologicalSpace.dim Y.left) v.1)
    (localB3Form Y (TopologicalSpace.dim Y.left) θ v.1) (hη v.1) v.1 hv
  exact (congrArg (fun L ↦ L (fun _ ↦ v.2)) he).trans
    (localB3Form_tangent_values Y (TopologicalSpace.dim Y.left) θ v.1 v hv)

/-- The canonical additive scheme-form equivalence with the specified literal tangent values.
Source: Griffiths–Harris, chapter 0 §2; schemeFormHolHom_surjective.
HC no distance; AV milestone no distance. -/
def schemeFormHolEquiv (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] :
    GlobalHolomorphicForm Y 1 ≃+
      b3_HolForm (Fin (TopologicalSpace.dim Y.left) → ℂ) (ComplexPoint Y) :=
  AddEquiv.ofBijective (schemeFormHolHom Y)
    ⟨schemeFormHolHom_injective Y, schemeFormHolHom_surjective Y⟩

/-- The canonical coordinate equivalence retains the original tangent function exactly.
Source: Griffiths–Harris, chapter 0 §2; schemeFormHolHom.
HC no distance; AV milestone no distance. -/
theorem schemeFormHolEquiv_apply (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom]
    (θ : GlobalHolomorphicForm Y 1) : (schemeFormHolEquiv Y θ).val = schemeForm Y θ := rfl

#print axioms localB3Form_compatible
#print axioms exists_gluedB3Form
#print axioms schemeFormHolHom_surjective
#print axioms schemeFormHolEquiv
#print axioms schemeFormHolEquiv_apply

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

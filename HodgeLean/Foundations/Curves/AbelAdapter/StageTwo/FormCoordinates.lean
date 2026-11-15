import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.Defs
import HodgeLean.Adapters.HolomorphicFormValues

/-! # Faithful tangent values of global scheme forms

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- Tangent values respect addition of sheaf sections.
Source: Griffiths–Harris, chapter 0 §2; globalFormValue.
HC no distance; AV milestone no distance. -/
theorem schemeForm_add (s t : GlobalHolomorphicForm X 1) :
    schemeForm X (s + t) = schemeForm X s + schemeForm X t := by
  funext v
  change globalFormValue X _ 1 v.1 (s + t) (fun _ ↦ v.2) =
    globalFormValue X _ 1 v.1 s (fun _ ↦ v.2) +
      globalFormValue X _ 1 v.1 t (fun _ ↦ v.2)
  erw [map_add]
  rfl

/-- The zero sheaf section has zero tangent values.
Source: Griffiths–Harris, chapter 0 §2; globalFormValue.
HC no distance; AV milestone no distance. -/
theorem schemeForm_zero : schemeForm X 0 = 0 := by
  funext v
  change globalFormValue X _ 1 v.1 0 (fun _ ↦ v.2) = 0
  rw [map_zero]
  rfl

/-- The tangent value map as an additive homomorphism.
Source: Griffiths–Harris, chapter 0 §2; globalFormValue.
HC no distance; AV milestone no distance. -/
def schemeFormAddHom : GlobalHolomorphicForm X 1 →+
    (TangentBundle 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) (ComplexPoint X) → ℂ) where
  toFun := schemeForm X
  map_zero' := schemeForm_zero X
  map_add' := schemeForm_add X

/-- A global scheme form is determined by its tangent values.
Source: Griffiths–Harris, chapter 0 §2; spec_eq_zero_of_globalFormValue_eq_zero.
HC no distance; AV milestone no distance. -/
theorem schemeForm_injective : Function.Injective (schemeForm X) := by
  apply (injective_iff_map_eq_zero (schemeFormAddHom X)).mpr
  intro s hs
  apply spec_eq_zero_of_globalFormValue_eq_zero X _ 1 s
  intro x
  ext v
  have hv := congrFun hs ⟨x, v 0⟩
  change globalFormValue X _ 1 x s (fun _ ↦ v 0) = 0 at hv
  have he : (fun _ : Fin 1 ↦ v 0) = v := by
    funext i
    exact congrArg v (Subsingleton.elim _ _)
  rw [he] at hv
  exact hv

/-- Tangent values retain the complex linear normalization in every fibre.
Source: Griffiths–Harris, chapter 0 §2; globalOneFormCovector.
HC no distance; AV milestone no distance. -/
theorem schemeForm_fibre (s : GlobalHolomorphicForm X 1) (x : ComplexPoint X)
    (a : ℂ) (v w : Fin (TopologicalSpace.dim X.left) → ℂ) :
    schemeForm X s ⟨x, a • v + w⟩ =
      a * schemeForm X s ⟨x, v⟩ + schemeForm X s ⟨x, w⟩ := by
  change globalOneFormCovector X _ s x (a • v + w) = _
  rw [map_add, map_smul]
  rfl

#print axioms schemeFormAddHom
#print axioms schemeForm_injective
#print axioms schemeForm_fibre

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

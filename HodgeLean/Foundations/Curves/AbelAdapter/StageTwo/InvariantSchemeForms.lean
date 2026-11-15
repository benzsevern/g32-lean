import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.FormCoordinates
import HodgeLean.Adapters.HodgeDegreeOneAbelian

/-! # Global scheme forms specified by their exponential covectors

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [GrpObj X]

/-- The exponential covector at zero is additive in the global scheme form.
Source: Birkenhake–Lange, §§1.1–1.2; globalFormValue and expPullback.
HC no distance; AV milestone no distance. -/
def schemeExpCovector : GlobalHolomorphicForm X 1 →+
    ((Fin (TopologicalSpace.dim X.left) → ℂ) →L[ℂ] ℂ) where
  toFun θ := expPullback X (TopologicalSpace.dim X.left) θ 0
  map_zero' := by
    ext v
    change globalFormValue X _ 1 _ 0 _ = 0
    rw [map_zero]
    rfl
  map_add' s t := by
    ext v
    change globalFormValue X _ 1 _ (s + t) _ =
      globalFormValue X _ 1 _ s _ + globalFormValue X _ 1 _ t _
    erw [map_add]
    rfl

/-- Every covector is represented by a unique global form on the projective group.
Source: Birkenhake–Lange, §§1.1–1.2; spec_exists_closed_expPullback_eq and
spec_eq_zero_of_expPullback_zero_eq_zero.
HC no distance; AV milestone no distance. -/
theorem schemeExpCovector_bijective [IsProjective X.hom] :
    Function.Bijective (schemeExpCovector X) := by
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  constructor
  · apply (injective_iff_map_eq_zero (schemeExpCovector X)).mpr
    intro θ hθ
    exact spec_eq_zero_of_expPullback_zero_eq_zero X _ θ hθ
  · intro a
    obtain ⟨θ, _, hθ⟩ := spec_exists_closed_expPullback_eq X a
    exact ⟨θ, hθ⟩

/-- Additive coordinates for all global forms, with their exact exponential values.
Source: Birkenhake–Lange, §§1.1–1.2; spec_exists_closed_expPullback_eq and
spec_eq_zero_of_expPullback_zero_eq_zero.
HC no distance; AV milestone no distance. -/
def schemeExpCovectorEquiv [IsProjective X.hom] : GlobalHolomorphicForm X 1 ≃+
    ((Fin (TopologicalSpace.dim X.left) → ℂ) →L[ℂ] ℂ) :=
  AddEquiv.ofBijective (schemeExpCovector X) (schemeExpCovector_bijective X)

/-- The inverse coordinates have the specified covector without rescaling.
Source: Birkenhake–Lange, §§1.1–1.2; AddEquiv.apply_symm_apply.
HC no distance; AV milestone no distance. -/
theorem schemeExpCovectorEquiv_symm_value [IsProjective X.hom]
    (a : (Fin (TopologicalSpace.dim X.left) → ℂ) →L[ℂ] ℂ) :
    expPullback X (TopologicalSpace.dim X.left) ((schemeExpCovectorEquiv X).symm a) 0 = a :=
  (schemeExpCovectorEquiv X).apply_symm_apply a

#print axioms schemeExpCovector
#print axioms schemeExpCovector_bijective
#print axioms schemeExpCovectorEquiv
#print axioms schemeExpCovectorEquiv_symm_value

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.LocalFormValues

/-! # Holomorphic tangent values of global scheme forms

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Program Opposite TopologicalSpace Filter
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

/-- The literal tangent values of a global scheme form constitute a B3 holomorphic form.
Source: Griffiths–Harris, chapter 0 §2; spec_exists_local_representative and
Algebra.DeRham.mk_induction.
HC no distance; AV milestone no distance. -/
theorem schemeForm_mem_holForm (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ : GlobalHolomorphicForm X 1) :
    schemeForm X θ ∈ b3_HolForm (Fin (TopologicalSpace.dim X.left) → ℂ) (ComplexPoint X) := by
  refine ⟨?_, schemeForm_fibre X θ⟩
  intro v
  obtain ⟨U, hxU, η, hη⟩ := spec_exists_local_representative X _ 1 θ v.1
  have hopen : IsOpen {q : TangentBundle 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ)
      (ComplexPoint X) | q.1 ∈ U} :=
    U.isOpen.preimage (FiberBundle.continuous_proj (Fin (TopologicalSpace.dim X.left) → ℂ)
      (TangentSpace 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ)))
  have hN : {q : TangentBundle 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ)
      (ComplexPoint X) | q.1 ∈ U} ∈ 𝓝 v := hopen.mem_nhds hxU
  have he : schemeForm X θ =ᶠ[𝓝 v] localFormValues X _ U η := by
    filter_upwards [hN] with q hq
    exact congrArg (fun L ↦ L (fun _ ↦ q.2))
      (globalFormValue_eq_chartEvaluation_self X _ 1 θ U η hη q.1 hq)
  exact ((localFormValues_contMDiffOn X _ U η v hxU).contMDiffAt hN).congr_of_eventuallyEq he

/-- Global scheme forms mapped additively to their actual holomorphic tangent functions.
Source: Griffiths–Harris, chapter 0 §2; schemeForm_mem_holForm.
HC no distance; AV milestone no distance. -/
def schemeFormHolHom (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    GlobalHolomorphicForm X 1 →+
      b3_HolForm (Fin (TopologicalSpace.dim X.left) → ℂ) (ComplexPoint X) where
  toFun θ := ⟨schemeForm X θ, schemeForm_mem_holForm X θ⟩
  map_zero' := Subtype.ext (schemeForm_zero X)
  map_add' s t := Subtype.ext (schemeForm_add X s t)

/-- The holomorphic tangent-function map retains all global scheme forms faithfully.
Source: Griffiths–Harris, chapter 0 §2; schemeForm_injective.
HC no distance; AV milestone no distance. -/
theorem schemeFormHolHom_injective (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    Function.Injective (schemeFormHolHom X) := by
  intro s t h
  exact schemeForm_injective X (congrArg Subtype.val h)

#print axioms schemeForm_mem_holForm
#print axioms schemeFormHolHom
#print axioms schemeFormHolHom_injective

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

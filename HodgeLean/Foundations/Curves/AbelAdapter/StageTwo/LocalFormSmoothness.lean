import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.LocalFormCoefficients

/-! # Smooth tangent values of local scheme one-forms

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters Opposite TopologicalSpace
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- Evaluation of the differential of a local holomorphic function is holomorphic on its tangent bundle.
Source: Griffiths–Harris, chapter 0 §2; ContMDiffOn.contMDiffOn_tangentMapWithin.
HC no distance; AV milestone no distance. -/
theorem localSection_tangentDerivative (U : Opens (TopCat.of (ComplexPoint X)))
    (f : OpenHolomorphicFunctions X d (op U)) :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ).tangent 𝓘(ℂ, ℂ) ω
      (fun v : TangentBundle 𝓘(ℂ, Fin d → ℂ) (ComplexPoint X) ↦
        mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) (extendedSection X d (op U) f) v.1 v.2)
      {v | v.1 ∈ U} := by
  have hf : ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω
      (extendedSection X d (op U) f) (U : Set (ComplexPoint X)) :=
    fun x hx ↦ (localSection_contMDiffAt X d U f hx).contMDiffWithinAt
  have ht := hf.contMDiffOn_tangentMapWithin (m := ω) (by simp) U.isOpen.uniqueMDiffOn
  have h := (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℂ, ℂ) (n := ω)).comp_contMDiffOn ht
  apply h.congr
  intro v hv
  change _ = mfderivWithin 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ)
      (extendedSection X d (op U) f) (U : Set (ComplexPoint X)) v.1 v.2
  rw [mfderivWithin_of_isOpen U.isOpen hv]

#print axioms localSection_tangentDerivative

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

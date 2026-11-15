import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.LocalFormRelations

/-! # Restriction and sheafification of local one-form representatives

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters Opposite TopologicalSpace
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- Restriction retains the exact tangent values on the smaller open set.
Source: Griffiths–Harris, chapter 0 §2; chartEvaluation_formRestriction.
HC no distance; AV milestone no distance. -/
theorem localFormValues_restrict (U V : Opens (TopCat.of (ComplexPoint X))) (h : V ≤ U)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) 1)
    (v : TangentBundle 𝓘(ℂ, Fin d → ℂ) (ComplexPoint X)) (hv : v.1 ∈ V) :
    localFormValues X d V (formRestriction X d (homOfLE h).op 1 θ) v =
      localFormValues X d U θ v :=
  congrArg (fun L ↦ L (fun _ ↦ v.2))
    (chartEvaluation_formRestriction X d (homOfLE h).op v.1 1 θ
      (extChartAt_self_mem_chartSectionDomain X d (op V) hv))

/-- A raw local representative mapped into the actual sheaf of holomorphic one-forms.
Source: Godement, Topologie algébrique et théorie des faisceaux, II.1.2; toSheafify.
HC no distance; AV milestone no distance. -/
def localSheafForm (U : Opens (TopCat.of (ComplexPoint X)))
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) 1) :
    (holomorphicDeRhamSheaf X d 1).presheaf.obj (op U) :=
  (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (holomorphicDeRhamPresheaf X d 1)).app (op U) (Submodule.Quotient.mk θ)

/-- Sheafification of a raw local representative commutes with restriction.
Source: Godement, Topologie algébrique et théorie des faisceaux, II.1.2; toSheafify.naturality.
HC no distance; AV milestone no distance. -/
theorem localSheafForm_restrict (U V : Opens (TopCat.of (ComplexPoint X))) (h : V ≤ U)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) 1) :
    (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE h).op (localSheafForm X d U θ) =
      localSheafForm X d V (formRestriction X d (homOfLE h).op 1 θ) := by
  have hn := (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (holomorphicDeRhamPresheaf X d 1)).naturality (homOfLE h).op
  exact (congrArg (fun k ↦ k (Submodule.Quotient.mk θ)) hn).symm

/-- Equal tangent values give equal local sections after the defining quotient and sheafification.
Source: Griffiths–Harris, chapter 0 §2; rawForm_mem_kernel_of_tangentValues_zero.
HC no distance; AV milestone no distance. -/
theorem localSheafForm_eq_of_tangentValues (U : Opens (TopCat.of (ComplexPoint X)))
    (θ η : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) 1)
    (h : ∀ v : TangentBundle 𝓘(ℂ, Fin d → ℂ) (ComplexPoint X), v.1 ∈ U →
      localFormValues X d U θ v = localFormValues X d U η v) :
    localSheafForm X d U θ = localSheafForm X d U η := by
  unfold localSheafForm
  congr 1
  apply (Submodule.Quotient.eq _).mpr
  apply rawForm_mem_kernel_of_tangentValues_zero X d U
  intro v hv
  simp only [map_sub, Pi.sub_apply, h v hv, sub_self]

#print axioms localFormValues_restrict
#print axioms localSheafForm
#print axioms localSheafForm_restrict
#print axioms localSheafForm_eq_of_tangentValues

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

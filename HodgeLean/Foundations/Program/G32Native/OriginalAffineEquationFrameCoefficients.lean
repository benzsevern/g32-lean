import HodgeLean.Foundations.TubularEuler.ActualConormalSectionDataHelpers
import HodgeLean.Foundations.TubularEuler.NormalFrameRegularCoefficientHelpers
import HodgeLean.Foundations.BundleResolution.ModuleSectionRefineHelpers

/-! # Analytic coefficients of original equations in retained conormal frames

The coefficients come from regular sections on the original base open.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution HodgeLean.Foundations.BundleThom

/-- Every descended affine equation has analytic coefficient functions in
any specified algebraic conormal frame on a smaller original base open.
Source: `i1_moduleSectionValue_refine`,
`normalFrameSectionCoefficient_evaluate`, and
`normalFrameSectionCoefficient_contMDiffOn`.
HC no distance; AV milestone no distance. -/
theorem originalAffineEquation_frame_coefficients
    (Q : Over (Spec ↧ℂ)) {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom)
    (k m : ℕ) [SmoothOfRelativeDimension m Q.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
    (U : Q.left.Opens) (hU : U ≤ j ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k)) :
    ∃ r : Fin k → Γ(Q.left, U),
      (∀ (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) (i : Fin k),
        i1_conormalFrameCoordinates j k U E x hx
          (i1_moduleSectionValue (Conormal.sheaf j) (j ⁻¹ᵁ A)
            (actualConormalAffineSectionData j A hA u).localSection x (hU hx)) i =
          Point.evaluate U (r i) x) ∧
      ContMDiffOn 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin k → ℂ) ω
        (fun x : ComplexPoint Q => fun i : Fin k => Point.evaluate U (r i) x)
        (Point.overOpen U) := by
  let s := i1_moduleSectionRefine (Conormal.sheaf j) hU
    (actualConormalAffineSectionData j A hA u).localSection
  refine ⟨normalFrameSectionCoefficient j k U E s, ?_,
    normalFrameSectionCoefficient_contMDiffOn j k U E s m⟩
  intro x hx i
  have hv := i1_moduleSectionValue_refine (Conormal.sheaf j) hU
    (actualConormalAffineSectionData j A hA u).localSection x hx
  rw [← hv]
  exact normalFrameSectionCoefficient_evaluate j k U E s x hx i

#print axioms originalAffineEquation_frame_coefficients

end HodgeLean.Foundations.TubularEuler

import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateInclusionCharts
import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleSectionsHelpers

/-! # Original discarded-ratio sections of the projective immersion ideal -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The discarded homogeneous ratio vanishes as a regular section under
the original projective immersion, before choosing affine coordinates. -/
theorem paired_c3_projective_inclusion_discarded_section {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (j : Fin (n + 1)) (hj : j ∉ Set.range e) :
    (pairedC3PolynomialCoordinateInclusion (A := ℂ) e).app
      (ProjSpace.standardOpen ℂ n (e i)) (ProjSpace.coordinateRatioSection ℂ n (e i) j) = 0 := by
  let f := pairedC3GradedCoordinateProjection (A := ℂ) e
  let hf := s2e_irrelevant_le_map_of_graded_retraction _ _ f
    (pairedC3GradedCoordinateSection e) (paired_c3_graded_coordinate_retraction e)
  have h := congrArg (fun ψ => ψ (pairedC3CoordinateNormalRatio (A := ℂ) e i j))
    (Proj.awayToSection_comp_appLE f hf (isHomogeneous_X ℂ (e i)))
  change (Proj.map f hf).appLE _ _ le_rfl
    (ProjSpace.coordinateRatioSection ℂ n (e i) j) =
      Proj.awayToSection _ _ (Away.map f (X (e i)) (pairedC3CoordinateNormalRatio e i j)) at h
  rw [paired_c3_coordinate_normal_ratio_vanishes e i j hj, map_zero] at h
  simpa only [Scheme.Hom.appLE_eq_app, pairedC3PolynomialCoordinateInclusion, f, hf] using h

/-- The original discarded ratio lifted to a section of the categorical
ideal kernel on its ambient standard open. -/
def pairedC3ProjectiveIdealGenerator {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (j : Fin (n + 1)) (hj : j ∉ Set.range e) :
    Γ(s2c_idealModule (pairedC3PolynomialCoordinateInclusion (A := ℂ) e),
      ProjSpace.standardOpen ℂ n (e i)) :=
  (s2e_idealModule_sections_equiv _ _).symm
    ⟨ProjSpace.coordinateRatioSection ℂ n (e i) j,
      paired_c3_projective_inclusion_discarded_section e i j hj⟩

/-- Inclusion of the categorical ideal generator gives exactly its
original homogeneous ratio, with coefficient one. -/
theorem paired_c3_projective_ideal_generator_inclusion {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (j : Fin (n + 1)) (hj : j ∉ Set.range e) :
    (CategoryTheory.Limits.kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (pairedC3PolynomialCoordinateInclusion (A := ℂ) e).toRingCatSheafHom)).val.app
        (Opposite.op (ProjSpace.standardOpen ℂ n (e i)))
        (pairedC3ProjectiveIdealGenerator e i j hj) =
      ProjSpace.coordinateRatioSection ℂ n (e i) j := by
  rw [← s2e_idealModule_sections_equiv_coe]
  exact congrArg Subtype.val ((s2e_idealModule_sections_equiv _ _).apply_symm_apply _)

end HodgeLean.Foundations.Program.G32Native

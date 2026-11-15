import HodgeLean.Foundations.Program.G32Native.PairedResidualCurveFibre
import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveMarkedPoint
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension
import HodgeLean.Foundations.Program.SchoenTowerFibreTopology

/-! # The unit conormal of the marked fibre of a projective-line ruling -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The scalar affine spectrum carries the identity ground-field map.
Source: Hartshorne, Algebraic Geometry, II.2. -/
theorem pairedC3_scalar_spec_structure :
    ComplexPoint.affineSpecStructureMap ℂ = 𝟙 (Spec ↧ℂ) := by
  change Spec.map (𝟙 (CommRingCat.of ℂ)) = 𝟙 (Spec (CommRingCat.of ℂ))
  exact Spec.map_id (CommRingCat.of ℂ)

#print axioms pairedC3_scalar_spec_structure

/-- The marked diagonal chart point is a section over the original field.
Source: Hartshorne, Algebraic Geometry, II.2.5. -/
theorem pairedC3_marked_projective_point_section :
    (projectiveLineChart (A := ℂ) 1 (1 : ℂ)).left ≫ projectiveLine.hom =
      𝟙 (Spec (CommRingCat.of ℂ)) := by
  calc
    _ = ComplexPoint.affineSpecStructureMap ℂ :=
      Over.w (projectiveLineChart (A := ℂ) 1 (1 : ℂ))
    _ = _ := pairedC3_scalar_spec_structure

#print axioms pairedC3_marked_projective_point_section

/-- The specified diagonal point is a closed section of the separated line.
Source: Hartshorne, Algebraic Geometry, II.4. -/
theorem pairedC3_marked_projective_point_closed :
    IsClosedImmersion (projectiveLineChart (A := ℂ) 1 (1 : ℂ)).left := by
  letI : IsSeparated projectiveLine.hom :=
    (ProjectiveSpace.toBaseProper (Fin 2) (Spec ↧ℂ)).toIsSeparated
  haveI : IsClosedImmersion
      ((projectiveLineChart (A := ℂ) 1 (1 : ℂ)).left ≫ projectiveLine.hom) := by
    rw [pairedC3_marked_projective_point_section]
    have h : IsClosedImmersion (Spec.map (𝟙 (CommRingCat.of ℂ))) :=
      IsClosedImmersion.spec_of_surjective (𝟙 (CommRingCat.of ℂ))
        (by intro x; exact ⟨x, rfl⟩)
    rw [Spec.map_id] at h
    exact h
  exact IsClosedImmersion.of_comp
    (projectiveLineChart (A := ℂ) 1 (1 : ℂ)).left projectiveLine.hom

#print axioms pairedC3_marked_projective_point_closed

/-- A flat marked fibre over a smooth curve retains the unit conormal
when the marked section is supplied as its original scheme morphism.
Source: Hartshorne, Algebraic Geometry, II.8, flat conormal base change. -/
theorem pairedC3_section_fibre_conormal_unit
    {S T : Scheme.{0}} (Y : Over (Spec ↧ℂ))
    [SmoothOfRelativeDimension 1 Y.hom]
    (z : Spec ↧ℂ ⟶ Y.left) [IsClosedImmersion z]
    (hz : z ≫ Y.hom = 𝟙 (Spec ↧ℂ))
    (s : S ⟶ T) [IsClosedImmersion s]
    (g : T ⟶ Y.left) [Flat g] (p : S ⟶ Spec ↧ℂ)
    (sq : IsPullback p s z g) :
    Nonempty (s2c_conormal s ≅
      (SheafOfModules.unit S.ringCatSheaf : S.Modules)) := by
  let z₀ : ComplexPoint Y :=
    Over.homMk (U := Over.mk (𝟙 (Spec ↧ℂ))) (V := Y) z hz
  letI : IsClosedImmersion z₀.left := ‹IsClosedImmersion z›
  exact ⟨residual_curve_fibre_conormal_unit Y z₀ s g p sq⟩

#print axioms pairedC3_section_fibre_conormal_unit

/-- The actual diagonal fibre of a smooth projective-line ruling has the
untwisted unit conormal on the original fibre scheme.
Source: Hartshorne, Algebraic Geometry, II.8, flat conormal base change;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem pairedC3_projective_ruling_conormal_unit
    {S T : Scheme.{0}} (s : S ⟶ T) [IsClosedImmersion s]
    (g : T ⟶ projectiveLine.left) [Smooth g] (p : S ⟶ Spec ↧ℂ)
    (sq : IsPullback p s (projectiveLineChart (A := ℂ) 1 (1 : ℂ)).left g) :
    Nonempty (s2c_conormal s ≅
      (SheafOfModules.unit S.ringCatSheaf : S.Modules)) := by
  letI : SmoothOfRelativeDimension 1 projectiveLine.hom :=
    s0_complex_projective_relative_dimension 1
  letI : IsClosedImmersion (projectiveLineChart (A := ℂ) 1 (1 : ℂ)).left :=
    pairedC3_marked_projective_point_closed
  letI : Flat g := ⟨fun {_} hU {_} hV h => (g.smooth_appLE hU hV h).flat⟩
  exact pairedC3_section_fibre_conormal_unit projectiveLine
    (projectiveLineChart (A := ℂ) 1 (1 : ℂ)).left
    pairedC3_marked_projective_point_section s g p sq

#print axioms pairedC3_projective_ruling_conormal_unit
end HodgeLean.Foundations.Program.G32Native

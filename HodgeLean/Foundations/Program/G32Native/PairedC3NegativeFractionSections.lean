import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeFractionTransitions
import HodgeLean.Foundations.Program.G32Native.PairedC3DualFrameTransitions
import HodgeLean.Foundations.Program.G32Native.PairedC3SectionScalars

/-! # Actual native negative-line sections from homogeneous fractions -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open ProjSpaceCech AlgebraicGeometry.ProjSpace Scheme.Modules
open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original coordinate section restricts to an actual frame on every
coordinate intersection containing its index. -/
theorem paired_c3_twisting_frame_intersection (R : Type) [CommRing R] (n : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I) :
    IsFrameOn ((twistingSheaf R n).presheaf.map
      (homOfLE (le_top : coordinateIntersection R n I ≤ ⊤)).op
        (twistingCoordinateSection R n i)) (coordinateIntersection R n I) :=
  ((isFrameOn_twistingCoordinateSection R n i).map
    (homOfLE (le_top : coordinateIntersection R n I ≤ ⊤))).mono
      (coordinateIntersection_le_standardOpen R n hi)

/-- A dual coordinate frame identifies degree minus one fractions with all
sections of the original native dual, with the structural base action. -/
def pairedC3NegativeFractionSectionEquivAt (R : Type) [CommRing R] (n : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I) :
    GradedModule.sec (GradedModule.FD R n (-1)) I ≃ₗ[R]
      sectionModuleOverBase ((𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))) ≫ π R n)
        (twistingSheaf R n).dual (coordinateIntersection R n I) :=
  pairedC3NegativeFractionCoefficient R n i hi ≪≫ₗ
    (pairedC3SectionScalarEquivOverBase ((𝟙 _) ≫ π R n)
      (pairedC3NativeDualFrameEquiv (paired_c3_twisting_frame_intersection R n i hi))).symm

#print axioms paired_c3_twisting_frame_intersection
#print axioms pairedC3NegativeFractionSectionEquivAt
/-- Evaluation in the chosen native dual frame recovers the original
regular fraction coefficient literally. -/
theorem paired_c3_negative_section_evaluation (R : Type) [CommRing R] (n : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I)
    (z : GradedModule.sec (GradedModule.FD R n (-1)) I) :
    pairedC3NativeDualFrameEquiv (paired_c3_twisting_frame_intersection R n i hi)
      (show Γ((twistingSheaf R n).dual, coordinateIntersection R n I) from
        pairedC3NegativeFractionSectionEquivAt R n i hi z) =
      (show Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R), coordinateIntersection R n I) from
        pairedC3NegativeFractionCoefficient R n i hi z) :=
  (pairedC3NativeDualFrameEquiv (paired_c3_twisting_frame_intersection R n i hi)).apply_symm_apply _

#print axioms paired_c3_negative_section_evaluation
/-- The original positive coordinate frames have their literal ratio
transition on every common coordinate intersection. -/
theorem paired_c3_twisting_frame_transition (R : Type) [CommRing R] (n : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I)
    (j : Fin (n + 1)) :
    Scheme.Modules.GlueOfCocycle.rO (coordinateIntersection_le_standardOpen R n hi)
        (coordinateRatioSection R n i j) •
      (twistingSheaf R n).presheaf.map
        (homOfLE (le_top : coordinateIntersection R n I ≤ ⊤)).op (twistingCoordinateSection R n i) =
      (twistingSheaf R n).presheaf.map
        (homOfLE (le_top : coordinateIntersection R n I ≤ ⊤)).op (twistingCoordinateSection R n j) := by
  let M := twistingSheaf R n
  let hVi := coordinateIntersection_le_standardOpen R n hi
  have h := congrArg (fun s : Γ(M, standardOpen R n i) =>
    M.presheaf.map (homOfLE hVi).op s)
      (coordinateRatioSection_smul_twistingCoordinateSection R n i j)
  change M.presheaf.map (homOfLE hVi).op
      (coordinateRatioSection R n i j •
        M.presheaf.map (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op (twistingCoordinateSection R n i)) =
    M.presheaf.map (homOfLE hVi).op
      (M.presheaf.map (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op (twistingCoordinateSection R n j)) at h
  rw [M.map_smul, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
    ← M.presheaf.map_comp] at h
  exact h

#print axioms paired_c3_twisting_frame_transition
/-- The actual native negative-line section does not depend on which
inverted coordinate supplied its local frame. -/
theorem paired_c3_negative_section_independent (R : Type) [CommRing R] (n : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I)
    (j : Fin (n + 1)) (hj : j ∈ I)
    (z : GradedModule.sec (GradedModule.FD R n (-1)) I) :
    pairedC3NegativeFractionSectionEquivAt R n i hi z =
      pairedC3NegativeFractionSectionEquivAt R n j hj z := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  let W := coordinateIntersection R n I
  let M := twistingSheaf R n
  let ei : Γ(M.dual, W) ≃ₗ[Γ(P, W)] Γ(P, W) :=
    pairedC3NativeDualFrameEquiv (paired_c3_twisting_frame_intersection R n i hi)
  let ej : Γ(M.dual, W) ≃ₗ[Γ(P, W)] Γ(P, W) :=
    pairedC3NativeDualFrameEquiv (paired_c3_twisting_frame_intersection R n j hj)
  let vi : Γ(M.dual, W) := pairedC3NegativeFractionSectionEquivAt R n i hi z
  let vj : Γ(M.dual, W) := pairedC3NegativeFractionSectionEquivAt R n j hj z
  let ci : Γ(P, W) := pairedC3NegativeFractionCoefficient R n i hi z
  let cj : Γ(P, W) := pairedC3NegativeFractionCoefficient R n j hj z
  let r : Γ(P, W) := Scheme.Modules.GlueOfCocycle.rO
    (coordinateIntersection_le_standardOpen R n hi) (coordinateRatioSection R n i j)
  have hei : ei vi = ci := paired_c3_negative_section_evaluation R n i hi z
  have hej : ej vj = cj := paired_c3_negative_section_evaluation R n j hj z
  change vi = vj
  apply ej.injective
  calc
    ej vi = r * ei vi := paired_c3_native_dual_frame_transition
      (paired_c3_twisting_frame_intersection R n i hi)
      (paired_c3_twisting_frame_intersection R n j hj) r
      (paired_c3_twisting_frame_transition R n i hi j).symm vi
    _ = r * ci := congrArg (fun c : Γ(P, W) => r * c) hei
    _ = cj := (paired_c3_negative_coefficient_transition R n i hi j hj z).symm
    _ = ej vj := hej.symm

#print axioms paired_c3_negative_section_independent
end HodgeLean.Foundations.Program.G32Native

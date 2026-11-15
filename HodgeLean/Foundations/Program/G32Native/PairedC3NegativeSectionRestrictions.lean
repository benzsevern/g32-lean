import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeFractionSections

/-! # Restricting the actual negative-line section comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open ProjSpaceCech AlgebraicGeometry.ProjSpace Scheme.Modules
open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra

/-- On coordinate intersections, native dual evaluation in a fixed coordinate
commutes with restriction, using the original global coordinate section. -/
theorem paired_c3_twisting_dual_evaluation_restrict (R : Type) [CommRing R] (n : ℕ)
    {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J)
    (i : Fin (n + 1)) (hi : i ∈ I)
    (φ : Γ((twistingSheaf R n).dual, coordinateIntersection R n I)) :
    pairedC3NativeDualFrameEquiv (paired_c3_twisting_frame_intersection R n i (hIJ hi))
        ((twistingSheaf R n).dual.presheaf.map
          (homOfLE (coordinateIntersection_mono R n hIJ)).op φ) =
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.map
        (homOfLE (coordinateIntersection_mono R n hIJ)).op
          (pairedC3NativeDualFrameEquiv (paired_c3_twisting_frame_intersection R n i hi) φ) := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  let M := twistingSheaf R n
  let WI := coordinateIntersection R n I
  let WJ := coordinateIntersection R n J
  let hW : WJ ≤ WI := coordinateIntersection_mono R n hIJ
  let f := (homOfLE hW).op
  let H := pairedC3HomSheaf M (SheafOfModules.unit P.ringCatSheaf)
  let sI : Γ(M, WI) := M.presheaf.map (homOfLE le_top).op (twistingCoordinateSection R n i)
  let sJ : Γ(M, WJ) := M.presheaf.map (homOfLE le_top).op (twistingCoordinateSection R n i)
  let ψI : Γ(H, WI) := (pairedC3DualPresheafIso M).hom.val.app (op WI) φ
  let ψJ : Γ(H, WJ) := (pairedC3DualPresheafIso M).hom.val.app (op WJ) (M.dual.presheaf.map f φ)
  have hn : ψJ = H.presheaf.map f ψI :=
    PresheafOfModules.naturality_apply (pairedC3DualPresheafIso M).hom.val f φ
  have hs : sJ = M.presheaf.map f sI := by
    dsimp only [sJ, sI, f]
    rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
    rfl
  change pairedC3FrameEvaluation sJ ψJ = P.presheaf.map f (pairedC3FrameEvaluation sI ψI)
  exact (congrArg (pairedC3FrameEvaluation sJ) hn).trans
    ((congrArg (fun t : Γ(M, WJ) => pairedC3FrameEvaluation t (H.presheaf.map f ψI)) hs).trans
      (paired_c3_dual_evaluation_restrict hW sI ψI))

#print axioms paired_c3_twisting_dual_evaluation_restrict
/-- With a fixed inverted coordinate, the actual negative-line section
comparison commutes with the original native restrictions. -/
theorem paired_c3_negative_section_at_restrict (R : Type) [CommRing R] (n : ℕ)
    {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J)
    (i : Fin (n + 1)) (hi : i ∈ I)
    (z : GradedModule.sec (GradedModule.FD R n (-1)) I) :
    sectionRestrictionOverBase ((𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))) ≫ π R n)
        (twistingSheaf R n).dual (coordinateIntersection_mono R n hIJ)
        (pairedC3NegativeFractionSectionEquivAt R n i hi z) =
      pairedC3NegativeFractionSectionEquivAt R n i (hIJ hi) (GradedModule.secIncl _ hIJ z) := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  let M := twistingSheaf R n
  let WI := coordinateIntersection R n I
  let WJ := coordinateIntersection R n J
  let f := (homOfLE (coordinateIntersection_mono R n hIJ)).op
  let ei : Γ(M.dual, WI) ≃ₗ[Γ(P, WI)] Γ(P, WI) :=
    pairedC3NativeDualFrameEquiv (paired_c3_twisting_frame_intersection R n i hi)
  let ej : Γ(M.dual, WJ) ≃ₗ[Γ(P, WJ)] Γ(P, WJ) :=
    pairedC3NativeDualFrameEquiv (paired_c3_twisting_frame_intersection R n i (hIJ hi))
  let vi : Γ(M.dual, WI) := pairedC3NegativeFractionSectionEquivAt R n i hi z
  let vj : Γ(M.dual, WJ) := pairedC3NegativeFractionSectionEquivAt R n i (hIJ hi) (GradedModule.secIncl _ hIJ z)
  let ci : Γ(P, WI) := pairedC3NegativeFractionCoefficient R n i hi z
  let cj : Γ(P, WJ) := pairedC3NegativeFractionCoefficient R n i (hIJ hi) (GradedModule.secIncl _ hIJ z)
  have hei : ei vi = ci := paired_c3_negative_section_evaluation R n i hi z
  have hej : ej vj = cj := paired_c3_negative_section_evaluation R n i (hIJ hi) (GradedModule.secIncl _ hIJ z)
  change M.dual.presheaf.map f vi = vj
  apply ej.injective
  calc
    ej (M.dual.presheaf.map f vi) = P.presheaf.map f (ei vi) :=
      paired_c3_twisting_dual_evaluation_restrict R n hIJ i hi vi
    _ = P.presheaf.map f ci := congrArg (fun a : Γ(P, WI) => P.presheaf.map f a) hei
    _ = cj := (paired_c3_negative_coefficient_restrict R n hIJ i hi z).symm
    _ = ej vj := hej.symm

#print axioms paired_c3_negative_section_at_restrict
end HodgeLean.Foundations.Program.G32Native

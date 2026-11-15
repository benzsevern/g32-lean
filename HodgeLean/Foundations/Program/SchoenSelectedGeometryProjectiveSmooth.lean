import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveCharts

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The integral projective model's structure map to its coefficient scheme.
Source: Hartshorne, Algebraic Geometry, II.2.5, standard projective affine charts. -/
def s0_integral_projective_structure (n : ℕ) :
    Proj (UniversalGrading n) ⟶ Spec ↧(ULift.{0} ℤ) :=
  Proj.toSpecZero (UniversalGrading n) ≫ Spec.map (CommRingCat.ofHom
    (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) (ULift.{0} ℤ)).symm.toRingHom)

set_option backward.isDefEq.respectTransparency.types false in
theorem s0_integral_projective_smooth (n : ℕ) : Smooth (s0_integral_projective_structure n) := by
  let U := Proj.affineOpenCoverOfIrrelevantLESpan (UniversalGrading n)
    (MvPolynomial.X : Fin (n + 1) → UniversalRing n)
    (fun i ↦ MvPolynomial.isHomogeneous_X _ i) (fun _ ↦ zero_lt_one)
    (irrelevant_le_span_coordinates n)
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) U.openCover]
  intro i
  change Smooth (Proj.awayι (UniversalGrading n) (MvPolynomial.X i : UniversalRing n)
    (MvPolynomial.isHomogeneous_X (ULift.{0} ℤ) i) zero_lt_one ≫
    (Proj.toSpecZero (UniversalGrading n) ≫ Spec.map (CommRingCat.ofHom
      (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) (ULift.{0} ℤ)).symm.toRingHom)))
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  change Smooth (Spec.map (CommRingCat.ofHom (s0_projective_chart_base i)))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact s0_projective_chart_smooth i

#print axioms s0_integral_projective_structure
#print axioms s0_integral_projective_smooth

theorem s0_integral_projective_terminal_smooth (n : ℕ) :
    Smooth (CategoryTheory.Limits.terminal.from (C := Scheme.{0}) (Proj (UniversalGrading n))) := by
  let e : Spec ↧(ULift.{0} ℤ) ≅ CategoryTheory.Limits.terminal Scheme :=
    specULiftZIsTerminal.uniqueUpToIso CategoryTheory.Limits.terminalIsTerminal
  have he : e.hom = CategoryTheory.Limits.terminal.from (Spec ↧(ULift.{0} ℤ)) :=
    Subsingleton.elim _ _
  haveI : IsIso (CategoryTheory.Limits.terminal.from (Spec ↧(ULift.{0} ℤ))) := by
    rw [← he]
    infer_instance
  haveI := s0_integral_projective_smooth n
  have hc : Smooth (s0_integral_projective_structure n ≫
      CategoryTheory.Limits.terminal.from (Spec ↧(ULift.{0} ℤ))) := inferInstance
  have hcomp : s0_integral_projective_structure n ≫
      CategoryTheory.Limits.terminal.from (Spec ↧(ULift.{0} ℤ)) =
      CategoryTheory.Limits.terminal.from (Proj (UniversalGrading n)) := Subsingleton.elim _ _
  rwa [hcomp] at hc

#print axioms s0_integral_projective_terminal_smooth

theorem s0_projective_space_smooth (n : ℕ) (S : Scheme.{0}) :
    Smooth (ProjectiveSpace.toBase (Fin (n + 1)) S) := by
  haveI := s0_integral_projective_terminal_smooth n
  change Smooth (CategoryTheory.Limits.pullback.fst
    (CategoryTheory.Limits.terminal.from S)
    (CategoryTheory.Limits.terminal.from (Proj (UniversalGrading n))))
  infer_instance

#print axioms s0_projective_space_smooth

end HodgeLean.Foundations.Program

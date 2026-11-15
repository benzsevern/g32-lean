import HodgeLean.Foundations.Program.SchoenTowerL1aPointJetInterpolation
import HodgeLean.Foundations.Program.SchoenTowerL1aProjectiveAffine

/-! # Separating sections on affine neighborhoods of actual projective curve support

The actual projective curve has an affine neighborhood of its finite support
and a separating section with nonzero first-order classes at all listed points.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A finite tuple on the retained projective curve has an actual affine neighborhood and a separating section with nonzero first-order point classes.
Source: Hartshorne, Algebraic Geometry, II.2, II.8 and III.10; Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10. -/
theorem s2v_l1a_projective_curve_separating_first_jets
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1)
    (n : ℕ) (p : Fin (n + 1) → ComplexPoint Z) :
    ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (u : U ⟶ Z)
      (y : Fin (n + 1) → ComplexPoint U) (z : Γ(U.left, ⊤)),
      IsOpenImmersion u.left ∧ (∀ j, Point.map u (y j) = p j) ∧
      Point.evaluate ⊤ z (y 0) = 0 ∧
      (∀ j k, p j ≠ p k → Point.evaluate ⊤ z (y j) ≠ Point.evaluate ⊤ z (y k)) ∧
      (∀ j, z - U.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
          (Point.evaluate ⊤ z (y j))) ∉ ((y j).left.ker.ideal ⟨⊤, @isAffineOpen_top _ hU⟩) ^ 2) := by
  obtain ⟨A, hpA⟩ := s2v_l1a_projective_finite_affine_neighborhood Z p
  let U := ComplexPoint.openScheme Z A.1
  let u := ComplexPoint.openInclusion Z A.1
  let y (j : Fin (n + 1)) : ComplexPoint U := ComplexPoint.asOpenPoint Z A.1 (p j) (hpA j)
  letI : IsAffine U.left := A.2
  letI : SmoothOfRelativeDimension 1 Z.hom := by
    simpa only [hdim] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim Z.left) Z.hom)
  letI : SmoothOfRelativeDimension 1 U.hom := by
    change SmoothOfRelativeDimension 1 (A.1.ι ≫ Z.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 A.1.ι Z.hom
  have hy (j : Fin (n + 1)) : Point.map u (y j) = p j := by
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac Z A.1 (p j) (hpA j)
  obtain ⟨z, hz0, hzsep, hzjet⟩ := s2v_l1a_affine_curve_separating_first_jets U n y
  refine ⟨U, inferInstance, u, y, z,
    inferInstanceAs (IsOpenImmersion A.1.ι), hy, hz0, ?_, hzjet⟩
  intro j k hjk
  apply hzsep j k
  intro heq
  exact hjk ((hy j).symm.trans ((congrArg (Point.map u) heq).trans (hy k)))

end HodgeLean.Foundations.Program

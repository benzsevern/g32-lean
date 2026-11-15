import HodgeLean.Foundations.Program.SchoenCycleAffinePointClosureIdeal
import HodgeLean.Foundations.Program.SchoenCycleProjectiveLinearSectionIdeal

/-! # The actual closure-defined hyperplane ideal on standard affine charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The actual ideal sheaf defined by the scheme closure of the projective linear point set has its standard-chart regular linear generator.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_projective_hyperplane_chart_ideal
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k : ℕ) (hd : Module.finrank ℂ V = k + 1) (L : V →ₗ[ℂ] ℂ) (i : Fin (k + 1))
    [LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))] :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let H : PP.left.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (Point.underlying ''
        {R : ComplexPoint PP | ∃ (v : V) (hv : v ≠ 0),
          (s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd).symm R =
            Projectivization.mk ℂ v hv ∧ L v = 0}))
    H.ideal (s2e_standardProjectiveAffineOpen i) =
      Ideal.span {s2e_standardProjectiveLinearSection V k hd L i} := by
  letI : LocallyOfFiniteType
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom :=
    inferInstanceAs (LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
  apply s2e_affine_point_closure_ideal
  · exact s2e_standardProjectiveLinearSection_span_isRadical V k hd L i
  · intro R hR
    exact s2e_projective_linear_pointSet_iff_evaluate V k hd L i R hR

end HodgeLean.Foundations.Program

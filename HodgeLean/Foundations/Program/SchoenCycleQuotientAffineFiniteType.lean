import HodgeLean.Foundations.Program.SchoenCycleComplexAffineFiniteType

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Finite surjective descent from the actual complex affine section extension gives finite type downstairs.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 7.8. -/
theorem s2e_finite_surjective_affine_sections_finiteType
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) :
    letI := s2e_step1_sectionAlgebra Y U
    Algebra.FiniteType ℂ Γ(Y.left, U) := by
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X W
  letI : Algebra Γ(Y.left, U) Γ(X.left, W) := (q.left.app U).hom.toAlgebra
  letI := s2e_complex_section_app_tower X Y q U
  haveI : Module.Finite Γ(Y.left, U) Γ(X.left, W) := q.left.finite_app U hU
  haveI : Algebra.FiniteType ℂ Γ(X.left, W) :=
    s2e_complex_affine_sections_finiteType X W (hU.preimage q.left)
  haveI := IsSchemeTheoreticallyDominant.of_isDominant q.left
  have hinj : Function.Injective (algebraMap Γ(Y.left, U) Γ(X.left, W)) := q.left.app_injective U
  exact ⟨fg_of_fg_of_fg ℂ Γ(Y.left, U) Γ(X.left, W)
    Algebra.FiniteType.out Module.Finite.fg_top hinj⟩

#print axioms s2e_finite_surjective_affine_sections_finiteType
end HodgeLean.Foundations.Program

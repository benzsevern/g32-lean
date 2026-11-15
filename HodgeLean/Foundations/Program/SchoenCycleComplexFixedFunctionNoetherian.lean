import HodgeLean.Foundations.Program.SchoenCycleFixedFunctionFiniteType
import HodgeLean.Foundations.Program.SchoenCycleComplexAffineFiniteType
import HodgeLean.Foundations.Program.SchoenCycleStep1SectionAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual fixed-function algebra on an affine inverse-image neighbourhood is Noetherian.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 7.8. -/
theorem s2e_complex_fixed_function_noetherian
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (G : Type) [Group G] [Finite G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ g, a g ≫ q = q) (U : Y.left.Opens)
    (hW : IsAffineOpen (q.left ⁻¹ᵁ U)) :
    letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
    IsNoetherianRing (FixedPoints.subalgebra ℂ Γ(X.left, q.left ⁻¹ᵁ U) G) := by
  letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  letI : Algebra.FiniteType ℂ Γ(X.left, q.left ⁻¹ᵁ U) :=
    s2e_complex_affine_sections_finiteType X _ hW
  letI := s2e_fixed_function_finiteType ℂ Γ(X.left, q.left ⁻¹ᵁ U) G
  exact Algebra.FiniteType.isNoetherianRing ℂ _

#print axioms s2e_complex_fixed_function_noetherian
end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenCycleComplexPointStabilizer
import HodgeLean.Foundations.Program.SchoenCycleStep1SectionAction
import Mathlib.RingTheory.Ideal.Pointwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The actual inverse-image section action fixes the affine prime exactly when the corresponding geometric action fixes the complex point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_quotient_point_prime_stabilizer
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] (hinv : ∀ u, a u ≫ q = q)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint X) (hx : x.underlying ∈ q.left ⁻¹ᵁ U) (g : G) :
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    g • ((hU.preimage q.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal =
      ((hU.preimage q.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal ↔
        Point.map (a g) x = x := by
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  let W := q.left ⁻¹ᵁ U
  let I := ((hU.preimage q.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal
  rw [Ideal.pointwise_smul_eq_comap]
  change I.comap ((a ((g⁻¹)⁻¹)).left.appLE W W _).hom = I ↔ Point.map (a g) x = x
  simpa only [inv_inv] using
    (s2e_complex_point_fixed_iff_prime_comap X (a g) W (hU.preimage q.left)
      (s2e_step1_action_preimage X Y q (a g) (hinv g) U) x hx).symm

#print axioms s2e_quotient_point_prime_stabilizer
end HodgeLean.Foundations.Program

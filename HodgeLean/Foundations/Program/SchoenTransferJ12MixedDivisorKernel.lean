import HodgeLean.Foundations.Program.SchoenTransferJ12DivisorCup
import HodgeLean.Foundations.Program.CycleFoundationsPullbackSpan

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Product of the actual mixed divisor kernels attached to the specified source maps.
Source: the group-sum mixed polarization and the ordered cup of its actual pair-map pullbacks. -/
def s4_selected_mixed_divisor_kernel
    (A B : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (n : ℕ) (l : Fin n → (B ⟶ A)) (pol : HQ A 2) : HQ (A ⊗ B) (2 * n) :=
  s4_selected_divisor_cup (A ⊗ B) n (fun i =>
    homPullback (lift (fst A B) (snd A B ≫ l i)) 2 (s4_mixedPolarization A pol))

/-- The specified mixed divisor product is algebraic when its source is also abelian.
Source: abelian morphism pullback of algebraic classes and the actual cycle-class product theorem. -/
theorem s4_selected_mixed_divisor_kernel_mem
    (A B : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (n : ℕ) (l : Fin n → (B ⟶ A)) (pol : HQ A 2) (hpol : pol ∈ cfd_cycleSpan A 1) :
    s4_selected_mixed_divisor_kernel A B n l pol ∈ cfd_cycleSpan (A ⊗ B) n := by
  apply s4_selected_divisor_cup_mem
  intro i
  exact cfd_morphism_pullback_span (A ⊗ A) (A ⊗ B)
    (lift (fst A B) (snd A B ≫ l i)) 1 _ (s4_mixedPolarization_algebraic A pol hpol)

#print axioms s4_selected_mixed_divisor_kernel_mem
end HodgeLean.Foundations.Program

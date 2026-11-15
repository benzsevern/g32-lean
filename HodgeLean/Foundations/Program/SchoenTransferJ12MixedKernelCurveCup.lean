import HodgeLean.Foundations.Program.SchoenTransferJ12PairMixedDivisor

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual mixed kernel is the ordered cup of the mixed divisors of its maps.
Source: pair pullback of the mixed polarization on each specified factor. -/
theorem s4_selected_mixed_kernel_curve_cup
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (n : ℕ) (f : Fin n → (Y ⟶ A)) (pol : HQ A 2) :
    s4_selected_mixed_divisor_kernel A Y n f pol =
      s4_selected_divisor_cup (A ⊗ Y) n
        (fun i => s4_selected_curve_mixed_divisor A Y (f i) pol) := by
  unfold s4_selected_mixed_divisor_kernel
  congr 1
  funext i
  exact s4_selected_pair_mixed_divisor A Y (f i) pol

#print axioms s4_selected_mixed_kernel_curve_cup
end HodgeLean.Foundations.Program

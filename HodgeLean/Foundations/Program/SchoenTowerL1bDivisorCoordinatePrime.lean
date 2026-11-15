import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorInsertion
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductFunction

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every coordinate point ideal is prime on an affine open meeting that coordinate fibre. -/
theorem s2v_l1b_divisor_coordinate_ideal_prime
    (Z : Over (Spec ↧ℂ)) [IsSeparated Z.hom] (n : ℕ)
    [IsIntegral (g3_power Z n).left]
    (b : ComplexPoint Z) (i : Fin (n + 1))
    (U : (g3_power Z (n + 1)).left.affineOpens)
    [Nonempty ((s2c_branchInsertion Z n b ≫
      s2_permute Z (n + 1) (Equiv.swap 0 i)).left ⁻¹ᵁ U.1)] :
    ((b.left.ker.comap (g3_proj Z (n + 1) i).left).ideal U).IsPrime := by
  letI : IsIso (s2_permute Z (n + 1) (Equiv.swap 0 i)) :=
    (s2_permuteIso Z (n + 1) (Equiv.swap 0 i)).isIso_hom
  letI : IsClosedImmersion (s2c_branchInsertion Z n b).left :=
    s2v_l1b_divisor_insertion_closedImmersion Z n b
  rw [← s2v_l1b_divisor_coordinate_insertion_kernel, Scheme.Hom.ker_apply]
  exact RingHom.ker_isPrime _

end HodgeLean.Foundations.Program

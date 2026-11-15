import HodgeLean.Foundations.Program.G32SelectedRealizationSecond

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

theorem s0_part_finrank
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P : g32p_Part J aut S) :
    Module.finrank ℚ (HQ P.P 1) = 2 * P.k * Nat.totient S.m := by
  have hF : Module.finrank ℚ (cyc_Field S.m) = S.m.totient :=
    IsCyclotomicExtension.finrank (cyc_Field S.m)
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos S.m))
  rw [P.act.cyc_coordinates.finrank_eq, Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    hF]

#print axioms s0_part_finrank

end HodgeLean.Foundations.Program

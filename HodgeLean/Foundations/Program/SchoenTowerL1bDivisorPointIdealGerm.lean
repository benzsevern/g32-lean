import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorPointIdeal

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The complex point ideal extends to the maximal ideal of its actual stalk. -/
theorem s2v_l1b_divisor_point_ideal_germ
    (Z : Over (Spec ↧ℂ)) (b : ComplexPoint Z) (U : Z.left.affineOpens)
    (hb : b.underlying ∈ U.1) :
    (b.left.ker.ideal U).map (Z.left.presheaf.germ U.1 b.underlying hb).hom =
      IsLocalRing.maximalIdeal (Z.left.presheaf.stalk b.underlying) := by
  rw [s2v_l1b_divisor_point_ideal_affine]
  let P := (U.2.primeIdealOf ⟨b.underlying, hb⟩).asIdeal
  letI : Algebra Γ(Z.left, U.1) (Z.left.presheaf.stalk b.underlying) :=
    TopCat.Presheaf.algebra_section_stalk Z.left.presheaf ⟨b.underlying, hb⟩
  letI : IsLocalization.AtPrime (Z.left.presheaf.stalk b.underlying) P :=
    U.2.isLocalization_stalk ⟨b.underlying, hb⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal P (Z.left.presheaf.stalk b.underlying)

end HodgeLean.Foundations.Program

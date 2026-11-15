import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIncidencePrime
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorLocalizationPrime

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A nonzero supplied local equation of an incidence ideal is a prime element or a unit. -/
theorem s2v_l1b_divisor_incidence_germ_prime_or_unit
    (Z B : Over (Spec ↧ℂ)) [IsProjective Z.hom] [IsIntegral B.left] (n : ℕ)
    [IsIntegral (g3_power Z n).left]
    (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left]
    (b : ComplexPoint Z) (x : B.left) (U : B.left.affineOpens)
    (hx : x ∈ U.1) (g : Γ(B.left, U))
    (hg : (s2c_branchIdeal Z B n γ b).ideal U = Ideal.span {g})
    (hg0 : (B.left.presheaf.germ U.1 x hx).hom g ≠ 0) :
    IsUnit ((B.left.presheaf.germ U.1 x hx).hom g) ∨
      Prime ((B.left.presheaf.germ U.1 x hx).hom g) := by
  letI : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  obtain htop | hprime := s2v_l1b_divisor_incidence_ideal_top_or_prime Z B n γ b U
  · left
    rw [hg] at htop
    exact (Ideal.span_singleton_eq_top.mp htop).map (B.left.presheaf.germ U.1 x hx).hom
  · have hg' : g ≠ 0 := by
      intro hz
      exact hg0 (by rw [hz, map_zero])
    rw [hg] at hprime
    have hgp : Prime g := (Ideal.span_singleton_prime hg').mp hprime
    letI : Algebra Γ(B.left, U) (B.left.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk B.left.presheaf ⟨x, hx⟩
    let P := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal
    letI : P.IsPrime := inferInstanceAs (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.IsPrime
    letI : IsLocalization.AtPrime (B.left.presheaf.stalk x) P := U.2.isLocalization_stalk ⟨x, hx⟩
    exact s2v_l1b_divisor_localization_prime_or_unit P.primeCompl
      (germ_injective_of_isIntegral B.left x hx) g hgp

end HodgeLean.Foundations.Program

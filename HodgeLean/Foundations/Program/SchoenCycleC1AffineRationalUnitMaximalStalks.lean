import HodgeLean.Foundations.Program.SchoenCycleC1AffineRationalMaximalStalks

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual rational units in every maximal affine stalk give one unit on
the entire original affine chart, retaining its rational value. -/
theorem s2e_c1_affine_rational_unit_of_maximal_stalks
    (X : Scheme) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (t : X.functionField) (ht : t ≠ 0)
    (hlocal : ∀ P : PrimeSpectrum Γ(X, U), P.asIdeal.IsMaximal →
      ∃ u : (X.presheaf.stalk (hU.fromSpec P))ˣ,
        algebraMap (X.presheaf.stalk (hU.fromSpec P)) X.functionField (u : _) = t) :
    ∃ u : Γ(X, U)ˣ, X.germToFunctionField U (u : Γ(X, U)) = t := by
  obtain ⟨a, ha⟩ := s2e_c1_affine_rational_of_maximal_stalks X U hU t (by
    intro P hP
    obtain ⟨u, hu⟩ := hlocal P hP
    exact ⟨u, hu⟩)
  obtain ⟨b, hb⟩ := s2e_c1_affine_rational_of_maximal_stalks X U hU t⁻¹ (by
    intro P hP
    obtain ⟨u, hu⟩ := hlocal P hP
    exact ⟨(u⁻¹ : (X.presheaf.stalk (hU.fromSpec P))ˣ), by rw [map_units_inv, hu]⟩)
  have hab : a * b = 1 := by
    apply X.germToFunctionField_injective U
    rw [map_mul, ha, hb, mul_inv_cancel₀ ht, map_one]
  have hau : IsUnit a := isUnit_iff_exists_inv.mpr ⟨b, hab⟩
  obtain ⟨u, hu⟩ := hau
  exact ⟨u, by rw [hu]; exact ha⟩

end HodgeLean.Foundations.Program

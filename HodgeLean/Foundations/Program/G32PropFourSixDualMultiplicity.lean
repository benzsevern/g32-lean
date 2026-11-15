import HodgeLean.Foundations.Program.G32PropFourSixUnitary

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

theorem g32p_inverse_rank {G : Type} [Group G] (V : FDRep ℂ G) (g : G) :
    Module.finrank ℂ (LinearMap.range (V.ρ g⁻¹ - 1)) =
      Module.finrank ℂ (LinearMap.range (V.ρ g - 1)) := by
  have hi (x : V) : V.ρ g (V.ρ g⁻¹ x) = x := by
    change (V.ρ g * V.ρ g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hj (x : V) : V.ρ g⁻¹ (V.ρ g x) = x := by
    change (V.ρ g⁻¹ * V.ρ g) x = x
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have hk : LinearMap.ker (V.ρ g⁻¹ - 1) = LinearMap.ker (V.ρ g - 1) := by
    ext x
    change V.ρ g⁻¹ x - x = 0 ↔ V.ρ g x - x = 0
    constructor
    · intro h
      apply sub_eq_zero.mpr
      have he := congrArg (V.ρ g) (sub_eq_zero.mp h)
      rw [hi] at he
      exact he.symm
    · intro h
      apply sub_eq_zero.mpr
      have he := congrArg (V.ρ g⁻¹) (sub_eq_zero.mp h)
      rw [hj] at he
      exact he.symm
  have h1 := LinearMap.finrank_range_add_finrank_ker (V.ρ g⁻¹ - 1)
  have h2 := LinearMap.finrank_range_add_finrank_ker (V.ρ g - 1)
  rw [hk] at h1
  omega

theorem g32p_dual_rank {G : Type} [Group G] (V : FDRep ℂ G) (g : G) :
    Module.finrank ℂ (LinearMap.range ((FDRep.of (Representation.dual V.ρ)).ρ g - 1)) =
      Module.finrank ℂ (LinearMap.range (V.ρ g - 1)) := by
  have he : (FDRep.of (Representation.dual V.ρ)).ρ g - 1 =
      (V.ρ g⁻¹ - 1).dualMap := by
    ext f x
    change f (V.ρ g⁻¹ x) - f x = f (V.ρ g⁻¹ x - x)
    exact (map_sub f _ _).symm
  rw [he, LinearMap.finrank_range_dualMap_eq_finrank_range, g32p_inverse_rank]

theorem g32p_dual_cwMult (V : FDRep ℂ g32p_G) :
    g32p_cwMult (FDRep.of (Representation.dual V.ρ)) = g32p_cwMult V := by
  unfold g32p_cwMult
  have hd : Module.finrank ℂ (FDRep.of (Representation.dual V.ρ)) =
      Module.finrank ℂ V := Subspace.dual_finrank_eq
  rw [hd]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun n : ℕ => (n : ℤ)) (g32p_dual_rank V (g32p_classDatum j))

theorem g32p_rhoDual_cwMult : g32p_cwMult g32p_rhoDual = 6 :=
  (g32p_dual_cwMult g32p_rho).trans g32p_rho_cwMult

end HodgeLean.Foundations.Program

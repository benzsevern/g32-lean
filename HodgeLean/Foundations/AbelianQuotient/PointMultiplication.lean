import HodgeLean.Foundations.AbelianQuotient.IntegralInverse

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- Positive integer powers are surjective on the complex points of an abelian variety. -/
theorem surjective_pow_points (A : Variety) (N : ℕ) (hN : 0 < N) :
    Function.Surjective (fun a : ComplexPoint A.X => a ^ N) := by
  intro a
  obtain ⟨v, hv⟩ := surjective_complexExponential A.X (dim A.X.left) (Additive.ofMul a)
  let w := (N : ℂ)⁻¹ • v
  have hw : N • w = v := by
    dsimp only [w]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      mul_inv_cancel₀ (show (N : ℂ) ≠ 0 by exact_mod_cast hN.ne'), one_smul]
  refine ⟨Additive.toMul (complexExponential A.X (dim A.X.left) w), ?_⟩
  have hexp := congrArg Additive.toMul
    ((complexExponentialHom A.X (dim A.X.left)).map_nsmul N w)
  change Additive.toMul (complexExponential A.X (dim A.X.left) (N • w)) =
    Additive.toMul (complexExponential A.X (dim A.X.left) w) ^ N at hexp
  change Additive.toMul (complexExponential A.X (dim A.X.left) w) ^ N = a
  rw [← hexp, hw, hv]
  rfl

/-- A positive power cannot annihilate a nontrivial homomorphism from an abelian variety. -/
theorem hom_eq_one_of_pow_eq_one {A B : Variety} (f : Hom A B) (N : ℕ) (hN : 0 < N)
    (h : f.hom ^ (N : ℤ) = (1 : A.X ⟶ B.X)) : f.hom = 1 := by
  apply abq_over_hom_ext_of_point_map
  funext s
  obtain ⟨t, ht⟩ := surjective_pow_points A N hN s
  change s ≫ f.hom = s ≫ (1 : A.X ⟶ B.X)
  rw [MonObj.comp_one, ← ht, MonObj.pow_comp]
  have hp := congrArg (fun k : A.X ⟶ B.X => t ≫ k) h
  rw [GrpObj.comp_zpow, zpow_natCast, MonObj.comp_one] at hp
  exact hp

end HodgeLean.Foundations.AbelianQuotient

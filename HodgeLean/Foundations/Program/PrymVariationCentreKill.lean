import HodgeLean.Foundations.Program.PrymVariationCentreAverage

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

section Rep
variable {U : Type} [AddCommGroup U] [Module ℂ U]
  (ρ : Representation ℂ b4b_Group U) (l : U →ₗ[ℂ] ℂ) (v : U)

theorem b63d_average_natural_coordinate :
    (b63d_averageHom ρ b63d_naturalRep (l.smulRight (Pi.single 0 1)) v) 0 =
      ∑ g : b4b_Group, b4b_toMatrix g⁻¹ 0 0 * l (ρ g v) := by
  rw [b63d_averageHom_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro g hg
  rw [LinearMap.smulRight_apply, map_smul]
  change l (ρ g v) * (Matrix.toLin' (b4b_toMatrix g⁻¹) (Pi.single 0 1)) 0 = _
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  exact mul_comm _ _

theorem b63d_average_conjugate_coordinate :
    b63d_barCoordinate (b63d_averageHom ρ (HurwitzPrymRex_barRep b63d_naturalRep)
      (l.smulRight (HurwitzPrymRex_Bar.of (Pi.single 0 1))) v) =
      ∑ g : b4b_Group, star (b4b_toMatrix g⁻¹ 0 0) * l (ρ g v) := by
  rw [b63d_averageHom_apply, map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [LinearMap.smulRight_apply, map_smul, map_smul]
  change l (ρ g v) * star ((Matrix.toLin' (b4b_toMatrix g⁻¹) (Pi.single 0 1)) 0) = _
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  exact mul_comm _ _

end Rep

theorem b63d_projector_kills {U : Type} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ b4b_Group U)
    (hn : ∀ φ : Representation.IntertwiningMap ρ b63d_naturalRep, φ = 0)
    (hb : ∀ φ : Representation.IntertwiningMap ρ (HurwitzPrymRex_barRep b63d_naturalRep), φ = 0) :
    (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • ρ g) = 0 := by
  apply LinearMap.ext
  intro v
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro l
  have h1 : (∑ g : b4b_Group, b4b_toMatrix g⁻¹ 0 0 * l (ρ g v)) = 0 := by
    rw [← b63d_average_natural_coordinate]
    rw [hn (b63d_averageHom ρ b63d_naturalRep (l.smulRight (Pi.single 0 1)))]
    rfl
  have h2 : (∑ g : b4b_Group, star (b4b_toMatrix g⁻¹ 0 0) * l (ρ g v)) = 0 := by
    rw [← b63d_average_conjugate_coordinate]
    rw [hb (b63d_averageHom ρ (HurwitzPrymRex_barRep b63d_naturalRep)
      (l.smulRight (HurwitzPrymRex_Bar.of (Pi.single 0 1))))]
    exact map_zero _
  change l ((∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • ρ g) v) = 0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  calc
    (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) * l (ρ g v)) =
        3 * ((∑ g : b4b_Group, b4b_toMatrix g⁻¹ 0 0 * l (ρ g v)) +
          (∑ g : b4b_Group, star (b4b_toMatrix g⁻¹ 0 0) * l (ρ g v))) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      rw [b63d_projectorCoeff_complex]
      ring
    _ = 0 := by rw [h1, h2]; ring

end HodgeLean.Foundations.Program

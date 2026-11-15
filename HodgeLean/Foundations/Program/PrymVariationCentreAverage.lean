import HodgeLean.Foundations.Program.PrymVariationCentreDistinct
import HodgeLean.Foundations.Program.PrymVariationCentreConjugateProjector

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- The unnormalized averaging map between two representations.
Source: Serre, Linear Representations of Finite Groups, §2.2. -/
def b63d_averageHom {G U W : Type} [Group G] [Fintype G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G U) (σ : Representation ℂ G W) (f : U →ₗ[ℂ] W) :
    Representation.IntertwiningMap ρ σ where
  toLinearMap := ∑ g : G, (σ g⁻¹).comp (f.comp (ρ g))
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    have hcancel (w : W) : σ h (σ h⁻¹ w) = w := by
      change (σ h * σ h⁻¹) w = w
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g ↦ ?_
    simp only [Equiv.coe_mulRight, mul_inv_rev, map_mul, Module.End.mul_apply]
    exact (hcancel _).symm

example {G U W : Type} [Group G] [Fintype G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G U) (σ : Representation ℂ G W) (f : U →ₗ[ℂ] W) (v : U) :
    b63d_averageHom ρ σ f v = ∑ g : G, σ g⁻¹ (f (ρ g v)) := by
  simp only [b63d_averageHom, Representation.IntertwiningMap.coe_mk,
    LinearMap.sum_apply, LinearMap.comp_apply]

theorem b63d_averageHom_apply {G U W : Type} [Group G] [Fintype G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G U) (σ : Representation ℂ G W) (f : U →ₗ[ℂ] W) (v : U) :
    b63d_averageHom ρ σ f v = ∑ g : G, σ g⁻¹ (f (ρ g v)) := by
  simp only [b63d_averageHom, Representation.IntertwiningMap.coe_mk,
    LinearMap.sum_apply, LinearMap.comp_apply]

theorem b63d_projectorCoeff_complex (g : b4b_Group) :
    (b4b_projectorCoeff g : ℂ) =
      3 * (b4b_toMatrix g⁻¹ 0 0 + star (b4b_toMatrix g⁻¹ 0 0)) := by
  apply Complex.ext
  · norm_num [Complex.mul_re, Complex.add_re, Complex.conj_re, Complex.star_def]
    linear_combination b63l_projectorCoeff_cast g
  · simp [Complex.mul_im, Complex.add_im, Complex.conj_im, Complex.star_def]

/-- The linear first coordinate on the conjugate column space.
Source: Fulton-Harris, Representation Theory, §3.5. -/
def b63d_barCoordinate : HurwitzPrymRex_Bar (Fin 4 → ℂ) →ₗ[ℂ] ℂ where
  toFun v := star (v.val 0)
  map_add' u v := by simp only [HurwitzPrymRex_Bar.val_add, Pi.add_apply, star_add]
  map_smul' c v := by
    change star (star c * v.val 0) = c * star (v.val 0)
    rw [star_mul, star_star, mul_comm]

example (v : HurwitzPrymRex_Bar (Fin 4 → ℂ)) :
    b63d_barCoordinate v = star (v.val 0) := rfl

end HodgeLean.Foundations.Program

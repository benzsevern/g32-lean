import HodgeLean.Foundations.Program.PrymVariationCentreIrreducible

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b63d_omega_ne_star : g32h_omega ≠ star g32h_omega := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  have hi0 : g32h_omega.im = 0 := by linarith
  have hr := congrArg Complex.re g32h_omega_sq_add
  rw [pow_two] at hr
  simp only [Complex.add_re, Complex.mul_re, Complex.one_re, Complex.zero_re, hi0,
    mul_zero, sub_zero] at hr
  nlinarith [sq_nonneg (g32h_omega.re + 1 / 2)]

theorem b63d_intertwiner_zero_of_scalars {G U W : Type} [Group G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G U) (σ : Representation ℂ G W)
    (g : G) (a b : ℂ) (hab : a ≠ b)
    (hρ : ∀ v, ρ g v = a • v) (hσ : ∀ v, σ g v = b • v)
    (φ : Representation.IntertwiningMap ρ σ) : φ = 0 := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have he : φ (ρ g v) = σ g (φ v) :=
    congrArg (fun f : U →ₗ[ℂ] W ↦ f v) (φ.isIntertwining' g)
  rw [hρ, hσ, map_smul] at he
  have hz : (a - b) • φ v = 0 := by rw [sub_smul, he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab)

theorem b63d_natural_conjugate_intertwiner_zero
    (φ : Representation.IntertwiningMap b63d_naturalRep
      (HurwitzPrymRex_barRep b63d_naturalRep)) : φ = 0 :=
  b63d_intertwiner_zero_of_scalars _ _ b63d_scalarElement _ _ b63d_omega_ne_star
    b63d_naturalRep_scalar b63d_conjugateRep_scalar φ

theorem b63d_conjugate_natural_intertwiner_zero
    (φ : Representation.IntertwiningMap (HurwitzPrymRex_barRep b63d_naturalRep)
      b63d_naturalRep) : φ = 0 :=
  b63d_intertwiner_zero_of_scalars _ _ b63d_scalarElement _ _ b63d_omega_ne_star.symm
    b63d_conjugateRep_scalar b63d_naturalRep_scalar φ

end HodgeLean.Foundations.Program

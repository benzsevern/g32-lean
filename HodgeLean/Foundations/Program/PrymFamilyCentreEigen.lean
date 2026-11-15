import HodgeLean.Foundations.Program.PrymFamilyCentreNaturality

/-! # B6-3g, parts 2 and 3: eigenparts through an integral comparison

An integral isomorphism that intertwines `c` with an ambient operator `Z` identifies the
`1 + 2z` eigenpart of `1 + 2c` inside a pulled-back filtration with the `z` eigenpart of `Z`,
when the ambient inclusion stays injective after `ℂ ⊗`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open HodgeLean.Papers
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

/-- **Eigenparts through an integral comparison.**
Source: Bourbaki, *Algebra*, Ch. II, §5 (extension of scalars); Birkenhake–Lange, §1.2. -/
theorem b63g2_eigen_transfer {Λ K A : Type*} [AddCommGroup Λ] [AddCommGroup K]
    [AddCommGroup A] (E : Λ ≃ₗ[ℤ] K) (ι : K →ₗ[ℤ] A)
    (hι : Function.Injective (ι.baseChange ℂ)) (c J : Λ →ₗ[ℤ] Λ) (Z : A →ₗ[ℤ] A)
    (hJ : J = LinearMap.id + c + c) (hc : ∀ x, ι (E (c x)) = Z (ι (E x)))
    (FA : Submodule ℂ (ℂ ⊗[ℤ] A)) (z μ : ℂ) (hμ : 1 + 2 * z = μ) :
    Module.finrank ℂ ↥((FA.comap (ι.baseChange ℂ)).comap
        ((E : Λ →ₗ[ℤ] K).baseChange ℂ) ⊓ Module.End.eigenspace (J.baseChange ℂ) μ) =
      Module.finrank ℂ ↥(FA.comap (ι.baseChange ℂ) ⊓
        (LinearMap.ker (Z.baseChange ℂ - z • LinearMap.id)).comap (ι.baseChange ℂ)) := by
  subst hμ
  set e : (ℂ ⊗[ℤ] Λ) ≃ₗ[ℂ] (ℂ ⊗[ℤ] K) := E.baseChange ℤ ℂ Λ K
  have he : ∀ v, e v = (E : Λ →ₗ[ℤ] K).baseChange ℂ v := fun _ ↦ rfl
  have hcomp : (ι.comp (E : Λ →ₗ[ℤ] K)).comp c = Z.comp (ι.comp (E : Λ →ₗ[ℤ] K)) :=
    LinearMap.ext hc
  have hcompC : ∀ v, ι.baseChange ℂ ((E : Λ →ₗ[ℤ] K).baseChange ℂ (c.baseChange ℂ v)) =
      Z.baseChange ℂ (ι.baseChange ℂ ((E : Λ →ₗ[ℤ] K).baseChange ℂ v)) := by
    intro v
    have h := congrArg (LinearMap.baseChange ℂ) hcomp
    simp only [LinearMap.baseChange_comp] at h
    exact LinearMap.congr_fun h v
  have hinj : Function.Injective (fun v ↦ ι.baseChange ℂ ((E : Λ →ₗ[ℤ] K).baseChange ℂ v)) :=
    hι.comp (show Function.Injective ((E : Λ →ₗ[ℤ] K).baseChange ℂ) from e.injective)
  have hS : (FA.comap (ι.baseChange ℂ)).comap ((E : Λ →ₗ[ℤ] K).baseChange ℂ) ⊓
      Module.End.eigenspace (J.baseChange ℂ) (1 + 2 * z) =
      (FA.comap (ι.baseChange ℂ) ⊓
        (LinearMap.ker (Z.baseChange ℂ - z • LinearMap.id)).comap (ι.baseChange ℂ)).comap
          (e : (ℂ ⊗[ℤ] Λ) →ₗ[ℂ] (ℂ ⊗[ℤ] K)) := by
    ext v
    simp only [Submodule.mem_inf, Submodule.mem_comap, Module.End.mem_eigenspace_iff,
      LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, he]
    refine and_congr Iff.rfl ?_
    rw [← hcompC, ← map_smul, ← map_smul, ← map_sub, ← map_sub, hJ]
    simp only [LinearMap.baseChange_add, LinearMap.baseChange_id, LinearMap.add_apply,
      LinearMap.id_apply]
    constructor
    · intro h
      have h2 : (2 : ℂ) • (c.baseChange ℂ v - z • v) = 0 := by
        rw [smul_sub, smul_smul, two_smul, add_smul, one_smul] at *
        linear_combination (norm := module) h
      have h3 : c.baseChange ℂ v - z • v = 0 :=
        (smul_eq_zero.mp h2).resolve_left two_ne_zero
      rw [h3, map_zero, map_zero]
    · intro h
      have h3 : c.baseChange ℂ v - z • v = 0 := by
        apply hinj
        simpa using h
      have h4 : c.baseChange ℂ v = z • v := sub_eq_zero.mp h3
      rw [h4, add_smul, one_smul, mul_smul, two_smul]
      abel
  rw [hS, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

/-- `1 + 2ω = i√3`.
Source: `g32h_omega = exp(2πi/3) = (−1 + i√3)/2`. -/
theorem b63g2_one_add_two_omega :
    1 + 2 * g32h_omega = HodgeBlocks.WeilAction.omegaC 3 := by
  have harg : 2 * Real.pi * Complex.I / 3 = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hθ : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [g32h_omega, harg, HodgeBlocks.WeilAction.omegaC]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    rw [hθ, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  · simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    rw [hθ, Real.sin_pi_sub, Real.sin_pi_div_three]
    norm_num
    ring

/-- `1 + 2ω̄ = -i√3`.
Source: complex conjugate of `b63g2_one_add_two_omega`. -/
theorem b63g2_one_add_two_star_omega :
    1 + 2 * star g32h_omega = -HodgeBlocks.WeilAction.omegaC 3 := by
  have h := congrArg star b63g2_one_add_two_omega
  simp only [star_add, star_one, star_mul', HodgeBlocks.WeilAction.omegaC] at h ⊢
  rw [show star (2 : ℂ) = 2 from Complex.conj_ofNat 2] at h
  rw [h]
  simp [Complex.conj_ofReal]

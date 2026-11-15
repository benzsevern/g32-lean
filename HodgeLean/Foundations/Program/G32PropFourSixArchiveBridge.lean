import HodgeLean.Foundations.Program.G32PropFourSixDefs

noncomputable section

open HodgeLean.Papers

namespace HodgeLean.Foundations.Program

def g32p_archiveFirstGenerator : Matrix (Fin 4) (Fin 4) ℂ :=
  let w := g32h_omega
  !![(w + 2) / 3, (2 * w + 1) / 3, -(2 * w + 1) / 3, 0;
     -(w + 2) / 3, (w + 2) / 3, (1 - w) / 3, 0;
     (w + 2) / 3, (1 - w) / 3, (w + 2) / 3, 0;
     0, 0, 0, 1]

theorem g32p_nonintegral_entry (a b : ℤ) :
    (a : ℂ) + (b : ℂ) * g32h_omega ≠ (g32h_omega + 2) / 3 := by
  intro hh
  have hi := congrArg Complex.im hh
  simp [Complex.mul_im] at hi
  have hb : (((3 * b - 1 : ℤ) : ℝ)) * g32h_omega.im = 0 := by
    push_cast
    linear_combination 3 * hi
  have hb0 : ((3 * b - 1 : ℤ) : ℝ) = 0 :=
    (mul_eq_zero.mp hb).resolve_right (omega_im_ne_zero g32h_omega g32h_omega_sq_add)
  have hbZ : 3 * b - 1 = 0 := by exact_mod_cast hb0
  omega

theorem g32p_archiveFirstGenerator_entry :
    (HurwitzPrymRex_g32Pinv * g32p_archiveFirstGenerator * HurwitzPrymRex_g32P) 0 0 =
      (g32h_omega + 2) / 3 := by
  norm_num [HurwitzPrymRex_g32Pinv, HurwitzPrymRex_g32P, g32p_archiveFirstGenerator,
    Matrix.mul_apply, Fin.sum_univ_four]
  papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add

theorem g32p_archiveFirstGenerator_not_integralConjugate (C : HurwitzPrymRex_Mat) :
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega C) ≠
      g32p_archiveFirstGenerator := by
  intro hh
  have hi := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ =>
    HurwitzPrymRex_g32Pinv * M * HurwitzPrymRex_g32P) hh
  have hcancel (M : Matrix (Fin 4) (Fin 4) ℂ) :
      HurwitzPrymRex_g32Pinv * HurwitzPrymRex_g32conj M * HurwitzPrymRex_g32P = M := by
    change HurwitzPrymRex_g32Pinv *
      (HurwitzPrymRex_g32P * M * HurwitzPrymRex_g32Pinv) * HurwitzPrymRex_g32P = M
    rw [show HurwitzPrymRex_g32Pinv *
      (HurwitzPrymRex_g32P * M * HurwitzPrymRex_g32Pinv) * HurwitzPrymRex_g32P =
      (HurwitzPrymRex_g32Pinv * HurwitzPrymRex_g32P) * M *
        (HurwitzPrymRex_g32Pinv * HurwitzPrymRex_g32P) by noncomm_ring,
      HurwitzPrymRex_g32_Pinv_P, one_mul, mul_one]
  rw [hcancel] at hi
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) hi
  rw [g32p_archiveFirstGenerator_entry] at he
  exact g32p_nonintegral_entry (C 0 0).re (C 0 0).om he

theorem g32p_integralClosure (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hM : M ∈ Submonoid.closure (HurwitzPrymRex_img g32h_omega HurwitzPrymRex_g32SOne)) :
    ∃ C : HurwitzPrymRex_Mat, HurwitzPrymRex_evM g32h_omega C = M := by
  induction hM using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨C, _, rfl⟩ := hx
      exact ⟨C, rfl⟩
  | one => exact ⟨HurwitzPrymRex_mone, HurwitzPrymRex_evM_mone⟩
  | mul x y _ _ hx hy =>
      obtain ⟨C, rfl⟩ := hx
      obtain ⟨D, rfl⟩ := hy
      exact ⟨HurwitzPrymRex_mmul C D, HurwitzPrymRex_evM_mmul g32h_omega_sq_add C D⟩

theorem g32p_archiveFirstGenerator_not_mem : g32p_archiveFirstGenerator ∉ g32h_G := by
  intro hh
  rw [HurwitzPrymRex_g32_G_eq] at hh
  obtain ⟨M, hM, he⟩ := hh
  obtain ⟨C, rfl⟩ := g32p_integralClosure M hM
  exact g32p_archiveFirstGenerator_not_integralConjugate C he

end HodgeLean.Foundations.Program

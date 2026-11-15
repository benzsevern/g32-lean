import HodgeLean.Foundations.Program.G32PropFourSixCommutant

noncomputable section

open HodgeLean.Papers CategoryTheory

namespace HodgeLean.Foundations.Program

theorem g32p_rho_character (g : g32p_G) :
    g32p_rho.character g = Matrix.trace (b4b_toMatrix g) := by
  change LinearMap.trace ℂ (Fin 4 → ℂ) (Matrix.toLin' (b4b_toMatrix g)) = _
  exact Matrix.trace_toLin'_eq _

theorem g32p_rho_character_reflection :
    g32p_rho.character (g32p_classDatum 0) = 3 + g32h_omega := by
  rw [g32p_rho_character]
  change Matrix.trace (g32R1 g32h_omega) = _
  norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_four, g32R1]
  ring

theorem g32p_rho_not_selfDual : ¬ g32p_SelfDual g32p_rho := by
  intro h
  have hh := h (g32p_classDatum 0)
  rw [g32p_rho_character_reflection] at hh
  have hi := congrArg Complex.im hh
  simp [Complex.add_im, Complex.conj_im] at hi
  exact omega_im_ne_zero g32h_omega g32h_omega_sq_add (by linarith)

theorem g32p_rho_end_scalar (f : g32p_rho ⟶ g32p_rho) :
    ∃ c : ℂ, f = c • 𝟙 g32p_rho := by
  let L : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) := f.hom.hom.hom
  let E := (Matrix.toLinAlgEquiv' : Matrix (Fin 4) (Fin 4) ℂ ≃ₐ[ℂ] _)
  let M := E.symm L
  have hc (g : g32p_G) : L * Matrix.toLin' (b4b_toMatrix g) = Matrix.toLin' (b4b_toMatrix g) * L := by
    exact congrArg (fun u => u.hom.hom) (f.comm g)
  have hm : M = M 3 3 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    apply g32p_matrix_commutant g32h_omega g32h_omega_sq_add
    · apply E.injective
      simp only [map_mul, M, AlgEquiv.apply_symm_apply]
      change L * Matrix.toLin' (g32R1 g32h_omega) = Matrix.toLin' (g32R1 g32h_omega) * L
      exact hc (b4b_generators 0)
    · apply E.injective
      simp only [map_mul, M, AlgEquiv.apply_symm_apply]
      change L * Matrix.toLin' (g32R2 g32h_omega) = Matrix.toLin' (g32R2 g32h_omega) * L
      exact hc (b4b_generators 1)
    · apply E.injective
      simp only [map_mul, M, AlgEquiv.apply_symm_apply]
      change L * Matrix.toLin' (g32X g32h_omega) = Matrix.toLin' (g32X g32h_omega) * L
      exact hc (b4b_generators 2)
  refine ⟨M 3 3, ?_⟩
  have hl := congrArg E hm
  simp only [map_smul, map_one, M, AlgEquiv.apply_symm_apply] at hl
  ext v
  change L v = (M 3 3 • (1 : Module.End ℂ (Fin 4 → ℂ))) v
  exact LinearMap.congr_fun hl v

theorem g32p_rho_simple : Simple g32p_rho := by
  apply (FDRep.simple_iff_end_is_rank_one g32p_rho).mpr
  have hid : (𝟙 g32p_rho : g32p_rho ⟶ g32p_rho) ≠ 0 := by
    intro hh
    have he := congrArg (fun f : g32p_rho ⟶ g32p_rho =>
      f.hom.hom.hom (fun _ => 1) 0) hh
    exact one_ne_zero he
  apply (finrank_eq_one_iff_of_nonzero' (𝟙 g32p_rho) hid).mpr
  intro f
  obtain ⟨c, hc⟩ := g32p_rho_end_scalar f
  exact ⟨c, hc.symm⟩

theorem g32p_rho_cwMult : g32p_cwMult g32p_rho = 6 := by
  have h := g32h_multCW_classRep g32h_omega g32h_omega_sq_add
  unfold g32h_multCW at h
  unfold g32p_cwMult
  have hd : Module.finrank ℂ g32p_rho = 4 := by
    change Module.finrank ℂ (Fin 4 → ℂ) = 4
    simp
  have key : ∀ M : Matrix (Fin 4) (Fin 4) ℂ,
      Module.finrank ℂ (LinearMap.range (Matrix.toLin' M - 1)) = (M - 1).rank := by
    intro M
    have hM : Matrix.toLin' M - 1 = Matrix.toLin' (M - 1) := by
      rw [map_sub, Matrix.toLin'_one, Module.End.one_eq_id]
    rw [hM]
    rfl
  have hr : ∀ j, Module.finrank ℂ (LinearMap.range (g32p_rho.ρ (g32p_classDatum j) - 1)) =
      (g32h_classRep g32h_omega j - 1).rank := fun j => key _
  rw [hd]
  simp only [hr]
  push_cast
  linarith

end HodgeLean.Foundations.Program

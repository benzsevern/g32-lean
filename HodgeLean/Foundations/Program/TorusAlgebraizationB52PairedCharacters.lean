import HodgeLean.Foundations.Program.TorusAlgebraizationB52CharacterProjection

noncomputable section
namespace HodgeLean.Foundations.Program

variable {G : Type*} [AddCommGroup G] [Fintype G]
    {U V W : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : G →+ Additive (Module.End ℂ U)) (σ : G →+ Additive (Module.End ℂ V))
    (τ : G →+ Additive (Module.End ℂ W)) (B : U →ₗ[ℂ] V →ₗ[ℂ] W)

theorem b52_average_bilinear_eigen_zero
    (hB : ∀ g u v, (τ g).toMul (B u v) = B ((ρ g).toMul u) ((σ g).toMul v))
    (g : G) (u : U) (v : V) (a b : ℂ)
    (hab : a * b ≠ 1) (hu : (ρ g).toMul u = a • u) (hv : (σ g).toMul v = b • v) :
    b52_averageEnd τ (B u v) = 0 := by
  apply b52_averageEnd_eq_zero_of_eigen τ g (B u v) (a * b) hab
  rw [hB, hu, hv]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm]

theorem b52_average_bilinear_character_zero
    (hB : ∀ g u v, (τ g).toMul (B u v) = B ((ρ g).toMul u) ((σ g).toMul v))
    (χ ψ : AddChar G ℂ) (hχψ : χ + ψ ≠ 0) (u : U) (v : V) :
    b52_averageEnd τ (B (b52_characterProjection ρ χ u)
      (b52_characterProjection σ ψ v)) = 0 := by
  obtain ⟨g, hg⟩ := AddChar.ne_zero_iff.mp hχψ
  have hab : (χ g)⁻¹ * (ψ g)⁻¹ ≠ 1 := by
    rw [← mul_inv]
    exact inv_ne_one.mpr hg
  apply b52_average_bilinear_eigen_zero ρ σ τ B hB g _ _ _ _ hab
  · exact (b52_characterProjection_range ρ χ _).mp ⟨u, rfl⟩ g
  · exact (b52_characterProjection_range σ ψ _).mp ⟨v, rfl⟩ g

theorem b52_average_bilinear_paired_characters
    (hB : ∀ g u v, (τ g).toMul (B u v) = B ((ρ g).toMul u) ((σ g).toMul v))
    (u : U) (v : V) :
    b52_averageEnd τ (B u v) =
      ∑ χ : AddChar G ℂ, b52_averageEnd τ
        (B (b52_characterProjection ρ χ u) (b52_characterProjection σ (-χ) v)) := by
  classical
  have hu : (∑ χ : AddChar G ℂ, b52_characterProjection ρ χ u) = u := by
    rw [← LinearMap.sum_apply, b52_sum_characterProjection]
    rfl
  have hv : (∑ ψ : AddChar G ℂ, b52_characterProjection σ ψ v) = v := by
    rw [← LinearMap.sum_apply, b52_sum_characterProjection]
    rfl
  calc
    _ = b52_averageEnd τ (B (∑ χ : AddChar G ℂ, b52_characterProjection ρ χ u)
        (∑ ψ : AddChar G ℂ, b52_characterProjection σ ψ v)) := by rw [hu, hv]
    _ = ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ, b52_averageEnd τ
        (B (b52_characterProjection ρ χ u) (b52_characterProjection σ ψ v)) := by
      simp only [map_sum, LinearMap.sum_apply]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_eq_single (-χ)
      · intro ψ _ hneq
        apply b52_average_bilinear_character_zero ρ σ τ B hB χ ψ
        intro heq
        apply hneq
        apply add_left_cancel (a := χ)
        simpa only [add_neg_cancel] using heq
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim

theorem b52_average_bilinear_paired_fixed
    (hB : ∀ g u v, (τ g).toMul (B u v) = B ((ρ g).toMul u) ((σ g).toMul v))
    (χ : AddChar G ℂ) (u : U) (v : V) :
    b52_averageEnd τ (B (b52_characterProjection ρ χ u)
      (b52_characterProjection σ (-χ) v)) =
    B (b52_characterProjection ρ χ u) (b52_characterProjection σ (-χ) v) := by
  apply b52_averageEnd_apply_of_fixed
  intro g
  have hχ : χ g ≠ 0 := by
    intro hg
    have hh := χ.map_add_eq_mul g (-g)
    simp [hg] at hh
  rw [hB, (b52_characterProjection_range ρ χ _).mp ⟨u, rfl⟩ g,
    (b52_characterProjection_range σ (-χ) _).mp ⟨v, rfl⟩ g]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, AddChar.neg_apply',
    inv_inv, mul_inv_cancel₀ hχ, one_smul]

theorem b52_average_bilinear_character_formula
    (hB : ∀ g u v, (τ g).toMul (B u v) = B ((ρ g).toMul u) ((σ g).toMul v))
    (u : U) (v : V) :
    b52_averageEnd τ (B u v) = ∑ χ : AddChar G ℂ,
      B (b52_characterProjection ρ χ u) (b52_characterProjection σ (-χ) v) := by
  rw [b52_average_bilinear_paired_characters ρ σ τ B hB]
  apply Finset.sum_congr rfl
  intro χ _
  exact b52_average_bilinear_paired_fixed ρ σ τ B hB χ u v

end HodgeLean.Foundations.Program

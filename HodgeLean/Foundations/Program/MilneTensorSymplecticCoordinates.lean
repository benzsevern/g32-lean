import HodgeLean.Foundations.Program.MilneTensorSymplecticSplit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*}

def m1b_symplecticComplementForm (k : ℕ) (e : ι ≃ Fin k ⊕ Fin k) :
    LinearMap.BilinForm ℂ (ι → ℂ) :=
  (m1b_J k).toBilin'.compl₁₂ (LinearEquiv.funCongrLeft ℂ ℂ e).symm.toLinearMap
    (LinearEquiv.funCongrLeft ℂ ℂ e).symm.toLinearMap

def m1b_symplecticSplitReindex (k : ℕ) (e : ι ≃ Fin k ⊕ Fin k) :
    (Fin (k + 1) ⊕ Fin (k + 1)) ≃ (Fin 2 ⊕ ι) :=
  (m1b_symplecticSplitIndex k).trans (Equiv.sumCongr (Equiv.refl _) e.symm)

theorem m1b_symplectic_split_reindexed_form (k : ℕ) (e : ι ≃ Fin k ⊕ Fin k) :
    ((m1b_prodBilin m1b_pairForm (m1b_symplecticComplementForm k e)).compl₁₂
      (LinearEquiv.sumArrowLequivProdArrow (Fin 2) ι ℂ ℂ).toLinearMap
      (LinearEquiv.sumArrowLequivProdArrow (Fin 2) ι ℂ ℂ).toLinearMap).compl₁₂
      (LinearEquiv.funCongrLeft ℂ ℂ (m1b_symplecticSplitReindex k e)).symm.toLinearMap
      (LinearEquiv.funCongrLeft ℂ ℂ (m1b_symplecticSplitReindex k e)).symm.toLinearMap =
        (m1b_J (k + 1)).toBilin' := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (x (Sum.inl 0) * y (Sum.inr 0) - x (Sum.inr 0) * y (Sum.inl 0)) +
    (m1b_J k).toBilin'
      (fun i => x ((m1b_symplecticSplitIndex k).symm (Sum.inr (e (e.symm i)))))
      (fun i => y ((m1b_symplecticSplitIndex k).symm (Sum.inr (e (e.symm i))))) =
        (m1b_J (k + 1)).toBilin' x y
  simp only [Equiv.apply_symm_apply]
  rw [m1b_standard_symplectic_apply, m1b_standard_symplectic_apply, Fin.sum_univ_succ]
  rfl

end HodgeLean.Foundations.Program

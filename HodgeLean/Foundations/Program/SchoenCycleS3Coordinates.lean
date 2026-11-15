import HodgeLean.Foundations.Program.SchoenCycleS2b

/-! # Coefficients adapted to the residue summand -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Choose coefficient coordinates retaining every coordinate of the second summand. -/
theorem s2e_residue_adapted_coefficients
    (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (k r : ℕ) (hd : Module.finrank ℂ (M × (Fin r → ℂ)) = k + 1) :
    ∃ (b : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (M × (Fin r → ℂ)))
      (ι : Fin r ↪ Fin (k + 1)), ∀ v j, (b v).2 j = v (ι j) := by
  classical
  let g := Module.finrank ℂ M
  have hg : g + r = k + 1 := by
    simpa only [Module.finrank_prod, Module.finrank_fin_fun] using hd
  let e : Fin g ⊕ Fin r ≃ Fin (k + 1) :=
    finSumFinEquiv.trans (finCongr hg)
  let b := (LinearEquiv.funCongrLeft ℂ ℂ e).trans
    ((LinearEquiv.sumArrowLequivProdArrow (Fin g) (Fin r) ℂ ℂ).trans
      ((Module.finBasis ℂ M).equivFun.symm.prodCongr (LinearEquiv.refl ℂ (Fin r → ℂ))))
  let ι : Fin r ↪ Fin (k + 1) :=
    ⟨fun j => e (Sum.inr j), e.injective.comp Sum.inr_injective⟩
  exact ⟨b, ι, fun _ _ => rfl⟩

/-- Reindexing the selected ideals uses exactly the image of the selected coordinates. -/
theorem s2e_residue_intersection_reindex
    (k r : ℕ) (ι : Fin r ↪ Fin (k + 1)) (T : Finset (Fin r)) :
    T.sup (fun j => s2e_s2b_residueIdeal k (ι j)) =
      s2e_s2b_intersectionIdeal k (T.map ι) := by
  classical
  rw [Finset.sup_eq_iSup, s2e_s2b_intersectionIdeal]
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun hi => ?_
    exact le_iSup_of_le (ι i)
      (le_iSup_of_le (Finset.mem_map.mpr ⟨i, hi, rfl⟩) le_rfl)
  · refine iSup_le fun j => iSup_le fun hj => ?_
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenCycleEtaleAnalyticCoordinateChart

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Any prescribed complex line identification has an exact nonzero scalar normalization relative to the native coordinate evaluation.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Gunning and Rossi, Analytic Functions of Several Complex Variables, Chapter I. -/
theorem s2e_line_equiv_native_normalization
    (L : ℂ ≃L[ℂ] (Fin 1 → ℂ)) :
    (L 1) 0 ≠ 0 ∧ ∀ v : Fin 1 → ℂ, L.symm v = ((L 1) 0)⁻¹ * v 0 := by
  have hc : (L 1) 0 ≠ 0 := by
    intro h
    have hL : L 1 ≠ 0 := fun he => one_ne_zero (L.injective (he.trans (map_zero L).symm))
    apply hL
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
    exact h
  refine ⟨hc, ?_⟩
  intro v
  have hv : v = L.symm v • L 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, L.apply_symm_apply]
  have he : (L 1) 0 * L.symm v = v 0 := by
    have h := congrFun hv 0
    change v 0 = L.symm v * (L 1) 0 at h
    exact (mul_comm _ _).trans h.symm
  calc
    L.symm v = ((L 1) 0)⁻¹ * ((L 1) 0 * L.symm v) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ = _ := congrArg (fun z : ℂ => ((L 1) 0)⁻¹ * z) he

#print axioms s2e_line_equiv_native_normalization
end HodgeLean.Foundations.Program

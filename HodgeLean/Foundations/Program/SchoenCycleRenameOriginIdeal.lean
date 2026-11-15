import HodgeLean.Foundations.Program.SchoenCycleRenamedAdicPowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- A bijective variable renaming carries the actual root-origin ideal onto the target root-origin ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_rename_origin_ideal
    {R σ τ : Type*} [CommRing R] (e : σ ≃ τ) :
    (idealOfVars σ R).map (rename e).toRingHom = idealOfVars τ R := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change rename e p ∈ idealOfVars τ R
    simpa only [pow_one] using s2e_rename_preserves_origin_powers e 1 p (by simpa only [pow_one] using hp)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    have hj : (X j : MvPolynomial σ R) ∈ idealOfVars σ R := Ideal.subset_span ⟨j, rfl⟩
    have h := Ideal.mem_map_of_mem (rename e).toRingHom hj
    change rename e (X j : MvPolynomial σ R) ∈ _ at h
    rwa [rename_X] at h

end HodgeLean.Foundations.Program

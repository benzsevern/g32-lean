import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # Origin-adic filtration under coordinate renaming -/
noncomputable section
set_option maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Every coordinate renaming preserves each power of the origin ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_rename_preserves_origin_powers
    {ι τ R : Type*} [CommRing R] (σ : ι → τ) :
    ∀ N : ℕ, ∀ p ∈ idealOfVars ι R ^ N, rename σ p ∈ idealOfVars τ R ^ N := by
  have hbase : (idealOfVars ι R).map (rename σ).toRingHom ≤ idealOfVars τ R := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change rename σ (X i : MvPolynomial ι R) ∈ idealOfVars τ R
    rw [rename_X]
    exact Ideal.subset_span ⟨σ i, rfl⟩
  intro N p hp
  have hpow : (idealOfVars ι R ^ N).map (rename σ).toRingHom ≤ idealOfVars τ R ^ N := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hbase N
  exact hpow (Ideal.mem_map_of_mem (rename σ).toRingHom hp)

#print axioms s2e_rename_preserves_origin_powers
end HodgeLean.Foundations.Program

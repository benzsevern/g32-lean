import HodgeLean.Foundations.Program.SchoenCycleSumCoordinateValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The one-block elementary comparison retains every original invariant coefficient from the tail blocks.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_sum_elementary_invariant_C
    {R σ τ G : Type*} [CommRing R] [Group G] [Fintype σ]
    (t : G →* Equiv.Perm τ)
    (q : (⨅ g, AlgHom.equalizer (rename (t g)) (AlgHom.id R (MvPolynomial τ R)) :
      Subalgebra R (MvPolynomial τ R))) :
    (s2e_sum_elementary_invariant_equiv (σ := σ) t (C q)).val = rename Sum.inr q.val := by
  rw [s2e_sum_elementary_invariant_value, s2e_symmetric_coefficient_invariant_value,
    aeval_C, algebraMap_eq, map_C]
  apply (sumAlgEquiv R σ τ).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (DFunLike.congr_fun (sumAlgEquiv_comp_rename_inr (R := R) (S₁ := σ) (S₂ := τ)) q.val).symm

/-- Each first-block coordinate maps to its actual positive elementary root coefficient.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_sum_elementary_invariant_X
    {R σ τ G : Type*} [CommRing R] [Group G] [Fintype σ]
    (t : G →* Equiv.Perm τ) (i : Fin (Fintype.card σ)) :
    (s2e_sum_elementary_invariant_equiv (R := R) (σ := σ) t (X i)).val =
      rename Sum.inl (esymm σ R (i.val + 1)) := by
  rw [s2e_sum_elementary_invariant_value, s2e_symmetric_coefficient_invariant_value,
    aeval_X, map_esymm]
  apply (sumAlgEquiv R σ τ).injective
  rw [AlgEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun (sumAlgEquiv_comp_rename_inl (R := R) (S₁ := σ) (S₂ := τ))
    (esymm σ R (i.val + 1))
  change sumAlgEquiv R σ τ (rename Sum.inl (esymm σ R (i.val + 1))) =
    map (algebraMap R (MvPolynomial τ R)) (esymm σ R (i.val + 1)) at h
  rw [map_esymm] at h
  exact h.symm

end HodgeLean.Foundations.Program

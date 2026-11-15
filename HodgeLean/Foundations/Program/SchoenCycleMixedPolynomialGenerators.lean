import HodgeLean.Foundations.Program.SchoenCycleMixedPolynomialStepValues
import HodgeLean.Foundations.Program.SchoenCycleSumElementaryValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Each indexed mixed coordinate maps to its actual block elementary root coefficient.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
theorem s2e_mixed_polynomial_invariant_X
    (R : Type*) [CommRing R] (b : ℕ) (m : Fin b → ℕ)
    (a : Fin b) (j : Fin (m a)) :
    (s2e_mixed_polynomial_invariant_coordinates R b m (X ⟨a, j⟩)).val =
      rename (Sigma.mk a) (esymm (Fin (m a)) R (j.val + 1)) := by
  induction b with
  | zero => exact Fin.elim0 a
  | succ b ih =>
    rw [s2e_mixed_polynomial_successor_value]
    cases a using Fin.cases with
    | zero =>
      simp only [rename_X]
      change rename (s2e_sigma_head_tail (fun a => Fin (m a))).symm
        (s2e_sum_elementary_invariant_equiv (R := R) (σ := Fin (m 0))
          (Equiv.Perm.sigmaCongrRightHom (fun a : Fin b => Fin (m a.succ)))
          (rename (finCongr (Fintype.card_fin (m 0)).symm)
            (map (s2e_mixed_polynomial_invariant_coordinates R b (fun a => m a.succ)).toRingHom
              (sumAlgEquiv R (Fin (m 0)) _ (X (Sum.inl j)))))).val = _
      rw [sumAlgEquiv_X_inl, map_X, rename_X, s2e_sum_elementary_invariant_X, rename_rename]
      rfl
    | succ a =>
      simp only [rename_X]
      change rename (s2e_sigma_head_tail (fun a => Fin (m a))).symm
        (s2e_sum_elementary_invariant_equiv (R := R) (σ := Fin (m 0))
          (Equiv.Perm.sigmaCongrRightHom (fun a : Fin b => Fin (m a.succ)))
          (rename (finCongr (Fintype.card_fin (m 0)).symm)
            (map (s2e_mixed_polynomial_invariant_coordinates R b (fun a => m a.succ)).toRingHom
              (sumAlgEquiv R (Fin (m 0)) _ (X (Sum.inr ⟨a, j⟩)))))).val = _
      rw [sumAlgEquiv_X_inr, map_C]
      change rename (s2e_sigma_head_tail (fun a => Fin (m a))).symm
        (s2e_sum_elementary_invariant_equiv (R := R) (σ := Fin (m 0))
          (Equiv.Perm.sigmaCongrRightHom (fun a : Fin b => Fin (m a.succ)))
          (rename (finCongr (Fintype.card_fin (m 0)).symm)
            (C (s2e_mixed_polynomial_invariant_coordinates R b (fun a => m a.succ) (X ⟨a, j⟩))))).val = _
      rw [rename_C, s2e_sum_elementary_invariant_C]
      change rename (s2e_sigma_head_tail (fun a => Fin (m a))).symm
        (rename Sum.inr (s2e_mixed_polynomial_invariant_coordinates R b (fun a => m a.succ)
          (X ⟨a, j⟩)).val) = _
      rw [ih, rename_rename, rename_rename]
      rfl

end HodgeLean.Foundations.Program

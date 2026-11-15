import HodgeLean.Foundations.Program.SchoenTowerL1bTwoEvaluations

/-! # Two evaluation coordinates with the higher coefficients retained

The remaining polynomial variables are fixed by the coordinate change.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
namespace HodgeLean.Foundations.Program
universe u

/-- The affine evaluation change extends to all coefficient variables, fixing every higher variable. -/
theorem s2v_l1b_two_evaluation_all_coordinates
    {R κ : Type*} [CommRing R] (a b : R)
    (p q : MvPolynomial κ R) (hab : IsUnit (b - a)) :
    ∃ e : MvPolynomial (Fin 2 ⊕ κ) R ≃ₐ[R] MvPolynomial (Fin 2 ⊕ κ) R,
      e (X (Sum.inl 0)) = X (Sum.inl 0) + C a * X (Sum.inl 1) + rename Sum.inr p ∧
      e (X (Sum.inl 1)) = X (Sum.inl 0) + C b * X (Sum.inl 1) + rename Sum.inr q ∧
      ∀ k, e (X (Sum.inr k)) = X (Sum.inr k) := by
  let E := sumAlgEquiv R (Fin 2) κ
  obtain ⟨f, hf₀, hf₁⟩ := s2v_l1b_two_evaluation_coordinates
    (C a : MvPolynomial κ R) (C b) p q (by
      rw [← map_sub]
      exact hab.map C)
  let e := E.trans ((f.restrictScalars R).trans E.symm)
  have hrest (v : MvPolynomial κ R) : E (rename Sum.inr v) = C v := by
    have H := congrArg (fun F : MvPolynomial κ R →ₐ[R]
        MvPolynomial (Fin 2) (MvPolynomial κ R) => F v)
      (sumAlgEquiv_comp_rename_inr R (Fin 2) κ)
    exact H
  refine ⟨e, ?_, ?_, ?_⟩
  · apply E.injective
    change E (E.symm (f (E (X (Sum.inl 0))))) = _
    rw [E.apply_symm_apply, sumAlgEquiv_X_inl, hf₀]
    simp only [map_add, map_mul, hrest, E, sumAlgEquiv_X_inl, sumAlgEquiv_C_inl]
  · apply E.injective
    change E (E.symm (f (E (X (Sum.inl 1))))) = _
    rw [E.apply_symm_apply, sumAlgEquiv_X_inl, hf₁]
    simp only [map_add, map_mul, hrest, E, sumAlgEquiv_X_inl, sumAlgEquiv_C_inl]
  · intro k
    apply E.injective
    change E (E.symm (f (E (X (Sum.inr k))))) = _
    rw [E.apply_symm_apply, sumAlgEquiv_X_inr]
    exact f.commutes (X k)

/-- Replacing the two low coordinates by distinct evaluations preserves the full etale section map. -/
theorem s2v_l1b_two_evaluation_all_etale
    {R A κ : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (z : Fin 2 ⊕ κ → A) (a b : R)
    (p q : MvPolynomial κ R) (hab : IsUnit (b - a))
    (hEt : (eval₂Hom f z).Etale) :
    (eval₂Hom f (Sum.elim
      ![z (Sum.inl 0) + f a * z (Sum.inl 1) + eval₂Hom f (fun k => z (Sum.inr k)) p,
        z (Sum.inl 0) + f b * z (Sum.inl 1) + eval₂Hom f (fun k => z (Sum.inr k)) q]
      (fun k => z (Sum.inr k)))).Etale := by
  obtain ⟨e, he₀, he₁, heRest⟩ := s2v_l1b_two_evaluation_all_coordinates a b p q hab
  let F := eval₂Hom f z
  have hrename (v : MvPolynomial κ R) :
      F (rename Sum.inr v) = eval₂Hom f (fun k => z (Sum.inr k)) v := by
    exact eval₂_rename f Sum.inr z v
  have hcomp : F.comp e.toRingEquiv.toRingHom = eval₂Hom f (Sum.elim
      ![z (Sum.inl 0) + f a * z (Sum.inl 1) + eval₂Hom f (fun k => z (Sum.inr k)) p,
        z (Sum.inl 0) + f b * z (Sum.inl 1) + eval₂Hom f (fun k => z (Sum.inr k)) q]
      (fun k => z (Sum.inr k))) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [eval₂Hom_C, RingHom.comp_apply]
      change F (e (C c)) = f c
      rw [show e (C c) = C c from e.commutes c]
      exact eval₂Hom_C f z c
    · intro k
      rw [RingHom.comp_apply, eval₂Hom_X']
      change F (e (X k)) = _
      rcases k with k | k
      · fin_cases k
        · change F (e (X (Sum.inl 0))) = _
          rw [he₀]
          simp only [map_add, map_mul, hrename, F, eval₂Hom_C, eval₂Hom_X']
          rfl
        · change F (e (X (Sum.inl 1))) = _
          rw [he₁]
          simp only [map_add, map_mul, hrename, F, eval₂Hom_C, eval₂Hom_X']
          rfl
      · rw [heRest]
        exact eval₂Hom_X' f z (Sum.inr k)
  rw [← hcomp]
  exact RingHom.Etale.stableUnderComposition e.toRingEquiv.toRingHom F
    (RingHom.Etale.of_bijective e.bijective) hEt

end HodgeLean.Foundations.Program

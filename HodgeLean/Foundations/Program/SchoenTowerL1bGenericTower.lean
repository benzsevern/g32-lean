import HodgeLean.Foundations.Program.SchoenTowerInertiaSuppliers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Compatible parametrizations commute with the actual tower composite. -/
theorem s2v_l1b_generic_tower_composite {r : ℕ} (T : Scheme)
    (W : Fin (r + 1) → Over (Spec ↧ℂ))
    (w : ∀ i : Fin r, W i.succ ⟶ W i.castSucc)
    (q : ∀ i, T ⟶ (W i).left)
    (hq : ∀ i : Fin r, q i.succ ≫ (w i).left = q i.castSucc)
    (i : Fin (r + 1)) :
    q i ≫ (s2v_towerToInitial W w i).left = q 0 := by
  induction i using Fin.induction with
  | zero => exact Category.comp_id _
  | succ i ih =>
    change q i.succ ≫ ((w i).left ≫ (s2v_towerToInitial W w i.castSucc).left) = q 0
    rw [← Category.assoc, hq i, ih]

/-- The chosen original parametrization is retained at every tower stage. -/
theorem s2v_l1b_generic_to_original {r : ℕ} (T : Scheme)
    (W : Fin (r + 1) → Over (Spec ↧ℂ))
    (w : ∀ i : Fin r, W i.succ ⟶ W i.castSucc)
    (q : ∀ i, T ⟶ (W i).left)
    (hq : ∀ i : Fin r, q i.succ ≫ (w i).left = q i.castSucc)
    (W₀ : Over (Spec ↧ℂ)) (eW : W 0 ≅ W₀) (q₀ : T ⟶ W₀.left)
    (hinit : q 0 ≫ eW.hom.left = q₀) (i : Fin (r + 1)) :
    q i ≫ (s2v_towerToInitial W w i ≫ eW.hom).left = q₀ := by
  change q i ≫ ((s2v_towerToInitial W w i).left ≫ eW.hom.left) = q₀
  rw [← Category.assoc, s2v_l1b_generic_tower_composite T W w q hq i, hinit]

/-- An original generic deck square gives the tower square after projection to the original cover. -/
theorem s2v_l1b_generic_deck_projected {r : ℕ} (T : Scheme)
    (W : Fin (r + 1) → Over (Spec ↧ℂ))
    (w : ∀ i : Fin r, W i.succ ⟶ W i.castSucc)
    (q : ∀ i, T ⟶ (W i).left)
    (hq : ∀ i : Fin r, q i.succ ≫ (w i).left = q i.castSucc)
    (d : ∀ i, W i ⟶ W i)
    (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (W₀ : Over (Spec ↧ℂ)) (eW : W 0 ≅ W₀) (d₀ : W₀ ⟶ W₀)
    (hdinit : d 0 ≫ eW.hom = eW.hom ≫ d₀)
    (q₀ : T ⟶ W₀.left) (hinit : q 0 ≫ eW.hom.left = q₀)
    (φ : T ⟶ T) (hφ : φ ≫ q₀ = q₀ ≫ d₀.left) (i : Fin (r + 1)) :
    (φ ≫ q i) ≫ (s2v_towerToInitial W w i ≫ eW.hom).left =
      (q i ≫ (d i).left) ≫ (s2v_towerToInitial W w i ≫ eW.hom).left := by
  have hg := s2v_l1b_generic_to_original T W w q hq W₀ eW q₀ hinit i
  have hd := congrArg (fun f => f.left)
    (s2v_towerToOriginal_deck W w d hdw W₀ eW d₀ hdinit i)
  change (d i).left ≫ (s2v_towerToInitial W w i ≫ eW.hom).left =
    (s2v_towerToInitial W w i ≫ eW.hom).left ≫ d₀.left at hd
  rw [Category.assoc, hg, hφ, Category.assoc, hd, ← Category.assoc, hg]

end HodgeLean.Foundations.Program

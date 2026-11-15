import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers

/-! # Total maps on the retained normalization tower

Rows T11 and T12 of `SchoenTransferJ2NativeInput.lean:213–221`.
The final object is the last normalization itself. The initial identification
and transitions are inputs from T07 and T08, on these very generic maps.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Retain the last normalization and compose the specified transitions, with
both native total-map equations. -/
theorem selectedTotalMaps
    (W₀ : Over (Spec ↧ℂ)) [IsIntegral W₀.left]
    (r : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc)) :
    ∃ (W : Over (Spec ↧ℂ)),
    ∃ (eWr : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W),
    ∃ f : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ W₀,
      f 0 = eW.hom ∧ (∀ i : Fin r, f i.succ = w i ≫ f i.castSucc) := by
  let N := fun i => s2b_normalizationOver (B i) (η i)
  exact ⟨N (Fin.last r), Iso.refl _, s2e_towerTotalMap N eW.hom w,
    s2e_towerTotalMap_zero N eW.hom w,
    s2e_towerTotalMap_succ N eW.hom w⟩

/-- The same total maps retain the generic point equation at every stage. -/
theorem selectedTotalMaps_generic
    (W₀ : Over (Spec ↧ℂ)) [IsIntegral W₀.left]
    (r : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (hgeneric : (η 0).toNormalization ≫ eW.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left))
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (f : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ W₀)
    (hf₀ : f 0 = eW.hom)
    (hf : ∀ i : Fin r, f i.succ = w i ≫ f i.castSucc)
    (i : Fin (r + 1)) :
    (η i).toNormalization ≫ (f i).left =
      W₀.left.fromSpecStalk (genericPoint W₀.left) := by
  induction i using Fin.induction with
  | zero => rw [hf₀]; exact hgeneric
  | succ i ih =>
    rw [hf, Over.comp_left, ← Category.assoc, hw i]
    exact ih

end HodgeLean.Foundations.Program.G32Native

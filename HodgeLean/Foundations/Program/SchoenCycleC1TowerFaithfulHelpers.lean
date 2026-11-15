import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationMapHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1FaithfulTransportHelpers

/-! # Faithfulness through the retained normalization tower -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Retained generic compatibility and generator equivariance carry faithful
powers from stage zero to every actual normalization in the tower. -/
theorem s2e_c1_normalization_tower_faithful_powers
    {T : Scheme} [IsReduced T] (r m : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsSeparated (B i).hom]
    (η : ∀ i, T ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (d : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ s2b_normalizationOver (B i) (η i))
    (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (hzero : ∀ n, n < m → End.of (d 0) ^ n = 1 → n = 0) :
    ∀ i n, n < m → End.of (d i) ^ n = 1 → n = 0 := by
  haveI (i : Fin (r + 1)) : IsReduced (s2b_normalizationOver (B i) (η i)).left :=
    inferInstanceAs (IsReduced (η i).normalization)
  haveI (i : Fin (r + 1)) : IsSeparated (s2b_normalizationOver (B i) (η i)).hom := by
    change IsSeparated ((η i).fromNormalization ≫ (B i).hom)
    infer_instance
  intro i
  induction i using Fin.induction with
  | zero => exact hzero
  | succ j ih =>
    haveI : IsDominant (w j).left :=
      s2e_c1_normalization_transition_dominant (B j.succ) (B j.castSucc)
        (η j.succ) (η j.castSucc) (w j) (hw j)
    exact s2e_c1_faithful_powers_of_dominant_equivariant (w j)
      (d j.succ) (d j.castSucc) (hdw j) m ih

/-- The specified initial and final identifications retain faithful powers
of the actual tower generator. -/
theorem s2e_c1_transported_normalization_tower_faithful_powers
    {T : Scheme} [IsReduced T] (r m : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsSeparated (B i).hom]
    (η : ∀ i, T ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (d : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ s2b_normalizationOver (B i) (η i))
    (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (W₀ : Over (Spec ↧ℂ)) [IsReduced W₀.left] [IsSeparated W₀.hom]
    (d₀ : W₀ ⟶ W₀) (e₀ : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (hd₀ : d 0 ≫ e₀.hom = e₀.hom ≫ d₀)
    (hzero : ∀ n, n < m → End.of d₀ ^ n = 1 → n = 0)
    (W : Over (Spec ↧ℂ))
    (eFinal : W ≅ s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r))) :
    ∀ n, n < m → End.of (eFinal.hom ≫ d (Fin.last r) ≫ eFinal.inv) ^ n = 1 → n = 0 := by
  have hz := s2e_c1_faithful_powers_of_dominant_equivariant e₀.hom (d 0) d₀ hd₀ m hzero
  have hlevels := s2e_c1_normalization_tower_faithful_powers r m B η w hw d hdw hz
  haveI : IsReduced (s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r))).left :=
    inferInstanceAs (IsReduced (η (Fin.last r)).normalization)
  haveI : IsSeparated (s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r))).hom := by
    change IsSeparated ((η (Fin.last r)).fromNormalization ≫ (B (Fin.last r)).hom)
    infer_instance
  exact s2e_c1_faithful_powers_of_dominant_equivariant eFinal.hom
    (eFinal.hom ≫ d (Fin.last r) ≫ eFinal.inv) (d (Fin.last r))
    (by simp only [Category.assoc, eFinal.inv_hom_id, Category.comp_id]) m (hlevels (Fin.last r))

end HodgeLean.Foundations.Program

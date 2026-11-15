import HodgeLean.Foundations.QuotientDuality.RetainedCycleDefs
import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms
import HodgeLean.Foundations.AlgebraicGeometry.Normalization.BirationalHelpers

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_tower_source_square {C : Type*} [Category C] {r : ℕ}
    (N : Fin (r + 1) → C) {T Y : C} (f₀ : N 0 ⟶ Y)
    (w : ∀ i : Fin r, N i.succ ⟶ N i.castSucc)
    (s : ∀ i, T ⟶ N i)
    (hs : ∀ i : Fin r, s i.succ ≫ w i = s i.castSucc)
    (i : Fin (r + 1)) :
    s i ≫ s2e_towerTotalMap N f₀ w i = s 0 ≫ f₀ := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [s2e_towerTotalMap_succ, ← Category.assoc, hs i]
    exact ih

theorem retained_birational_of_generic_source {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (s : Spec Y.functionField ⟶ X) [IsDominant s]
    (hs : s ≫ f = Y.fromSpecStalk (genericPoint Y)) : zmtiso_IsBirational f := by
  apply Normalization.birational_of_dominant_factor s f
  rw [hs]
  exact s2_genericPointMorphism_birational Y

theorem retained_endpoint_source_square {r : ℕ}
    (N : Fin (r + 1) → Over (Spec ↧ℂ)) {W W₀ : Over (Spec ↧ℂ)}
    (e₀ : N 0 ≅ W₀) (e : N (Fin.last r) ≅ W)
    (w : ∀ i : Fin r, N i.succ ⟶ N i.castSucc)
    {T : Scheme} (s : ∀ i, T ⟶ (N i).left)
    (hs : ∀ i : Fin r, s i.succ ≫ (w i).left = s i.castSucc) :
    (s (Fin.last r) ≫ e.hom.left) ≫
        (retainedCycleModification N e₀ e w).left = s 0 ≫ e₀.hom.left := by
  have htotal (i : Fin (r + 1)) :
      s i ≫ (s2e_towerTotalMap N e₀.hom w i).left = s 0 ≫ e₀.hom.left := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      rw [s2e_towerTotalMap_succ, Over.comp_left, ← Category.assoc, hs i]
      exact ih
  have he : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  change (s (Fin.last r) ≫ e.hom.left) ≫
    (e.inv.left ≫ (s2e_towerTotalMap N e₀.hom w (Fin.last r)).left) = _
  rw [Category.assoc, ← Category.assoc e.hom.left e.inv.left, he, Category.id_comp]
  exact htotal (Fin.last r)

theorem retained_normalization_modification_birational {r : ℕ}
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (W W₀ : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsIntegral W₀.left]
    (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (e₀ : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (e : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W)
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hgeneric : (η 0).toNormalization ≫ e₀.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization) :
    zmtiso_IsBirational (retainedCycleModification
      (fun i => s2b_normalizationOver (B i) (η i)) e₀ e w).left := by
  letI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  letI : IsDominant (η (Fin.last r)).toNormalization := by infer_instance
  letI : IsDominant e.hom.left := by infer_instance
  let s := (η (Fin.last r)).toNormalization ≫ e.hom.left
  letI : IsDominant s := by
    change IsDominant ((η (Fin.last r)).toNormalization ≫ e.hom.left)
    infer_instance
  apply retained_birational_of_generic_source _ s
  exact (retained_endpoint_source_square
    (fun i => s2b_normalizationOver (B i) (η i)) e₀ e w
    (fun i => (η i).toNormalization) hw).trans hgeneric

end HodgeLean.Foundations.QuotientDuality
